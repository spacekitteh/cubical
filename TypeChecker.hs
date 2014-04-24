{-# LANGUAGE RecordWildCards #-}
module TypeChecker ( runDecls
                   , runDeclss
                   , runInfer
                   , TEnv(..)
                   , verboseEnv
                   , silentEnv
                   ) where

import Data.Either
import Data.List
import Data.Maybe
import Data.Monoid hiding (Sum)
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Trans.Reader
import Control.Monad.Error (throwError)
import Control.Applicative
import Pretty

import CTT
import Eval

trace :: String -> Typing ()
trace s = do
  b <- asks verbose
  if b then liftIO (putStrLn s) else return ()

traceb :: String -> Typing ()
traceb s = do
  b <- asks debug
  if b then liftIO (putStrLn s) else return ()

-- Type checking monad
type Typing a = ReaderT TEnv (ErrorT String IO) a

runTyping :: Typing a -> TEnv -> IO (Either String a)
runTyping t env = runErrorT $ runReaderT t env

liftEval :: Eval v -> Typing v
liftEval ev = do eenv <- EEnv <$> asks debug <*> asks mor <*> asks env <*> asks opaques
                 return $ runEval eenv ev

-- Used in the interaction loop
runDecls :: TEnv -> ODecls -> IO (Either String TEnv)
runDecls tenv d = flip runTyping tenv $ do
  checkDecls d
  addDecls d

runDeclss :: TEnv -> [ODecls] -> IO (Maybe String,TEnv)
runDeclss tenv []     = return $ (Nothing, tenv)
runDeclss tenv (d:ds) = do
  x   <- runDecls tenv d
  case x of
    Right tenv' -> runDeclss tenv' ds
    Left s      -> return $ (Just s , tenv)

runInfer :: TEnv -> Ter -> IO (Either String Val)
runInfer lenv e = runTyping (checkInfer e) lenv

-- Environment for type checker
data TEnv = TEnv { index   :: Int   -- for de Bruijn levels (for fresh variables)
                 , mor     :: Morphism
                 , env     :: Env
                 , opaques :: [Binder]
                 , ctxt    :: Ctxt
                 , verbose :: Bool  -- Should it be verbose and print
                                    -- what it typechecks?
                 , debug   :: Bool  -- Should the evaluator be run in
                                    -- debug mode?
                 }

verboseEnv :: Bool -> TEnv
verboseEnv debug = TEnv 0 idMor Empty [] EmptyCtxt True debug

silentEnv :: TEnv
silentEnv = TEnv 0 idMor Empty [] EmptyCtxt False False

-- local modifiers
inEnv :: Env -> TEnv -> TEnv
inEnv rho e = e {env = rho}

addPairs :: [(Binder,Val)] -> TEnv -> TEnv
addPairs xus e@(TEnv{..}) = e {env = foldl Pair env xus}

addMor :: Morphism -> TEnv -> TEnv
addMor f e@(TEnv{..}) = e {mor = compMor mor f}

isOpaque :: Binder -> Typing Bool
isOpaque x = elem x <$> asks opaques

addC :: (Tele,Env) -> [(Binder,Val)] -> Ctxt -> Typing Ctxt
addC _             []          gam = return gam
addC ((y,a):as,nu) ((x,u):xus) gam = do
  v <- local (inEnv nu) $ liftEval $ eval a
  addC (as, Pair nu (y,u)) xus  (BinderCtxt x v gam)

-- Extract the type of a label as a closure
getLblType :: String -> Val -> Typing (Tele, Env)
getLblType c (Ter (Sum _ cas) _f r) = case getIdent c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType " ++ show c)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

addTypeAndVal :: Binder -> Val -> Val -> TEnv -> TEnv
addTypeAndVal x typ val tenv@(TEnv {..}) =
 tenv { index = index + 1
      , env = Pair env (x, val)
      , ctxt = BinderCtxt x typ ctxt}

addTypeVal :: (Binder,Val) -> TEnv -> TEnv
addTypeVal p@(x,tx) tenv =
   addTypeAndVal x tx (mkVar (index tenv) (mor tenv)) tenv

addType :: (Binder,Ter) -> Typing TEnv
addType (x,a) = do
  v <- liftEval $ eval a
  addTypeVal (x,v) <$> ask

addColor :: Color -> TEnv -> TEnv
addColor i tenv@(TEnv {..}) = tenv {ctxt = ColorCtxt i ctxt}

modEnv :: (Env -> Typing Env) -> TEnv -> Typing TEnv
modEnv f tenv = do fenv <- f (env tenv); return tenv {env = fenv}

addBranch :: [(Binder,Val)] -> (Tele,Env) -> Typing TEnv
addBranch nvs (tele,env) = do
  TEnv k f rho o gam v d <- ask
  gam' <- addC (tele,env) nvs gam
  return $ TEnv (k + length nvs) f (upds rho nvs) o gam' v d

addDecls :: ODecls -> Typing TEnv
addDecls od@(ODecls d) = do
  rho  <- PDef (declDefs d) <$> asks env
  es'  <- local (inEnv rho) $ liftEval $ evals (declDefs d)
  gam  <- addC (declTele d,rho) es' =<< asks ctxt
  tenv <- ask
  return $ tenv {env = rho, ctxt = gam}
addDecls (Transparent d) = do
    tenv <- ask
    return $ tenv {opaques = delete d (opaques tenv)}
addDecls (Opaque d)      = do
    tenv <- ask
    return $ tenv {opaques = d:(opaques tenv)}

addTele :: Tele -> Typing TEnv
addTele xas = do tenv <- ask
                 foldM (\e xa -> local (const e) $ addType xa) tenv xas

-- Useful monadic versions of functions:
checkM :: Typing Val -> Ter -> Typing ()
checkM v t = do
  v' <- v
  check v' t

localM :: Typing TEnv -> Typing a -> Typing a
localM tenv x = do tenv' <- tenv; local (const tenv') x

-- Getters:
getFresh :: Typing Val
getFresh = mkVar <$> asks index <*> asks mor

checkDecls :: ODecls -> Typing ()
checkDecls (ODecls d) =
  let (idents, tele, ters) = (declIdents d, declTele d, declTers d)
  in do
    trace ("Checking definition: " ++ unwords idents)
    checkTele tele
    rho <- asks env
    tenv' <- addTele tele
    local (const tenv') $ checks (tele,rho) ters
checkDecls _ = return ()

checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  check VU a
  localM (addType (x,a)) $ checkTele xas

subTEnv :: Color -> TEnv -> TEnv
subTEnv i tenv = tenv {ctxt = subCtxt i (ctxt tenv)}

checkFace :: Side -> Val -> Ter -> Typing Val
checkFace s@(i,d) v t = do
  ctx <- subCtxt i <$> asks ctxt
  local (\e -> e {ctxt = ctx}) $ checkAndEval v t

checkAndEval :: Val -> Ter -> Typing Val
checkAndEval a t = do
  check a t
  liftEval $ eval t

check :: Val -> Ter -> Typing ()
check a t = case (a,t) of
  (_,Undefined) -> return ()
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (VU,Pi a (Lam x b)) -> do
    check VU a
    localM (addType (x,a)) $ check VU b
  (VU,Sigma a (Lam x b)) -> do
    check VU a
    localM (addType (x,a)) $ check VU b
  (VU,ColoredPair i a (Lam x b)) -> local (subTEnv i) $ do
    a0 <- checkAndEval VU a
    local (addTypeVal (x,a0)) $ check VU b
  (VU,Sum _ bs) -> sequence_ [checkTele as | (_,as) <- bs]
  (VPi (Ter (Sum _ cas) _f nu) f,Split _ ces) ->
    if sort (map fst ces) == sort [n | ((n,_),_) <- cas]
       then sequence_ [ checkBranch (as,nu) f brc
                      | (brc, (_,as)) <- zip ces cas ]
       else throwError "case branches does not match the data type"
  (VPi a f,Lam x t)  -> do
    var <- getFresh
    local (addTypeVal (x,a)) $ do
       fvar <- liftEval $ app f var
       check fvar t
  (VSigma a f, SPair t1 t2) -> do
    check a t1
    v <- liftEval $ eval t1
    checkM (liftEval $ app f v) t2
  (VCSPair x a f, ColoredPair y t1 t2) -> local (subTEnv x) $ do
    when (x /= y) $
      throwError $ "The dimension of the pair and sigma differ: "
                   ++ show x ++ " " ++ show y
    v <- checkAndEval a t1
    checkM (liftEval $ app f v) t2
  (VPi (VCSPair i a f) g, ColoredPair j (Lam x t1) (Lam y (Lam z t2))) ->
      local (subTEnv i) $ do
        when (i /= j) $
             throwError $ "The dimension of the cfpair and csigma differ: "
                            ++ show i ++ " " ++ show j
        u <- mkVar <$> asks index <*> asks mor
        gu   <- liftEval $ app g u
        ui0  <- liftEval $ face i u
        fui0  <- liftEval $ app f ui0
        case gu of
          VCSPair i' b h | i == i' -> do
            v1 <- local (addTypeAndVal x a ui0) $ checkAndEval b t1
            local (addTypeAndVal y a ui0) $
              local (addTypeAndVal z fui0 (VCSnd i u)) $
                  checkM (liftEval $ app h v1) t2
          _ -> throwError $ "check (funpair): " ++ show gu ++ " is not well formed"
  (_,Where e d) -> do
    checkDecls d
    localM (addDecls d) $ check a e
  _ -> do
    v <- checkInfer t
    k <- asks index
    gam <- asks ctxt
    rho <- asks env
    f   <- asks mor
    b   <- liftEval $ conv k f v a
    unless b $
      throwError $ "check conv: the actual type of " ++ show t ++ ": \n       "
                 ++ show a ++ " is not convertible to the expected type " ++ show v
                 ++ "\n\nin  "  ++ show gam ++ "\nand\n  " ++ show rho

checkBranch :: (Tele,Env) -> Val -> Brc -> Typing ()
checkBranch (xas,nu) f (c,(xs,e)) = do
  k     <- asks index
  env   <- asks env
  mor   <- asks mor
  let l  = length xas
  let us = map (`mkVar` mor) [k..k+l-1]
  localM (addBranch (zip xs us) (xas,nu))
    $ checkM (liftEval $ app f (VCon c us)) e

checkInfer :: Ter -> Typing Val
checkInfer e = case e of
  U -> return VU                 -- U : U
  Var n -> do
    gam <- asks ctxt
    case lookupCtxt n gam of
      Just v  -> return v
      Nothing -> throwError $ show n ++ " is not declared!"
  App t u -> do
    c <- checkInfer t
    case c of
      VPi a f -> do
        check a u
        v   <- liftEval $ eval u
        liftEval $ app f v
      _       -> throwError $ show t ++ " has not a pi-type, but " ++ show c
  Fst t -> do
    c <- checkInfer t
    case c of
      VSigma a f -> return a
      _          -> throwError $ show c ++ " is not a sigma-type"
  Snd t -> do
    c <- checkInfer t
    case c of
      VSigma a f -> do
        v <- liftEval $ eval t
        liftEval $ app f (fstSVal v)
      _          -> throwError $ show c ++ " is not a sigma-type"
  ColoredSnd i t -> do
    c <- local (addColor i) $ checkInfer t
    case c of
      VCSPair j _a f -> do
        when (i /= j) $
          throwError $ "The dimension of the pair and sigma differ: "
                       ++ show i ++ " " ++ show j
        v <- liftEval $ eval t
        vi0 <- liftEval $ face i v
        liftEval $ app f vi0
      _          -> throwError $ show c ++ " is not a colored sigma-type"
  Where t d -> do
    checkDecls d
    localM (addDecls d) $ checkInfer t
  _ -> throwError ("checkInfer " ++ show e)

checks :: (Tele,Env) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  v <- local (inEnv nu) $ liftEval $ eval a
  check v e
  v' <- liftEval $ eval e
  checks (xas, Pair nu (x,v')) es
checks _              _      = throwError "checks"

-- Not used since we have U : U
--
-- (=?=) :: Typing Ter -> Ter -> Typing ()
-- m =?= s2 = do
--   s1 <- m
--   unless (s1 == s2) $ throwError (show s1 ++ " =/= " ++ show s2)
--
-- checkTs :: [(String,Ter)] -> Typing ()
-- checkTs [] = return ()
-- checkTs ((x,a):xas) = do
--   checkType a
--   local (addType (x,a)) (checkTs xas)
--
-- checkType :: Ter -> Typing ()
-- checkType t = case t of
--   U              -> return ()
--   Pi a (Lam x b) -> do
--     checkType a
--     local (addType (x,a)) (checkType b)
--   _ -> checkInfer t =?= U
