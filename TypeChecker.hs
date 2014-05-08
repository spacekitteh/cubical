module TypeChecker where

import Data.Function
import Data.List
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Trans.Reader
import Control.Monad.Error (throwError)
import Control.Applicative

import CTT
import Eval

-- Type checking monad
type Typing a = ReaderT TEnv (ErrorT String IO) a

-- Environment for type checker
data TEnv = TEnv { index   :: Int   -- for de Bruijn levels
                 , dom     :: [Name]
                 , env     :: Env
                 , ctxt    :: Ctxt
                 , verbose :: Bool  -- Should it be verbose and print
                                    -- what it typechecks?
                 }
  deriving (Eq,Show)

verboseEnv, silentEnv :: TEnv
verboseEnv = TEnv 0 [] Empty [] True
silentEnv  = TEnv 0 [] Empty [] False

addTypeVal :: (Binder,Val) -> TEnv -> TEnv
addTypeVal p@(x,_) (TEnv k dom rho gam v) =
  TEnv (k+1) dom (Pair rho (x,mkVar k dom)) (p:gam) v

addType :: (Binder,Ter) -> TEnv -> Typing TEnv
addType (x,a) tenv@(TEnv _ dom rho _ _) =
  return $ addTypeVal (x,eval (idMor dom) rho a) tenv

addC :: Ctxt -> (Tele,Env) -> [(Binder,Val)] -> Typing Ctxt
addC gam _             []          = return gam
addC gam ((y,a):as,nu) ((x,u):xus) = do
  dom <- asks dom
  addC ((x,eval (idMor dom) nu a):gam) (as,Pair nu (y,u)) xus

addBranch :: [(Binder,Val)] -> (Tele,Env) -> TEnv -> Typing TEnv
addBranch nvs (tele,env) (TEnv k dom rho gam v) = do
  e <- addC gam (tele,env) nvs
  return $ TEnv (k + length nvs) dom (upds rho nvs) e v

addDecls :: Decls -> TEnv -> Typing TEnv
addDecls d (TEnv k dom rho gam v) = do
  let rho1 = PDef [ (x,y) | (x,_,y) <- d ] rho
      es' = evals (idMor dom) rho1 (declDefs d)
  gam' <- addC gam (declTele d,rho) es'
  return $ TEnv k dom rho1 gam' v

addTele :: Tele -> TEnv -> Typing TEnv
addTele xas lenv = foldM (flip addType) lenv xas

trace :: String -> Typing ()
trace s = do
  b <- verbose <$> ask
  when b $ liftIO (putStrLn s)

runTyping :: TEnv -> Typing a -> IO (Either String a)
runTyping env t = runErrorT $ runReaderT t env

-- Used in the interaction loop
runDecls :: TEnv -> Decls -> IO (Either String TEnv)
runDecls tenv d = runTyping tenv $ do
  checkDecls d
  addDecls d tenv

runDeclss :: TEnv -> [Decls] -> IO (Maybe String,TEnv)
runDeclss tenv []         = return (Nothing, tenv)
runDeclss tenv (d:ds) = do
  x <- runDecls tenv d
  case x of
    Right tenv' -> runDeclss tenv' ds
    Left s      -> return (Just s, tenv)

runInfer :: TEnv -> Ter -> IO (Either String Val)
runInfer lenv e = runTyping lenv (checkInfer e)

-- Extract the type of a label as a closure
getLblType :: String -> Val -> Typing (Tele, Env)
getLblType c (Ter (Sum _ cas) _f r) = case getIdent c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType " ++ show c)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Useful monadic versions of functions:
localM :: (TEnv -> Typing TEnv) -> Typing a -> Typing a
localM f r = do
  e <- ask
  a <- f e
  local (const a) r

getFresh :: Typing Val
getFresh = mkVar <$> asks index <*> asks dom

checkDecls :: Decls -> Typing ()
checkDecls d = do
  let (idents, tele, ters) = (declIdents d, declTele d, declTers d)
  trace ("Checking: " ++ unwords idents)
  checkTele tele
  rho <- asks env
  localM (addTele tele) $ checks (tele,rho) ters

checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  check VU a
  localM (addType (x,a)) $ checkTele xas

check :: Val -> Ter -> Typing ()
check a t = case (a,t) of
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (VU,Pi a (Lam x b)) -> do
    check VU a
    localM (addType (x,a)) $ check VU b
  (VU,Sigma a (Lam x b)) -> do
    check VU a
    localM (addType (x,a)) $ check VU b
  (VU,Sum _ bs) -> sequence_ [checkTele as | (_,as) <- bs]
  (VPi (Ter (Sum _ cas) _g nu) f,Split _ ces) -> do
    let cas' = sortBy (compare `on` fst . fst) cas
        ces' = sortBy (compare `on` fst) ces
    if map (fst . fst) cas' == map fst ces'
       then sequence_ [ checkBranch (as,nu) f brc
                      | (brc, (_,as)) <- zip ces' cas' ]
       else throwError "case branches does not match the data type"
  (VPi a f,Lam x t)  -> do
    var <- getFresh
    local (addTypeVal (x,a)) $ check (app f var) t
  (VSigma a f, SPair t1 t2) -> do
    check a t1
    dom <- asks dom
    e   <- asks env
    check (app f (eval (idMor dom) e t1)) t2
  (_,Where e d) -> do
    checkDecls d
    localM (addDecls d) $ check a e
  (VApp (VNSnd i VU) a, Lam x t) ->
    local (addTypeVal (x,a)) $ check VU t
  (VApp (VNSnd i (VPi a f)) c, Lam x (Lam y t)) -> do
    varX <- getFresh
    dom  <- asks dom
    let ai0  = appMor (faceMor (i:dom) i) a
    let adot = app (a `dot` i) varX
    local (addTypeVal (x, ai0)) $ do
      varY <- getFresh
      let fdot = app f (VNSPair i varX varY) `dot` i
      let v    = app fdot (app c varX)
      local (addTypeVal (y, adot)) $ check v t
  (a, NamedPair i t p) -> do
    TEnv k dom rho gam v <- ask
    when (i `notElem` dom) $
      throwError $ "check: NamedPair " ++ show i ++ "should be in " ++ show dom
    let i0    = faceMor dom i
        gami0 = [ (x, appMor i0 v) | (x,v) <- gam ]
        rhoi0 = appMorEnv i0 rho
        ai0   = appMor i0 a
        dom'  = delete i dom
        adot  = app (a `dot` i) (eval (idMor dom') rhoi0 t)
    local (const (TEnv k dom' rhoi0 gami0 v)) $ do
      check ai0 t
      check adot p
  _ -> do
    v <- checkInfer t
    k <- asks index
    d <- asks dom
    unless (conv k d v a) $
      throwError $ "check conv: " ++ show v ++ " /= " ++ show a

checkBranch :: (Tele,Env) -> Val -> Brc -> Typing ()
checkBranch (xas,nu) f (c,(xs,e)) = do
  k   <- asks index
  d   <- asks dom
  env <- asks env
  let l  = length xas
      us = map (`mkVar` d) [k..k+l-1]
  localM (addBranch (zip xs us) (xas,nu)) $ check (app f (VCon c us)) e

checkInferApp :: Ter -> Ter -> Typing Val
checkInferApp t u = do
  c <- checkInfer t
  case c of
    VPi a f -> do
      check a u
      dom <- asks dom
      rho <- asks env
      let v = eval (idMor dom) rho u
      return $ app f v
    VApp (VNSnd i VU) a -> do
      check a u
      return VU
    _       -> throwError $ show c ++ " is not a product"

checkInfer :: Ter -> Typing Val
checkInfer e = case e of
  U -> return VU                 -- U : U
  Var n -> do
    gam <- asks ctxt
    case getIdent n gam of
      Just v  -> return v
      Nothing -> throwError $ show n ++ " is not declared!"
  App t@(App t0 t1) t2 -> do
    v <- checkInfer t0
    case v of
      VApp (VNSnd i (VPi a f)) c -> do
        dom <- asks dom
        rho <- asks env
        check (appMor (faceMor (i:dom) i) a) t1
        let t1val = eval (idMor dom) rho t1
            t2val = eval (idMor dom) rho t2
        check (app (a `dot` i) t1val) t2
        let fdot = app f (VNSPair i t1val t2val) `dot` i
        return $ app fdot (app c t1val)
      _ -> checkInferApp t t2
  App t u -> checkInferApp t u
  Fst t -> do
    c <- checkInfer t
    case c of
      VSigma a f -> return a
      _          -> throwError $ show c ++ " is not a sigma-type"
  Snd t -> do
    c <- checkInfer t
    case c of
      VSigma a f -> do
        dom <- asks dom
        e   <- asks env
        let v = eval (idMor dom) e t
        return $ app f (fstSVal v)
      _          -> throwError $ show c ++ " is not a sigma-type"
  Where t d -> do
    checkDecls d
    localM (addDecls d) $ checkInfer t
  NamedSnd i t -> do
    v <- local (\e -> e{dom=i:dom e}) $ checkInfer t -- implicit deg's
    case v of
      VNSPair j a p | i == j -> do
        dom <- asks dom
        rho <- asks env
        let i0 = faceMor (i:dom) i
        return $ app p (eval i0 (appMorEnv i0 rho) t)
      VNSPair j a p ->
        throwError $ "checkInfer: names do not match " ++ show v ++
                     " and " ++ show i
      _ -> throwError $ "checkInfer: should be a VNSPair " ++ show v
  _ -> throwError ("checkInfer " ++ show e)

checks :: (Tele,Env) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  dom <- asks dom
  let v = eval (idMor dom) nu a
  check v e
  rho <- asks env
  let v' = eval (idMor dom) rho e
  checks (xas,Pair nu (x,v')) es
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
