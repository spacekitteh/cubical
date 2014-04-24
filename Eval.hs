{-# LANGUAGE TupleSections, RecordWildCards #-}
module Eval ( fstSVal
            , runEval
            , EEnv(EEnv)
            , Eval
            , face
            , eval
            , evals
            , app
            , appM
            , conv
            , convM
            ) where

import Control.Applicative
import Control.Arrow (second)
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Data.Functor.Identity
import Data.List
import Data.Maybe (fromMaybe)

import Debug.Trace

import CTT

traceb :: String -> Eval a -> Eval a
traceb s x = do
  debug <- asks debug
  if debug then trace s x else x

-- For now only store the debugging boolean
data EEnv = EEnv { debug   :: Bool     -- Should the evaluator be run in
                                       -- debug mode?
                 , mor     :: Morphism -- morphisms
                 , env    :: Env
                 , opaques :: [Binder]
                 }
  deriving (Show)

type Eval a = ReaderT EEnv Identity a

emptyEEnv :: Bool -> EEnv
emptyEEnv d = EEnv d idMor Empty []

runEval :: EEnv -> Eval a -> a
runEval e v = runIdentity $ runReaderT v e

look :: Ident -> Eval (Binder, Val)
look x = do r <- asks env
            case r of
              Pair rho (n@(y,l),u) | x == y    -> return $ (n, u)
                                   | otherwise -> local (inEnv rho) $ look x
              PDef es r1 -> case lookupIdent x es of
                              Just (y,t)  -> (y,) <$> eval t
                              Nothing     -> local (inEnv r1) $ look x

inEnv :: Env -> EEnv -> EEnv
inEnv rho e = e {env = rho}

addPairs :: [(Binder,Val)] -> EEnv -> EEnv
addPairs xus e@(EEnv{..}) = e {env = foldl Pair env xus}

addDecls :: Decls -> EEnv -> EEnv
addDecls decls e@(EEnv{..}) = e {env = pDef decls env}

addMor :: Morphism -> EEnv -> EEnv
addMor f e@(EEnv{..}) = e {mor = compMor mor f}

isOpaque :: Binder -> Eval Bool
isOpaque x = elem x <$> asks opaques

eval :: Ter -> Eval Val
eval U                    = return VU
eval t@(App r s)          = appM (eval r) (eval s)
eval (Var i)              = do
  (x,v) <- look i
  x_opaque <- isOpaque x
  if x_opaque then VVar ("opaque_" ++ show x) <$> asks mor else return v
eval (Pi a b)             = VPi <$> eval a <*> eval b
eval (Lam x t) = do
  eenv <- ask
  return $ Closure $ \f u -> runEval (addMor f $ addPairs [(x,u)] $ eenv) $ eval t
eval (Sigma a b)          = VSigma <$> eval a <*> eval b
eval (SPair a b)          = VSPair <$> eval a <*> eval b
eval (ColoredPair i a b)  = VCSPair i <$> eval a <*> eval b
eval (Fst a)              = fstSVal <$> eval a
eval (Snd a)              = sndSVal <$> eval a
eval (ColoredSnd i a)     = sndCSVal i <$> eval a
-- eval f e (Nabla _i a)         = eval f e a
eval (Where t (ODecls decls))  = local (addDecls decls) $ eval t
eval (Where t _)          = eval t
eval (Con name ts)        = VCon name <$> mapM eval ts
eval (Split pr alts)      = Ter (Split pr alts) <$> asks mor <*> asks env
eval (Sum pr ntss)        = Ter (Sum pr ntss) <$> asks mor <*> asks env
eval Undefined = VVar "undefined" <$> asks mor

evals :: [(Binder,Ter)] -> Eval [(Binder,Val)]
evals = sequenceSnd . map (second eval)

fstSVal, sndSVal :: Val -> Val
fstSVal (VSPair a b)    = a
fstSVal u | isNeutral u = VFst u
          | otherwise   = error $ show u ++ " should be neutral"
sndSVal (VSPair a b)    = b
sndSVal u | isNeutral u = VSnd u
          | otherwise   = error $ show u ++ " should be neutral"
sndCSVal i (VCSPair j a b) | i == j   = b
sndCSVal i u | isNeutral u = VCSnd i u
             | otherwise   = error $ show u ++ " should be neutral"

-- Application
app :: Val -> Val -> Eval Val
app (Closure cl) u = return $ cl idMor u
app (Ter (Split _ nvs) f e) (VCon name us) = case lookup name nvs of
    Just (xs,t)  -> local (addPairs (zip xs us)) $ eval t
    Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name
app u@(Ter (Split _ _) _ _) v
  | isNeutral v = return $ VSplit u v -- v should be neutral
  | otherwise   = error $ "app: (VSplit) " ++ show v ++ " is not neutral"
app (VCSPair i a b) v = do
  vi0 <- face i v
  VCSPair i <$> app a vi0 <*> apps b [vi0, sndCSVal i v]
app r s
  | isNeutral r = return $ VApp r s -- r should be neutral
  | otherwise   = error $ "app: (VApp) " ++ show r ++ " is not neutral"

-- Monadic version of app
appM :: Eval Val -> Eval Val -> Eval Val
appM t1 t2 = do
  u <- t1
  v <- t2
  app u v

apps :: Val -> [Val] -> Eval Val
apps = foldM app

-- Compute the face of an environment
appMorEnv :: Morphism -> Env -> Eval Env
appMorEnv f = mapEnvM (appMor f)

-- faceCtxt :: Ctxt -> Side -> Eval Ctxt
-- faceCtxt c xd = traverseSnds (`face` xd) c


faceName :: CVal -> Side -> CVal
faceName Nothing _ = Nothing
faceName (Just x) (y,d) | x == y    = Nothing
                        | otherwise = Just x

appMor :: Morphism -> Val -> Eval Val
appMor g u =
  let appg = appMor g in case u of
  VU         -> return VU
  Closure cl -> return $ Closure (\f u -> cl (compMor f g) u)
  Ter t f e  -> Ter t (compMor f g) <$> appMorEnv g e
  VPi a f    -> VPi <$> appg a <*> appg f
  VSigma a f -> VSigma <$> appg a <*> appg f
  VSPair a b -> VSPair <$> appg a <*> appg b
  VApp u v   -> appM (appg u) (appg v)
  VSplit u v -> appM (appg u) (appg v)
  VVar s f   -> return $ VVar s (compMor f g)
  VFst p     -> fstSVal <$> appg p
  VSnd p     -> sndSVal <$> appg p
  VCSnd y p  -> sndCSVal y <$> appg p
  VCSPair i a b -> case appMorName g i of
    Just j  -> VCSPair j <$> appg a <*> appg b
    Nothing -> appg a

appMorM :: Morphism -> Eval Val -> Eval Val
appMorM f t = do v <- t; appMor f v

face :: Color -> Val -> Eval Val
face i = appMor (faceMor i)

-- Conversion functions
(<&&>) :: Monad m => m Bool -> m Bool -> m Bool
(<&&>) = liftM2 (&&)

(<==>) :: (Monad m, Eq a) => a -> a -> m Bool
a <==> b = return (a == b)

andM :: [Eval Bool] -> Eval Bool
andM = liftM and . sequence

conv :: Int -> Morphism -> Val -> Val -> Eval Bool
conv k g v1 v2 =
  let cv = conv k g in
  case (v1, v2) of
    (VU, VU) -> return True
    (Closure cl, Closure cl') -> do
      let v = mkVar k g
      conv (k+1) g (cl idMor v) (cl' idMor v)
    (Closure cl, u') -> do
      let v = mkVar k g
      conv (k+1) g (cl idMor v) =<< (app u' v)
    (u', Closure cl) -> do
      let v = mkVar k g
      u'v <- app u' v
      conv (k+1) g u'v (cl idMor v)
    (Ter (Split p _) f e, Ter (Split p' _) f' e') ->
      pure (f == f' && p == p') <&&> convEnv k g e e'
    (Ter (Sum p _) f e,   Ter (Sum p' _) f' e')   ->
      pure (f == f' && p == p') <&&> convEnv k g e e'
    (VPi u v, VPi u' v') -> do
      let w = mkVar k g
      cv u u' <&&> convM (k+1) g (app v w) (app v' w)
    (VSigma u v, VSigma u' v') -> do
      let w = mkVar k g
      cv u u' <&&> convM (k+1) g (app v w) (app v' w)
    (VFst u, VFst u')          -> cv u u'
    (VSnd u, VSnd u')          -> cv u u'
    (VCSnd i u, VCSnd i' u')   -> pure (i == i') <&&> conv k g u u' -- Is this correct ?
    (VCon c us, VCon c' us')   -> liftM (\bs -> (c == c') && and bs) (zipWithM (cv) us us')
    (VSPair u v, VSPair u' v') -> cv u u' <&&> cv v v'
    (VSPair u v, w)            -> cv u (fstSVal w) <&&> cv v (sndSVal w)
    (w, VSPair u v)            -> cv (fstSVal w) u <&&> cv (sndSVal w) v
    (VCSPair i u v, VCSPair i' u' v')  -> pure (i == i') <&&> cv u u' <&&> cv v v'
    (VCSPair i u v, w)                 -> (cv u =<< (face i w)) <&&> cv v (sndCSVal i w)
    (w,             VCSPair i u v)     -> (cv u =<< (face i w)) <&&> cv v (sndCSVal i w)
    (VApp u v,      VApp u' v')     -> cv u u' <&&> cv v v'
    -- (VAppName u x,  VAppName u' x') -> cv u u' <&&> (x <==> x')
    (VSplit u v,    VSplit u' v')   -> cv u u' <&&> cv v v'
    (VVar x d,      VVar x' d')     -> return $ (x == x')   && (d == d')
    _                               -> return False

-- Monadic version of conv
convM :: Int -> Morphism -> Eval Val -> Eval Val -> Eval Bool
convM k g v1 v2 = join $ liftM2 (conv k g) v1 v2

convEnv :: Int -> Morphism -> Env -> Env -> Eval Bool
convEnv k g e e' = liftM and $ zipWithM (conv k g) (valOfEnv e) (valOfEnv e')
