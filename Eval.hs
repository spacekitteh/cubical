{-# LANGUAGE TupleSections #-}
module Eval ( evalTer
            , evalTers
            , appVal
            , convVal
            , fstSVal
            , runEval
            , Eval
            , faceEnv
            -- , faceCtxt
            , face
            ) where

import Control.Applicative
import Control.Arrow (second)
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State
import Data.Functor.Identity
import Data.List
import Data.Maybe (fromMaybe)

import Debug.Trace

import CTT

traceb :: String -> Eval a -> Eval a
traceb s x = do
  debug <- get
  if debug then trace s x else x

-- For now only store the debugging boolean
type EState = Bool

type Eval a = StateT EState Identity a

runEval :: Bool -> Eval a -> a
runEval debug e = runIdentity $ evalStateT e debug

evalTer :: Bool -> OEnv -> Ter -> Val
evalTer b env = runEval b . eval env

evalTers :: Bool -> OEnv -> [(Binder,Ter)] -> [(Binder,Val)]
evalTers b env bts = runEval b (evals env bts)

appVal :: Bool -> Val -> Val -> Val
appVal b v1 v2 = runEval b $ app v1 v2

convVal :: Bool -> Int -> [Color] -> Val -> Val -> Bool
convVal b k cs v1 v2 = runEval b $ conv k cs v1 v2

look :: Ident -> OEnv -> Eval (Binder, Val)
look x (OEnv (Pair rho (n@(y,l),u)) opaques)
  | x == y    = return $ (n, u)
  | otherwise = look x (OEnv rho opaques)
look x r@(OEnv (PDef es r1) o) = case lookupIdent x es of
  Just (y,t)  -> (y,) <$> eval r t
  Nothing     -> look x (OEnv r1 o)

eval :: OEnv -> Ter -> Eval Val
eval e U                    = return VU
eval e t@(App r s)          = appM (eval e r) (eval e s)
eval e (Var i)              = do
  (x,v) <- look i e
  return $ if x `elem` opaques e then VVar ("opaque_" ++ show x) $ map Just (support v) else v
eval e (Pi a b)             = VPi <$> eval e a <*> eval e b
eval e (Lam x t)            = return $ Ter [] (Lam x t) e -- stop at lambdas
eval e (Sigma a b)          = VSigma <$> eval e a <*> eval e b
eval e (SPair a b)          = VSPair <$> eval e a <*> eval e b
eval e (ColoredSigma i a b) = VCSigma i <$> eval e a <*> eval e b
eval e (ColoredPair i a b)  = VCSPair i <$> eval e a <*> eval e b
eval e (ColoredFunPair i a b)  = VCFPair i <$> eval e a <*> eval e b
eval e (Fst a)              = fstSVal <$> eval e a
eval e (Snd a)              = sndSVal <$> eval e a
eval e (ColoredSnd i a)     = sndCSVal i <$> eval e a
eval e (ColoredFst i a)     = do v <- eval e a
                                 face v (i,0)
eval e (Nabla _i a)         = eval e a
eval e (Where t decls)      = eval (oPDef False decls e) t
eval e (Con name ts)        = VCon name <$> mapM (eval e) ts
eval e (Split pr alts)      = return $ Ter [] (Split pr alts) e
eval e (Sum pr ntss)        = return $ Ter [] (Sum pr ntss) e
eval e Undefined = return $ VVar "undefined" []

evals :: OEnv -> [(Binder,Ter)] -> Eval [(Binder,Val)]
evals env = sequenceSnd . map (second (eval env))

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
app (Ter f (Lam x t) e) u                         = faces f =<< eval (oPair e (x,u)) t
app (Ter f (Split _ nvs) e) (VCon name us) = case lookup name nvs of
    Just (xs,t)  -> faces f =<< eval (upds e (zip xs us)) t
    Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name
app u@(Ter f (Split _ _) _) v
  | isNeutral v = return $ VSplit u v -- v should be neutral
  | otherwise   = error $ "app: (VSplit) " ++ show v ++ " is not neutral"
app (VCFPair i a b) v = do
  vi0 <- face v (i,0)
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
faceEnv :: OEnv -> Side -> Eval OEnv
faceEnv e xd = mapOEnvM (`face` xd) e

-- faceCtxt :: Ctxt -> Side -> Eval Ctxt
-- faceCtxt c xd = traverseSnds (`face` xd) c


faceName :: CVal -> Side -> CVal
faceName Nothing _ = Nothing
faceName (Just x) (y,d) | x == y    = Nothing
                        | otherwise = Just x

faces :: [Color] -> Val -> Eval Val
faces [] x = return x
faces (c:cs) x = (`face` (c,0)) =<< faces cs x

-- Compute the face of a value
face :: Val -> Side -> Eval Val
face u xdir@(x,dir) =
  let fc v = v `face` xdir in case u of
  VU         -> return VU
  Ter fs t e    -> return $ Ter (x:fs) t e
  VPi a f    -> VPi <$> fc a <*> fc f
  VSigma a f -> VSigma <$> fc a <*> fc f
  VSPair a b -> VSPair <$> fc a <*> fc b
  VApp u v            -> appM (fc u) (fc v)
  VSplit u v          -> appM (fc u) (fc v)
  VVar s d            -> return $ VVar s [ faceName n xdir | n <- d ]
  VFst p              -> fstSVal <$> fc p
  VSnd p              -> sndSVal <$> fc p
  VCSigma y a f | x == y -> return a
                | otherwise -> VCSigma y <$> fc a <*> fc f
  VCSPair y a f | x == y -> return a
                | otherwise -> VCSPair y <$> fc a <*> fc f
  VCFPair y a f | x == y -> return a
                | otherwise -> VCFPair y <$> fc a <*> fc f
  VCSnd y p  -> sndCSVal y <$> fc p

faceM :: Eval Val -> Side -> Eval Val
faceM t xdir = do
  v <- t
  v `face` xdir

-- Conversion functions
(<&&>) :: Monad m => m Bool -> m Bool -> m Bool
(<&&>) = liftM2 (&&)

(<==>) :: (Monad m, Eq a) => a -> a -> m Bool
a <==> b = return (a == b)

andM :: [Eval Bool] -> Eval Bool
andM = liftM and . sequence

conv :: Int -> [Color] -> Val -> Val -> Eval Bool
conv k cs v1 v2 =
  let cv = conv k cs in
  case (v1, v2) of
    (VU, VU) -> return True
    (Ter f (Lam x u) e, Ter f' (Lam x' u') e') -> do
      let v = mkVar k cs
      convM (k+1) cs (faces f =<< eval (oPair e (x,v)) u) (faces f' =<< eval (oPair e' (x',v)) u')
    (Ter f (Lam x u) e, u') -> do
      let v = mkVar k cs
      convM (k+1) cs (faces f =<< eval (oPair e (x,v)) u) (app u' v)
    (u', Ter f (Lam x u) e) -> do
      let v = mkVar k cs
      convM (k+1) cs (app u' v) (eval (oPair e (x,v)) u)
    (Ter f (Split p _) e, Ter f' (Split p' _) e') -> pure (f == f' && p == p') <&&> convEnv k cs e e'
    (Ter f (Sum p _) e,   Ter f' (Sum p' _) e')   -> pure (f == f' && p == p') <&&> convEnv k cs e e'
    (VPi u v, VPi u' v') -> do
      let w = mkVar k cs
      cv u u' <&&> convM (k+1) cs (app v w) (app v' w)
    (VSigma u v, VSigma u' v') -> do
      let w = mkVar k cs
      cv u u' <&&> convM (k+1) cs (app v w) (app v' w)
    (VCSigma i u v, VCSigma i' u' v') -> do
      let w = mkVar k cs
      ((i == i') &&) <$> cv u u' <&&> convM (k+1) cs (app v w) (app v' w)
    (VFst u, VFst u')          -> cv u u'
    (VSnd u, VSnd u')          -> cv u u'
    (VCSnd i u, VCSnd i' u')   -> pure (i == i') <&&> conv k (i:cs) u u' -- Is this correct ?
    (VCon c us, VCon c' us')   -> liftM (\bs -> (c == c') && and bs) (zipWithM (cv) us us')
    (VSPair u v, VSPair u' v') -> cv u u' <&&> cv v v'
    (VSPair u v, w)            -> cv u (fstSVal w) <&&> cv v (sndSVal w)
    (w, VSPair u v)            -> cv (fstSVal w) u <&&> cv (sndSVal w) v
    (VCSPair i u v, VCSPair i' u' v')  -> pure (i == i') <&&> cv u u' <&&> cv v v'
    (VCSPair i u v, w)                 -> (cv u =<< (face w (i,0))) <&&> cv v (sndCSVal i w)
    (w,             VCSPair i u v)     -> (cv u =<< (face w (i,0))) <&&> cv v (sndCSVal i w)
    (VCFPair i u v, VCFPair i' u' v')  -> pure (i == i') <&&> cv u u' <&&> cv v v'
    (VCFPair i u v, w)              -> (cv u =<< (face w (i,0))) <&&> cv v (sndCSVal i w)
    (w,             VCFPair i u v)  -> (cv u =<< (face w (i,0))) <&&> cv v (sndCSVal i w)
    (VApp u v,      VApp u' v')     -> cv u u' <&&> cv v v'
    (VAppName u x,  VAppName u' x') -> cv u u' <&&> (x <==> x')
    (VSplit u v,    VSplit u' v')   -> cv u u' <&&> cv v v'
    (VVar x d,      VVar x' d')     -> return $ (x == x')   && (d == d')
    _                               -> return False
  
-- Monadic version of conv
convM :: Int -> [Color] -> Eval Val -> Eval Val -> Eval Bool
convM k cs v1 v2 = do
  v1' <- v1
  v2' <- v2
  conv k cs v1' v2'

convEnv :: Int -> [Color] -> OEnv -> OEnv -> Eval Bool
convEnv k cs e e' = liftM and $ zipWithM (conv k cs) (valOfOEnv e) (valOfOEnv e')
