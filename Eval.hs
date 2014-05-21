module Eval where

import Data.List

import CTT

look :: Ident -> Morphism -> Env -> (Binder, Val)
look x f (Pair rho (n@(y,l),u))
  | x == y    = (n, u)
  | otherwise = look x f rho
look x f r@(PDef es r1) = case lookupIdent x es of
  Just (y,t)  -> (y,eval f r t)
  Nothing     -> look x f r1

eval :: Morphism -> Env -> Ter -> Val
eval f e U                 = VU
eval f e (App r s)         = app (eval f e r) (eval f e s)
eval f e (Var i)           = snd (look i f e)
eval f e (Pi a b)          = VPi (eval f e a) (eval f e b)
eval f e (Lam x t)         = Ter (Lam x t) f e -- stop at lambdas
eval f e (Sigma a b)       = VSigma (eval f e a) (eval f e b)
eval f e (SPair a b)       = VSPair (eval f e a) (eval f e b)
eval f e (Fst a)           = fstSVal (eval f e a)
eval f e (Snd a)           = sndSVal (eval f e a)
eval f e (Where t decls)   = eval f (PDef [ (x,y) | (x,_,y) <- decls ] e) t
eval f e (Con name ts)     = VCon name (map (eval f e) ts)
eval f e (Split pr alts)   = Ter (Split pr alts) f e
eval f e (Sum pr ntss)     = Ter (Sum pr ntss) f e
eval f e (NamedPair i u v) = case appMorName f i of
  Just j  -> let e' = appMorEnv (faceMor (codomain f) j) e
                 f' = minusMor i f
             in VNSPair j (eval f' e' u) (eval f' e' v)
  Nothing -> eval (minusMor i f) e u
eval f e (NamedSnd i w)    =
  let (j,f')               = updateMor i f
  in eval f' e w `dot` j           -- TODO: implicit degeneracy okay?
eval f e (Undef _)         = error "undefined"

evals :: Morphism -> Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals f env bts = [ (b,eval f env t) | (b,t) <- bts ]

dot :: Val -> Name -> Val
dot (VNSPair i u v) j | i == j = v
dot u j = VNSnd j u

-- TODO: Finish!
app :: Val -> Val -> Val
app (Ter (Lam x t) f e) u = eval f (Pair e (x,u)) t
app (Ter (Split _ nvs) f e) (VCon name us) = case lookup name nvs of
    Just (xs,t)  -> eval f (upds e (zip xs us)) t
    Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name
app u@(Ter (Split _ _) _ _) v | isNeutral v = VSplit u v -- v should be neutral
                            | otherwise   = error $ "app: VSplit " ++ show v
                                                  ++ " is not neutral"
app (VNSPair i u v) (VNSPair i' a b) | i == i' =
  VNSPair i (app u a) (app (app v a) b)
app r s = VApp r s
-- TODO: fix neutral and use:
-- app r s | isNeutral r = VApp r s -- r should be neutral
--        | otherwise   = error $ "app: VApp " ++ show r ++ " is not neutral"

appMorEnv :: Morphism -> Env -> Env
appMorEnv f = mapEnv (appMor f)

appMor :: Morphism -> Val -> Val
appMor g u = case u of
  VU            -> VU
  VCon n vs     -> VCon n (map (appMor g) vs)
  Ter t f e     -> Ter t (compMor f g) (appMorEnv g e)
  VPi a f       -> VPi (appMor g a) (appMor g f)
  VSigma a f    -> VSigma (appMor g a) (appMor g f)
  VSPair a b    -> VSPair (appMor g a) (appMor g b)
  VApp u v      -> app (appMor g u) (appMor g v)
  VSplit u v    -> app (appMor g u) (appMor g v)
  VVar s d      -> VVar s (map (maybe Nothing (appMorName g)) d)
  VFst p        -> fstSVal (appMor g p)
  VSnd p        -> sndSVal (appMor g p)
  VNSnd i p     -> let (j,g') = updateMor i g
                   in appMor g' p `dot` j
  VNSPair i a b -> let g' = minusMor i g
                   in case appMorName g i of
    Just j  -> VNSPair j (appMor g' a) (appMor g' b)
    Nothing -> appMor g' a
  _ -> error $ "appMor: " ++ show u

-- sndNSVal :: Name -> Val -> Val
-- sndNSVal i (VNSPair j a b) | i == j   = b
-- sndNSVal i u | isNeutral u = VNSnd i u
--              | otherwise   = error $ show u ++ " should be neutral"

fstSVal, sndSVal :: Val -> Val
fstSVal (VSPair a b)    = a
fstSVal u | isNeutral u = VFst u
          | otherwise   = error $ show u ++ " should be neutral"
sndSVal (VSPair a b)    = b
sndSVal u | isNeutral u = VSnd u
          | otherwise   = error $ show u ++ " should be neutral"

conv :: Int -> [Name] -> Val -> Val -> Bool
conv k xs VU VU                                       = True
conv k xs (Ter (Lam x u) f e) (Ter (Lam x' u') f' e') =
  let v = mkVar k xs
  in conv (k+1) xs (eval f (Pair e (x,v)) u) (eval f' (Pair e' (x',v)) u')
conv k xs (Ter (Lam x u) f e) u' =
  let v = mkVar k xs
  in conv (k+1) xs (eval f (Pair e (x,v)) u) (app u' v)
conv k xs u' (Ter (Lam x u) f e) =
  let v = mkVar k xs
  in conv (k+1) xs (app u' v) (eval f (Pair e (x,v)) u)
conv k xs (Ter (Split p _) f e) (Ter (Split p' _) f' e') =
  (p == p' && f == f') && convEnv k xs e e'
conv k xs (Ter (Sum p _) f e)   (Ter (Sum p' _) f' e') =
  (p == p' && f == f') && convEnv k xs e e'
conv k xs (Ter (Undef p) f e) (Ter (Undef p') f' e') =
  (p == p' && f == f') && convEnv k xs e e'
conv k xs (VPi u v) (VPi u' v') =
  let w = mkVar k xs
  in conv k xs u u' && conv (k+1) xs (app v w) (app v' w)
conv k xs (VSigma u v) (VSigma u' v') =
  let w = mkVar k xs
  in conv k xs u u' && conv (k+1) xs (app v w) (app v' w)
conv k xs (VFst u) (VFst u') = conv k xs u u'
conv k xs (VSnd u) (VSnd u') = conv k xs u u'
conv k xs (VCon c us) (VCon c' us') =
  (c == c') && and (zipWith (conv k xs) us us')
conv k xs (VSPair u v) (VSPair u' v')   = conv k xs u u' && conv k xs v v'
conv k xs (VSPair u v) w                =
  conv k xs u (fstSVal w) && conv k xs v (sndSVal w)
conv k xs w            (VSPair u v)     =
  conv k xs (fstSVal w) u && conv k xs (sndSVal w) v
conv k xs (VApp u v)     (VApp u' v')   = conv k xs u u' && conv k xs v v'
conv k xs (VSplit u v)   (VSplit u' v') = conv k xs u u' && conv k xs v v'
conv k xs (VVar x d)     (VVar x' d')   = (x == x') && (d == d')
conv k xs (VNSnd i u) (VNSnd i' u')     =
  conv k (i:xs) u (appMor (swapMor xs i' i) u')
conv k xs (VNSPair i u v) (VNSPair i' u' v') = i == i' &&
  conv k (delete i xs) u u' && conv k (delete i xs) v v'
conv k _ _              _               = False

convEnv :: Int -> [Name] -> Env -> Env -> Bool
convEnv k xs e e' = and $ zipWith (conv k xs) (valOfEnv e) (valOfEnv e')


-- data Val = VU
--          | Ter Ter Morphism Env
--          | VPi Val Val
--          | VId Val Val Val
--          | VSigma Val Val
--          | VSPair Val Val
--          | VCon Ident [Val]
--          | VNSPair Name Val Val
--          | VNSnd Name Val
--          | VApp Val Val            -- the first Val must be neutral
--          | VSplit Val Val          -- the second Val must be neutral
--          | VVar String Dim
--          | VFst Val
--          | VSnd Val
--   deriving Eq


reifyVal :: Int -> Val -> Ter
reifyVal _ VU = U
reifyVal k (Ter (Lam n t) f env) =
  Lam n (eval f (Pair env (n, mkVar k (codomain f))) t)
-- TODO: What about the f part?
reifyVal k (Ter (Split loc brcs) _ env) = RSplit loc brcs (reifyEnv k env)
reifyEnv k (Ter (Sum n lbls) _ env)     = RSum n lbls (reifyEnv k env)
reifyVal k (VPi a f)    = Pi (reifyVal k a) (reifyVal k f)
reifyVal k (VSigma a f) = Sigma (reifyVal k a) (reifyVal k f)
reifyVal k (VSPair u v) = SPair (reifyVal k u) (reifyVal k v)
reifyVal k (VCon n us)  = Con n (map (reifyVal k) us)
reifyVal k (VNSPair i u v) = NamedPair i (reifyVal k u) (reifyVal k v)
reifyVal k (VNSnd i u)  = NamedSnd i (reifyVal k u)
reifyVal k (VApp u v)   = App (reifyVal k u) (reifyVal k v)
-- TODO: Can't we throw out VSplit?!
-- t is a split, and v neutral
--reifyVal k (VSplit (Ter t f env) v) = App ()
reifyVal k (VVar n dim) = Var n -- or should we anotate with dim's?
reifyVal k (VFst u)     = Fst (reifyVal k u)
reifyVal k (VSnd u)     = Snd (reifyVal k u)

reifyEnv :: Int -> Env -> Tele
reifyEnv _ Empty = []
reifyEnv k (Pair e (x,v)) = (x,reifyEnv k v) : reifyEnv k e
reifyEnv k (PDef _ e)     = reifyEnv k e