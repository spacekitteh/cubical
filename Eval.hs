module Eval where

import Data.List
import Data.Maybe (fromMaybe)

import CTT

look :: Ident -> Env -> (Binder, Val)
look x (Pair rho (n@(y,l),u))
  | x == y    = (n, u)
  | otherwise = look x rho
look x r@(PDef es r1) = case lookupIdent x es of
  Just (y,t)  -> (y,eval r t)
  Nothing     -> look x r1

eval :: Env -> Ter -> Val
eval _ U               = VU
eval e (Param i t)     = param i (eval e t)
eval e (App r s)       = app (eval e r) (eval e s)
eval e (Var i)         = snd (look i e)
eval e (Pi a b)        = VPi (eval e a) (eval e b)
eval e (Lam x t u)     = Ter (eval e t) (\xv -> eval (Pair e (x,xv)) u) -- stop at lambdas
eval e (Sigma a b)     = VSigma (eval e a) (eval e b)
eval e (SPair a b)     = VSPair (eval e a) (eval e b)
eval e (Fst a)         = fstSVal (eval e a)
eval e (Snd a)         = sndSVal (eval e a)
eval e (Where t decls) = eval (PDef [ (x,y) | (x,_,y) <- decls ] e) t
eval e (Con name ts)   = VCon name (map (eval e) ts)
-- eval e (Split pr alts) = Ter (Split pr alts) e
-- eval e (Sum pr ntss)   = Ter (Sum pr ntss) e
eval _ (Undef _)       = error "undefined"

evals :: Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]

face :: Color -> Val -> Val
face i t = case t of
  VU -> VU
  Ter ty f -> Ter (face i ty) $ \x -> face i (f x)
  VPi a b -> VPi (face i a) (face i b)
  VSigma a b -> VSigma (face i a) (face i b)
  VSPair a b -> VSPair (face i a) (face i b)
  VCon x vs -> VCon x (map (face i) vs)
  VApp a b -> VApp (face i a) (face i b)
  VSplit a b -> VSplit (face i a) (face i b)
  VFst a -> VFst (face i a)
  VSnd a -> VSnd (face i a)
  VCPair j a b ty | j == i -> a
                  | otherwise -> VCPair j (face i a) (face i b) (face i ty)
  VParam f -> VParam $ \c -> face i (f c)
  VVar x -> VVar x

vpi a b = VPi a $ Ter a b
vcSig i a b = VCPair i a (Ter a b) VU
vSig a b = VSigma a (Ter a b)

paramT :: Color -> Val -> Val -> Val
paramT i VU t = vpi t (\_ -> VU)
paramT i (VPi a g) f = vpi (face i a) $ \x -> vpi (paramT i a x) $ \xi ->
                    paramT i (g `app` (VCPair i x xi a))  (f `app` x)
paramT i (VCPair j a b VU) xx | i == j = b
                              | otherwise = vcSig j (paramT i a (face i xx)) $ \xj -> param i b `app` (face i xx) `app` xj `app` (param i xx)
paramT i (VSigma a b) xx = vSig (paramT i a (face i xx)) $ \xj -> param i b `app` (face i xx) `app` xj `app` (param i xx)
paramT i t x = param i t `app` x

substCol :: Color -> Color -> Val -> Val
substCol = error "color substitution not implemented"

param :: Color -> Val -> Val
param i t = case t of
  Ter a f -> Ter (face i a) $ \x -> Ter (paramT i a x) $ \xi -> param i (f $ VCPair i x xi a)
  VCPair j _ b _ | j == i -> b
  VCPair j a b (ty@(VCPair k _ _ VU)) | j == k -> VCPair j (param i a) (param i b) (paramT i ty (face i t))
  VSPair a b -> VSPair (param i a) (param i b)
  VFst a -> VFst (param i a)
  VSnd a -> VSnd (param i a)
  VVar _ -> stop
  VParam _ -> stop
  VApp _ _ -> stop
  VCPair _ _ _ VU -> typ
  VPi _ _ -> typ
  VSigma _ _ -> typ
  VU -> typ
 where stop = VParam (\c -> substCol i c t)
       typ = Ter (face i t) $ \x -> paramT i t x

app :: Val -> Val -> Val
app (VApp (VParam f) a) ai = VParam $ \c -> (f c `app` (VCPair c a ai (error "TYPE HEERE!")))
app (VCPair i f g (VPi _a b)) u = VCPair i (app f (face i u)) ((g `app` (face i u)) `app` param i u) (b `app` u)
app (Ter _ f) u = f u
-- app (Ter (Split _ nvs) e) (VCon name us) = case lookup name nvs of
--     Just (xs,t) -> eval (upds e (zip xs us)) t
--     Nothing -> error $ "app: Split with insufficient arguments; " ++
--                         "missing case for " ++ name
-- app u@(Ter (Split _ _) _) v | isNeutral v = VSplit u v -- v should be neutral
--                             | otherwise   = error $ "app: VSplit " ++ show v
--                                                   ++ " is not neutral"
app r s | isNeutral r = VApp r s -- r should be neutral
        | otherwise   = error $ "app: VApp " ++ show r ++ " is not neutral"

fstSVal, sndSVal :: Val -> Val
fstSVal (VSPair a b)    = a
fstSVal u | isNeutral u = VFst u
          | otherwise   = error $ show u ++ " should be neutral"
sndSVal (VSPair a b)    = b
sndSVal u | isNeutral u = VSnd u
          | otherwise   = error $ show u ++ " should be neutral"

-- conversion test
conv :: Int -> Val -> Val -> Bool
conv k VU VU                                  = True
conv k (Ter _ f) (Ter _ f') = do
  let v = mkVar k
  conv (k+1) (f v) (f' v)
conv k (Ter _ f) u' = do
  let v = mkVar k
  conv (k+1) (f v) (app u' v)
conv k u' (Ter _ f) = do
  let v = mkVar k
  conv (k+1) (app u' v) (f v)
-- conv k (Ter (Split p _) e) (Ter (Split p' _) e') =
--   (p == p') && convEnv k e e'
-- conv k (Ter (Sum p _) e)   (Ter (Sum p' _) e') =
--   (p == p') && convEnv k e e'
-- conv k (Ter (Undef p) e) (Ter (Undef p') e') =
--   (p == p') && convEnv k e e'
conv k (VPi u v) (VPi u' v') = do
  let w = mkVar k
  conv k u u' && conv (k+1) (app v w) (app v' w)
conv k (VSigma u v) (VSigma u' v') = do
  let w = mkVar k
  conv k u u' && conv (k+1) (app v w) (app v' w)
conv k (VFst u) (VFst u') = conv k u u'
conv k (VSnd u) (VSnd u') = conv k u u'
conv k (VCon c us) (VCon c' us') =
  (c == c') && and (zipWith (conv k) us us')
conv k (VSPair u v) (VSPair u' v') = conv k u u' && conv k v v'
conv k (VSPair u v) w              =
  conv k u (fstSVal w) && conv k v (sndSVal w)
conv k w            (VSPair u v)   =
  conv k (fstSVal w) u && conv k (sndSVal w) v
conv k (VApp u v)   (VApp u' v')   = conv k u u' && conv k v v'
conv k (VSplit u v) (VSplit u' v') = conv k u u' && conv k v v'
conv k (VVar x)     (VVar x')      = x == x'
conv k _              _            = False

convEnv :: Int -> Env -> Env -> Bool
convEnv k e e' = and $ zipWith (conv k) (valOfEnv e) (valOfEnv e')
