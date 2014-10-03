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
eval e (Lam x t u)     = VLam (eval e t) (\xv -> eval (Pair e (x,xv)) u) -- stop at lambdas
eval e (Sigma a b)     = VSigma (eval e a) (eval e b)
eval e (SPair a b)     = VSPair (eval e a) (eval e b)
eval e (Fst a)         = fstSVal (eval e a)
eval e (Snd a)         = sndSVal (eval e a)
eval e (Where t decls) = eval (PDef [ (x,y) | (x,_,y) <- decls ] e) t
eval e (Con name ts)   = VCon name (map (eval e) ts)
eval e (Split pr alts) = Ter (Split pr alts) e
eval e (Sum pr ntss)   = Ter (Sum pr ntss) e
eval _ (Undef _)       = error "undefined"
evals :: Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]

second f (a,b) = (a,f b)
faceTer :: Color -> Ter -> Ter
faceTer i t0 = let fc = faceTer i in case t0 of
  App t u -> App (fc t) (fc u)
  Pi t u -> Pi (fc t) (fc u)
  Lam b t u -> Lam b (fc t) (fc u)
  Sigma t u -> Sigma (fc t) (fc u)
  SPair t u -> SPair (fc t) (fc u)
  Fst t -> Fst (fc t)
  Snd t -> Snd (fc t)
  Where t ds -> Where (fc t) [ (b, fc u, fc v) | (b,u,v) <- ds]
  Var x -> Var x
  U -> U
  Param j t | i == j -> Param j t
            | i /= j -> Param j (fc t)
  Con l ts -> Con l (map fc ts)
  Split loc brcs -> Split loc (map (second (second fc)) brcs)
  Sum b lblsum -> Sum b (map (second (map (second fc))) lblsum)
  Undef loc -> Undef loc
  
face :: Color -> Val -> Val
face i t = case t of
  VU -> VU
  Ter ter e -> Ter (faceTer i ter) e
  VLam ty f -> VLam (face i ty) $ \x -> face i (f x)
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
  VParam j v -> VParam k (face i (v `swap` (j,k)))
    where k = fresh (v,i,j)
  VVar x ty -> VVar x (face i ty)

vpi a b = VPi a $ VLam a b
vcSig i a b = VCPair i a (VLam a b) VU
vSig a b = VSigma a (VLam a b)

paramT :: Color -> Val -> Val -> Val
paramT i VU t = vpi t (\_ -> VU)
paramT i (VPi a g) f = vpi (face i a) $ \x -> vpi (paramT i a x) $ \xi ->
                    paramT i (g `app` (VCPair i x xi a))  (f `app` x)
paramT i (VCPair j a b VU) xx | i == j = b `app` xx
                              | otherwise = vcSig j (paramT i a (face i xx)) $ \xj -> param i b `app` (face i xx) `app` xj `app` (param i xx)
paramT i (VSigma a b) xx = vSig (paramT i a (face i xx)) $ \xj -> param i b `app` (face i xx) `app` xj `app` (param i xx)
paramT i t x = param i t `app` x

-- substCol :: Color -> Color -> Val -> Val
-- substCol = error "color substitution not implemented"

param :: Color -> Val -> Val
param i t = case t of
  VLam a f -> VLam (face i a) $ \x -> VLam (paramT i a x) $ \xi -> param i (f $ VCPair i x xi a)
  VCPair j _ b _ | j == i -> b
  VCPair j a b (ty@(VCPair k _ _ VU)) | j == k -> VCPair j (param i a) (param i b) (paramT i ty (face i t))
  VSPair a b -> VSPair (param i a) (param i b)
  VFst a -> VFst (param i a)
  VSnd a -> VSnd (param i a)
  VVar _ _ -> stop
  VParam _ _ -> stop
  VApp _ _ -> stop
  VCPair _ _ _ VU -> typ
  VPi _ _ -> typ
  VSigma _ _ -> typ
  VU -> typ
 where stop = VParam i t
       typ = VLam (face i t) $ \x -> paramT i t x

neuTyp :: Val -> Val
neuTyp v0 = case v0 of
   VVar _ ty -> ty
   VCPair _ _ _ t -> t
   VParam i t -> paramT i (neuTyp t) (face i t)
   VApp n u -> case neuTyp n of
     VPi _ b -> b `app` u
     _ -> error "neuTyp: panic"
   VFst n -> case neuTyp n of
     VSigma a _ -> a
     _ -> error "neuTyp: VFst: panic"
   VSnd n -> case neuTyp n of
     VSigma _ b -> b `app` fstSVal n
     _ -> error "neuTyp: VSnd: panic"
  
app :: Val -> Val -> Val
app (VApp (VParam i f) a) ai = VParam i (f `app` (VCPair i a ai arg))
  where VPi arg _ = neuTyp f
app (VCPair i f g (VPi _a b)) u = VCPair i (app f (face i u)) ((g `app` (face i u)) `app` param i u) (b `app` u)
app (VLam _ f) u = f u
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
conv k (VLam ty f) (VLam _ f') = do
  let v = mkVar k ty
  conv (k+1) (f v) (f' v)
conv k (VLam ty f) u' = do
  let v = mkVar k ty
  conv (k+1) (f v) (app u' v)
conv k u' (VLam ty f) = do
  let v = mkVar k ty
  conv (k+1) (app u' v) (f v)
conv k (Ter (Split p _) e) (Ter (Split p' _) e') =
  (p == p') && convEnv k e e'
conv k (Ter (Sum p _) e)   (Ter (Sum p' _) e') =
  (p == p') && convEnv k e e'
conv k (Ter (Undef p) e) (Ter (Undef p') e') =
  (p == p') && convEnv k e e'
conv k (VPi u v) (VPi u' v') = do
  let w = mkVar k u
  conv k u u' && conv (k+1) (app v w) (app v' w)
conv k (VSigma u v) (VSigma u' v') = do
  let w = mkVar k u
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
conv k (VVar x _) (VVar x' _)      = x == x'
conv k (VParam i u) (VParam j v)   = conv k u (swap v (i,j))
conv k _              _            = False

convEnv :: Int -> Env -> Env -> Bool
convEnv k e e' = and $ zipWith (conv k) (valOfEnv e) (valOfEnv e')
