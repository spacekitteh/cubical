{-# LANGUAGE PatternGuards #-}

module Eval where

import Data.List
import Data.Maybe (fromMaybe)
import Control.Applicative

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
eval e (Param n i t)   = param n i (eval e t)
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
  Param n j t | i == j -> Param n j t
              | i /= j -> Param n j (fc t)
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
  VParam n j v -> VParam n k (face i (v `swap` (j,k)))
    where k = fresh (v,i,j)
  VVar x ty -> VVar x (face i ty)

vpi a b = VPi a $ VLam a b
vcSig i a b = VCPair i a (VLam a b) VU
vSig a b = VSigma a (VLam a b)
vFun a b = vpi a (\_ -> b) 

testTarget :: (Val -> Bool) -> VTele -> Bool
testTarget p t = case t of
  Nil x -> p x
  Cons a f -> testTarget p (f $ VVar "testTarget" a)

isVU VU = True
isVU _ = False

isRelTyp :: VTele -> Bool
isRelTyp = testTarget isVU

isRel :: VTele -> Bool
isRel = testTarget isType

getPiTele :: Val -> VTele
getPiTele (VPi a f) = Cons a $ \x -> getPiTele (f `app` x)
getPiTele x = Nil x

getPiTeleN :: Int -> Val -> VTele
getPiTeleN 0 x = Nil x
getPiTeleN n (VPi a f) = Cons a $ \x -> getPiTeleN (n-1) (f `app` x)
getPiTeleN _ x = Nil x

getLamTeleN :: Int -> Val -> VTele
getLamTeleN 0 x = Nil x
getLamTeleN n (VLam a f) = Cons a $ \x -> getLamTeleN (n-1) (f x)
getLamTeleN _ x = Nil x

lenT n getter x | l == n = Just tele
                | otherwise = Nothing
  where tele = getter n x
        l = teleLen tele
  
teleLen :: VTele -> Int
teleLen (Nil _) = 0
teleLen (Cons a f) = 1 + teleLen (f $ VVar "teleLen" a)

data VTele = Nil Val | Cons Val (Val -> VTele)

instance Show VTele where
  show (Nil x) = show x
  show (Cons x xs) = "x:" ++ show x ++ ", " ++ show (xs $ VVar "x" x)
type Rel = [Val] -> Val


type BindOp = Val -> (Val -> Val) -> Val


faceTele :: BindOp -> Color -> VTele -> [Val] -> ([Val] -> Val) -> Val
faceTele _ _ (Nil _) xs k = k xs
faceTele bind i (Cons a gamma) xs k = bind (face i a) $ \x -> faceTele bind i (gamma x) (x:xs) k

paramTele' :: [Int] -> BindOp -> Color -> VTele -> [Val] -> (Val -> Val) -> Val
paramTele' _ _ _ (Nil b) [] g = g b
paramTele' (l:ls) bind i (Cons a gamma) (x:xs) g = bind (paramT l i a x) $ \xi -> paramTele' ls bind i (gamma (VCPair i x xi a)) xs g

paramTele :: Int -> BindOp -> Color -> VTele -> [Val] -> (Val -> Val) -> Val
paramTele n = paramTele' (paramLevels n)

mkRelTyp :: Int -> Color -> VTele -> Val -> Val
mkRelTyp n i tele rel = faceTele vpi i tele [] $ \xs ->
                      vFun (rel `apps` xs) $
                      paramTele n vpi i tele xs $
                      \_ -> VU

mkFunTyp :: Int -> Color -> VTele -> Val -> Val
mkFunTyp n i tele f =
  faceTele vpi i tele [] $ \xs ->
  paramTele n vpi i tele xs $ \b ->
  paramT n i b (f `apps` xs)

getArgs :: Int -> Val -> Maybe (Val, [Val])
getArgs 0 x = Just (x, [])
getArgs n (VApp f a) = second (++[a]) <$> getArgs (n-1) f
getArgs _ _ = Nothing

apps :: Val -> [Val] -> Val
apps = foldl app

paramTelescope :: Int -> Color -> Env -> Tele -> [Val] -> Val
paramTelescope n i env ((b,t):tele) (a:as) =
  vSig (paramT n i t' a) (\ai -> paramTelescope n i (Pair env (b,VCPair i a ai t')) tele as)
  where t' = eval env t
paramTelescope n i env [] [] = Ter (Sum ("1",Loc "paramTelescope"(1,1)) []) Empty

paramT :: Int -> Color -> Val -> Val -> Val
paramT n i t0 xx = case t0 of
  VU -> vFun xx VU
  Ter (Sum _ lblsum) env -> case xx of
    VCon c as ->
      let Just (_bnd,tele) = lookupIdent c lblsum
      in paramTelescope n i env tele as
    _ -> stop
  -- Relation
  _ | Just tele <- lenT (2^(n-1)-1) getPiTeleN t0, isRelTyp tele -> mkRelTyp n i tele xx
  -- Pi
  _ | Just tele <- lenT (2^(n-1))   getPiTeleN t0 -> mkFunTyp n i tele xx
  -- Applied relation
  _ | Just (p,args) <- getArgs (2^(n-1)-1) t0 -> ext p `apps` map (face i) args `app` xx `apps` paramArgs n i args
  (VSigma a b) -> vSig (extT a (face i xx)) $ \xj -> ext b `app` (face i xx) `app` xj `app` (ext xx)
  _ -> ext t0 `app` xx
 where ext = param n i
       extT = paramT n i
       stop = VApp (VParam n i t0) xx

paramLevels 1 = [1]
paramLevels n = paramLevels (n-1) ++ map (1+) (paramLevels (n-1))

paramArgs :: Int -> Color -> [Val] -> [Val]
paramArgs n i xs = zipWith (\l -> param l i) (paramLevels n) xs

param :: Int -> Color -> Val -> Val
param n i t0 = case t0 of
  -- Ter (Sum p lblsum) env -> flip Ter env $ Split (snd p) -- FIXME: encode n i in here.
  --    [(con,) | (con,vars) <- lblsum]

  -- VLam a f -> VLam (face i a) $ \x -> VLam (extT a x) $ \xi -> ext (f $ VCPair i x xi a)
  -- Function
  _ | Just tele <- lenT (2^(n-1)) getLamTeleN t0 ->
    faceTele VLam i tele [] $ \xs ->
    paramTele n VLam i tele xs $ \b ->
    param n i b
  VCPair j a b ty | j == i -> b
                  | otherwise -> VCPair j (ext a) (param (n+1) i b) (extT ty (face i t0))
  VSPair a b -> VSPair (ext a) (ext b)
  VFst a -> VFst (ext a)
  VSnd a -> VSnd (ext a)
  VVar _ _ -> stop
  VParam m j u | n > m -> VParam m j $ param (n-1) i u
               | otherwise -> stop
  _ | Just (f,args) <- getArgs (2^(n-1)) t0 ->
    ext f `apps` map (face i) args `apps` paramArgs n i args
  -- Predicate
  _ | Just tele <- lenT (2^(n-1)-1) getLamTeleN t0, isRel tele -> 
    faceTele VLam i tele [] $ \xs ->
    VLam (face i t0 `apps` xs) $ \xi ->
    paramTele n VLam i tele xs $ \b ->
    paramT n i b xi
  _ | isType t0 -> typ -- ??? Is this redundant ???
  _ -> stop
 where stop = VParam n i t0
       typ = VLam (face i t0) $ \x -> extT t0 x
       ext = param n i
       extT = paramT n i

isType :: Val -> Bool
isType t = case t of
  VLam _ _ -> False
  VSPair _ _ -> False
  Ter (Sum _ _) _ -> True
  VPi _ _ -> True
  VSigma _ _ -> True
  VU -> True
  _ -> isVU (neuTyp t)

neuTyp :: Val -> Val
neuTyp v0 = case v0 of
   VVar _ ty -> ty
   VCPair _ _ _ t -> t
   VParam n i t -> paramT n i (neuTyp t) (face i t)
   VApp n u -> case neuTyp n of
     VPi _ b -> b `app` u
     _ -> error "neuTyp: panic"
   VFst n -> case neuTyp n of
     VSigma a _ -> a
     _ -> error "neuTyp: VFst: panic"
   VSnd n -> case neuTyp n of
     VSigma _ b -> b `app` fstSVal n
     _ -> error "neuTyp: VSnd: panic"


-- FIXME: VCPair of a vcon must reduce.: (Cons x xs, (xi, xsi))  ---> Cons (x,xi) (xs,xsi)

app :: Val -> Val -> Val
app (VApp (VParam 1 i f@(Ter _ _)) a) ai = VParam 1 i (f `app` (VCPair i a ai arg))
  where VPi arg _ = neuTyp f
-- FIXME. This is useful, for example, if f is a split (or param of split...). But currently we are restricted to n=1 (also to just Ter for bad reasons)!
app (VCPair i f g (VPi _a b)) u = VCPair i (app f (face i u)) ((g `app` (face i u)) `app` param 1 i u) (b `app` u)
app (VLam _ f) u = f u
app (Ter (Split _ nvs) e) (VCon name us) = case lookup name nvs of
    Just (xs,t) -> eval (upds e (zip xs us)) t
    Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name
app u@(Ter (Split _ _) _) v | isNeutral v = VSplit u v -- v should be neutral
                            | otherwise   = error $ "app: VSplit " ++ show v
                                                   ++ " is not neutral"
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
conv k (VParam n i u) (VParam m j v) = n == m && conv k u (swap v (i,j))
conv k _              _            = False

convEnv :: Int -> Env -> Env -> Bool
convEnv k e e' = and $ zipWith (conv k) (valOfEnv e) (valOfEnv e')
