module Eval where

import Control.Monad
import Data.List
import Data.Maybe (fromMaybe)

import CTT

look :: Ident -> Morphism -> Env -> (Binder, Val)
look x f (Pair rho (n@(y,l),u))
  | x == y    = (n, u)
  | otherwise = look x f rho
look x f r@(PDef es r1) = case lookupIdent x es of
  Just (y,t)  -> (y,eval f r t)
  Nothing     -> look x f r1

eval :: Morphism -> Env -> Ter -> Val
eval f e U               = VU
eval f e (App r s)       = app (eval f e r) (eval f e s)
eval f e (Var i)         = snd (look i f e)
eval f e (Pi a b)        = VPi (eval f e a) (eval f e b)
eval f e (Lam x t)       = Ter (Lam x t) f e -- stop at lambdas
eval f e (Sigma a b)     = VSigma (eval f e a) (eval f e b)
eval f e (SPair a b)     = VSPair (eval f e a) (eval f e b)
eval f e (Fst a)         = fstSVal (eval f e a)
eval f e (Snd a)         = sndSVal (eval f e a)
eval f e (Where t decls) = eval f (PDef [ (x,y) | (x,_,y) <- decls ] e) t
eval f e (Con name ts)   = VCon name (map (eval f e) ts)
eval f e (Split pr alts) = Ter (Split pr alts) f e
eval f e (Sum pr ntss)   = Ter (Sum pr ntss) f e
eval f e (Undef _)       = error "undefined"

evals :: Morphism -> Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals f env bts = [ (b,eval f env t) | (b,t) <- bts ]

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
app r s | isNeutral r = VApp r s -- r should be neutral
        | otherwise   = error $ "app: VApp " ++ show r ++ " is not neutral"

appMorEnv :: Morphism -> Env -> Env
appMorEnv f = mapEnv (appMor f)

appMor :: Morphism -> Val -> Val
appMor g u = case u of
  VU         -> VU
  Ter t f e  -> Ter t (compMor f g) (appMorEnv g e)
  VPi a f    -> VPi (appMor g a) (appMor g f)
  VSigma a f -> VSigma (appMor g a) (appMor g f)
  VSPair a b -> VSPair (appMor g a) (appMor g b)
  VApp u v   -> app (appMor g u) (appMor g v)
  VSplit u v -> app (appMor g u) (appMor g v)
  VVar s d   -> VVar s (map (maybe Nothing (appMorName g)) d)
  VFst p     -> fstSVal (appMor g p)
  VSnd p     -> sndSVal (appMor g p)
  VNSnd y p  -> sndNSVal y (appMor g p)
  VNSPair i a b -> let g' = minusMor i g
                   in case appMorName g i of
    Just j  -> VNSPair j (appMor g' a) (appMor g' b)
    Nothing -> appMor g' a

sndNSVal :: Name -> Val -> Val
sndNSVal i (VNSPair j a b) | i == j   = b
sndNSVal i u | isNeutral u = VNSnd i u
             | otherwise   = error $ show u ++ " should be neutral"

fstSVal, sndSVal :: Val -> Val
fstSVal (VSPair a b)    = a
fstSVal u | isNeutral u = VFst u
          | otherwise   = error $ show u ++ " should be neutral"
sndSVal (VSPair a b)    = b
sndSVal u | isNeutral u = VSnd u
          | otherwise   = error $ show u ++ " should be neutral"

-- apps :: Val -> [Val] -> Eval Val
-- apps = foldM app

-- appName :: Val -> Name -> Eval Val
-- appName (Path x u) y | y `elem` [0,1] = u `face` (x,y)
-- appName p y          | y `elem` [0,1] = return $ VAppName p y
--                                         -- p has to be neutral
-- appName (Path x u) y | x == y             = return u
--                      | y `elem` support u = error ("appName " ++ "\nu = " ++
--                                                    show u ++ "\ny = " ++ show y)
--                      | otherwise          = return $ swap u x y
-- appName v y          = return $ VAppName v y

-- -- Compute the face of an environment
-- faceEnv :: OEnv -> Side -> Eval OEnv
-- faceEnv e xd = mapOEnvM (`face` xd) e

-- faceName :: Name -> Side -> Name
-- faceName 0 _                 = 0
-- faceName 1 _                 = 1
-- faceName x (y,d) | x == y    = d
--                  | otherwise = x

-- -- Compute the face of a value
-- face :: Val -> Side -> Eval Val
-- face u xdir@(x,dir) =
--   let fc v = v `face` xdir in case u of
--   VU          -> return VU
--   Ter t e -> do e' <- e `faceEnv` xdir
--                 eval e' t
--   VId a v0 v1 -> VId <$> fc a <*> fc v0 <*> fc v1
--   Path y v | x == y    -> return u
--            | otherwise -> Path y <$> fc v
--   -- VExt y b f g p | x == y && dir == down -> return f
--   --                | x == y && dir == up   -> return g
--   --                | otherwise             ->
--   --                  VExt y <$> fc b <*> fc f <*> fc g <*> fc p
--   VHExt y b f g p | x == y && dir == down -> return f
--                   | x == y && dir == up   -> return g
--                   | otherwise             ->
--                     VHExt y <$> fc b <*> fc f <*> fc g <*> fc p
--   VPi a f    -> VPi <$> fc a <*> fc f
--   VSigma a f -> VSigma <$> fc a <*> fc f
--   VSPair a b -> VSPair <$> fc a <*> fc b
--   VInh v     -> VInh <$> fc v
--   VInc v     -> VInc <$> fc v
--   VSquash y v0 v1 | x == y && dir == down -> return v0
--                   | x == y && dir == up   -> return v1
--                   | otherwise             -> VSquash y <$> fc v0 <*> fc v1
--   VCon c us -> VCon c <$> mapM fc us
--   VEquivEq y a b f s t | x == y && dir == down -> return a
--                        | x == y && dir == up   -> return b
--                        | otherwise             ->
--                          VEquivEq y <$> fc a <*> fc b <*> fc f <*> fc s <*> fc t
--   VPair y a v | x == y && dir == down -> return a
--               | x == y && dir == up   -> fc v
--               | otherwise             -> VPair y <$> fc a <*> fc v
--   VEquivSquare y z a s t | x == y                -> return a
--                          | x == z && dir == down -> return a
--                          | x == z && dir == up   -> do
--                            let idV = Ter (Lam (noLoc "x") (Var "x")) oEmpty
--                            return $ VEquivEq y a a idV s t
--                          | otherwise             ->
--                           VEquivSquare y z <$> fc a <*> fc s <*> fc t
--   VSquare y z v | x == y                -> fc v
--                 | x == z && dir == down -> fc v
--                 | x == z && dir == up   -> do
--                   v' <- fc v
--                   VPair y <$> v' `face` (y,down) <*> pure v'
--                 | otherwise             -> VSquare y z <$> fc v
--   Kan Fill a b@(Box dir' y v nvs)
--     | x /= y && x `notElem` nonPrincipal b -> fillM (fc a) (mapBoxM fc b)
--     | x `elem` nonPrincipal b              -> return $ lookBox (x,dir) b
--     | x == y && dir == mirror dir'         -> return v
--     | otherwise                            -> com a b
--   VFillN a b@(Box dir' y v nvs)
--     | x /= y && x `notElem` nonPrincipal b -> fillM (fc a) (mapBoxM fc b)
--     | x `elem` nonPrincipal b              -> return $ lookBox (x,dir) b
--     | x == y && dir == mirror dir'         -> return v
--     | otherwise                            -> com a b
--   Kan Com a b@(Box dir' y v nvs)
--     | x == y                     -> return u
--     | x `notElem` nonPrincipal b -> comM (fc a) (mapBoxM fc b)
--     | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
--   VComN a b@(Box dir' y v nvs)
--     | x == y                     -> return u
--     | x `notElem` nonPrincipal b -> comM (fc a) (mapBoxM fc b)
--     | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
--   VComp b@(Box dir' y _ _)
--     | x == y                     -> return u
--     | x `notElem` nonPrincipal b -> VComp <$> mapBoxM fc b
--     | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
--   VFill z b@(Box dir' y v nvs)
--     | x == z                               -> return u
--     | x /= y && x `notElem` nonPrincipal b -> VFill z <$> mapBoxM fc b
--     | (x,dir) `elem` defBox b              ->
--       lookBox (x,dir) <$> mapBoxM (`face` (z,down)) b
--     | x == y && dir == dir'                ->
--         VComp <$> mapBoxM (`face` (z,up)) b
--   VInhRec b p h a     -> join $ inhrec <$> fc b <*> fc p <*> fc h <*> fc a
--   VApp u v            -> appM (fc u) (fc v)
--   VAppName u n        -> do
--    trace ("face " ++ "\nxdir " ++ show xdir ++
--           "\nu " ++ show u ++ "\nn " ++ show n)
--    appNameM (fc u) (faceName n xdir)
--   VSplit u v          -> appM (fc u) (fc v)
--   VVar s d            -> return $ VVar s [ faceName n xdir | n <- d ]
--   VFst p              -> fstSVal <$> fc p
--   VSnd p              -> sndSVal <$> fc p
--   VCircle             -> return VCircle
--   VBase               -> return VBase
--   VLoop y | x == y    -> return VBase
--           | otherwise -> return $ VLoop y
--   VCircleRec f b l s  -> join $ circlerec <$> fc f <*> fc b <*> fc l <*> fc s
--   VI  -> return VI
--   VI0 -> return VI0
--   VI1 -> return VI1
--   VLine y
--     | x == y && dir == down -> return VI0
--     | x == y && dir == up   -> return VI1
--     | otherwise             -> return $ VLine y
--   VIntRec f s e l u -> join $ intrec <$> fc f <*> fc s <*> fc e <*> fc l <*> fc u



conv :: Int -> [Name] -> Val -> Val -> Bool
conv k xs VU VU                                  = True
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
