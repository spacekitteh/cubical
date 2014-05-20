module CTT where

import Control.Monad
import Data.List

import Pretty

--------------------------------------------------------------------------------
-- | Terms

data Loc = Loc { locFile :: String
               , locPos :: (Int, Int) }
  deriving Eq

type Ident  = String
type Label  = String
type Binder = (Ident,Loc)

noLoc :: String -> Binder
noLoc x = (x, Loc "" (0,0))

-- Branch of the form: c x1 .. xn -> e
type Brc    = (Label,([Binder],Ter))

-- Telescope (x1 : A1) .. (xn : An)
type Tele   = [(Binder,Ter)]

-- Labelled sum: c (x1 : A1) .. (xn : An)
type LblSum = [(Binder,Tele)]

-- Context gives type values to identifiers
type Ctxt   = [(Binder,Val)]

-- Mutual recursive definitions: (x1 : A1) .. (xn : An) and x1 = e1 .. xn = en
type Decls  = [(Binder,Ter,Ter)]

declIdents :: Decls -> [Ident]
declIdents decl = [ x | ((x,_),_,_) <- decl]

declBinders :: Decls -> [Binder]
declBinders decl = [ x | (x,_,_) <- decl]

declTers :: Decls -> [Ter]
declTers decl = [ d | (_,_,d) <- decl]

declTele :: Decls -> Tele
declTele decl = [ (x,t) | (x,t,_) <- decl]

declDefs :: Decls -> [(Binder,Ter)]
declDefs decl = [ (x,d) | (x,_,d) <- decl]

-- Terms
data Ter = App Ter Ter
         | Pi Ter Ter
         | Lam Binder Ter
         | Sigma Ter Ter
         | SPair Ter Ter
         | Fst Ter
         | Snd Ter
         | Where Ter Decls
         | Var Ident
         | U
         -- constructor c Ms
         | Con Label [Ter]
         -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Split Loc [Brc]
         -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | Sum Binder LblSum
         | Undef Loc
         | NamedPair Name Ter Ter
         | NamedSnd Name Ter
  deriving Eq

-- For an expression t, returns (u,ts) where u is no application
-- and t = u t
unApps :: Ter -> (Ter,[Ter])
unApps = aux []
  where aux :: [Ter] -> Ter -> (Ter,[Ter])
        aux acc (App r s) = aux (s:acc) r
        aux acc t         = (t,acc)
-- Non tail reccursive version:
-- unApps (App r s) = let (t,ts) = unApps r in (t, ts ++ [s])
-- unApps t         = (t,[])

mkApps :: Ter -> [Ter] -> Ter
mkApps (Con l us) vs = Con l (us ++ vs)
mkApps t ts          = foldl App t ts

mkLams :: [String] -> Ter -> Ter
mkLams bs t = foldr Lam t [noLoc b | b <- bs]

mkWheres :: [Decls] -> Ter -> Ter
mkWheres []     e = e
mkWheres (d:ds) e = Where (mkWheres ds e) d

--------------------------------------------------------------------------------
-- | Names, dimension

newtype Name = N String
  deriving (Eq,Ord)

instance Show Name where
  show (N s) = s

allStrings :: [String]
allStrings = [] : [x:s | s <- allStrings, x <- ['a'..'z']]

allSyms :: [Name]
allSyms = tail $ map N allStrings

gensym :: [Name] -> Name
gensym xs = head $ gensyms xs

gensyms :: [Name] -> [Name]
gensyms d = allSyms \\ d

-- class Nominal a where
-- --  swap :: a -> Name -> Name -> a
--   support :: a -> [Name]

-- fresh :: Nominal a => a -> Name
-- fresh = gensym . support

-- freshs :: Nominal a => a -> [Name]
-- freshs = gensyms . support

-- instance (Nominal a, Nominal b) => Nominal (a, b) where
--   support (a, b)  = support a `union` support b
-- --  swap (a, b) x y = (swap a x y, swap b x y)

-- instance (Nominal a) => Nominal (Maybe a) where
--   support (Just x) = support x
--   support Nothing  = []

-- instance Nominal a => Nominal [a]  where
--   support vs  = unions (map support vs)
-- --  swap vs x y = [swap v x y | v <- vs]

-- -- Make Name an instance of Nominal
-- instance Nominal Name where
--   support n = [n]

--   -- swap z x y | z == x    = y
--   --            | z == y    = x
--   --            | otherwise = z

--------------------------------------------------------------------------------
-- | Values

data Val = VU
         | Ter Ter Morphism Env
         | VPi Val Val
         | VId Val Val Val
         | VSigma Val Val
         | VSPair Val Val
         | VCon Ident [Val]
         | VNSPair Name Val Val
         | VNSnd Name Val
         | VApp Val Val            -- the first Val must be neutral
         | VSplit Val Val          -- the second Val must be neutral
         | VVar String Dim
         | VFst Val
         | VSnd Val
  deriving Eq

mkVar :: Int -> [Name] -> Val
mkVar k f = VVar ('X' : show k) (map Just f)

isNeutral :: Val -> Bool
isNeutral (VApp u _)   = isNeutral u
isNeutral (VSplit _ v) = isNeutral v
isNeutral (VVar _ _)   = True
isNeutral (VFst v)     = isNeutral v
isNeutral (VSnd v)     = isNeutral v
isNeutral (VNSnd _i v) = isNeutral v
isNeutral _            = False

-- unions :: Eq a => [[a]] -> [a]
-- unions = foldr union []

-- instance Nominal Val where
--   support VU            = []
--   support (Ter _ _ e)   = support e
--   support (VId a v0 v1) = support [a,v0,v1]
--   support (VPi v1 v2)   = support [v1,v2]
--   support (VCon _ vs)   = support vs
--   support (VApp u v)    = support (u, v)
--   support (VSplit u v)  = support (u, v)
--   support (VVar x d)    = support d
--   support (VSigma u v)  = support (u,v)
--   support (VSPair u v)  = support (u,v)
--   support (VFst u)      = support u
--   support (VSnd u)      = support u
--   support (VNSnd i u)   = delete i $ support u
--   support (VNSPair i u v) = i : support (u,v)

--  support v                    = error ("support " ++ show v)

  -- swap u x y =
  --   let sw u = swap u x y in case u of
  --   VU          -> VU
  --   Ter t f e     -> Ter t f (swap e x y)
  --   VId a v0 v1 -> VId (sw a) (sw v0) (sw v1)
  --   VPi a f     -> VPi (sw a) (sw f)
  --   VCon c us   -> VCon c (map sw us)
  --   VApp u v    -> VApp (sw u) (sw v)
  --   VSplit u v  -> VSplit (sw u) (sw v)
  --   VVar s d    -> VVar s (swap d x y)
  --   VSigma u v  -> VSigma (sw u) (sw v)
  --   VSPair u v  -> VSPair (sw u) (sw v)
  --   VFst u      -> VFst (sw u)
  --   VSnd u      -> VSnd (sw u)

--------------------------------------------------------------------------------
-- | Environments

data Env = Empty
         | Pair Env (Binder,Val)
         | PDef [(Binder,Ter)] Env
  deriving Eq

instance Show Env where
  show Empty            = ""
  show (PDef xas env)   = show env
  show (Pair env (x,u)) = parens $ showEnv1 env ++ show u
    where
      showEnv1 (Pair env (x,u)) = showEnv1 env ++ show u ++ ", "
      showEnv1 e                = show e

-- instance Nominal Env where
--   -- swap e x y = mapEnv (\u -> swap u x y) e

--   support Empty          = []
--   support (Pair e (_,v)) = support (e, v)
--   support (PDef _ e)     = support e

upds :: Env -> [(Binder,Val)] -> Env
upds = foldl Pair

lookupIdent :: Ident -> [(Binder,a)] -> Maybe (Binder, a)
lookupIdent x defs = lookup x [(y,((y,l),t)) | ((y,l),t) <- defs]

getIdent :: Ident -> [(Binder,a)] -> Maybe a
getIdent x defs = do (_,t) <- lookupIdent x defs; return t

getBinder :: Ident -> [(Binder,a)] -> Maybe Binder
getBinder x defs = do (b,_) <- lookupIdent x defs; return b

mapEnv :: (Val -> Val) -> Env -> Env
mapEnv _ Empty          = Empty
mapEnv f (Pair e (x,v)) = Pair (mapEnv f e) (x,f v)
mapEnv f (PDef ts e)    = PDef ts (mapEnv f e)

valOfEnv :: Env -> [Val]
valOfEnv Empty            = []
valOfEnv (Pair env (_,v)) = v : valOfEnv env
valOfEnv (PDef _ env)     = valOfEnv env

--------------------------------------------------------------------------------
-- | Morphisms

type EName = Maybe Name
type Dim   = [EName]

data Morphism = Morphism
  { domain     :: [Name]
  , codomain   :: [Name]
  , appMorName :: Name -> EName }
-- JP: Do we have codomain == catMaybes $ map appMorName domain?

normalizedDomain = nub . sort . domain

instance Eq Morphism where
  f == g = normalizedDomain f == normalizedDomain g
         && all (\x -> appMorName f x == appMorName g x) (domain f)

showEName :: EName -> String
showEName Nothing  = "0"
showEName (Just x) = show x

instance Show Morphism where
  show f = ccat [ show x ++ " -> " ++ showEName (appMorName f x)
                | x <- domain f, appMorName f x /= Just x ]

-- Identity morphism
idMor :: [Name] -> Morphism
idMor domain = Morphism domain domain Just

-- Composition in diagramatic order (g after f)
compMor :: Morphism -> Morphism -> Morphism
compMor f g
  | codomain f == domain g =
    Morphism (domain f) (codomain g)
             (appMorName g <=< appMorName f)
  | otherwise = error "compMor: 'codomain f' and 'domain g' do not match"

-- face morphism, @i@ should be in the domain
faceMor :: [Name] -> Name -> Morphism
faceMor domain i
  | i `elem` domain =
     Morphism domain (i `delete` domain)
       (\j -> if i == j then Nothing else Just j)
  | otherwise       = error $ "faceMor: " ++ show i ++ " not in domain"

-- f : I,i -> J,f(i)
-- f - i : I -> J
minusMor :: Name -> Morphism -> Morphism
minusMor i (Morphism dom codom f) = case f i of
  Just j -> Morphism (i `delete` dom) (j `delete` codom) f
  Nothing -> Morphism (i `delete` dom) codom f

-- f : I -> J and i fresh for I
-- returns (f,(i=j)) : I,i -> J,j
-- Also return j
updateMor :: Name -> Morphism -> (Name,Morphism)
updateMor i (Morphism dom codom f)
  | i `elem` dom = error "updateMor"
  | otherwise =
    let fi = gensym codom
    in (fi,Morphism (i : dom) (fi : codom) (
               \j -> if i == j then Just fi else f j))

swapMor :: [Name] -> Name -> Name -> Morphism
swapMor domain i j =
  Morphism (i:domain) (j:domain) (\x -> Just (if x == i then j else x))

--------------------------------------------------------------------------------
-- | Pretty printing

instance Show Loc where
  show (Loc name (i,j)) = name ++ "_L" ++ show i ++ "_C" ++ show j

instance Show Ter where
  show = showTer

showTer :: Ter -> String
showTer U                   = "U"
showTer (App e0 e1)         = showTer e0 <+> showTer1 e1
showTer (Pi e0 e1)          = "Pi" <+> showTers [e0,e1]
showTer (Lam (x,_) e)       = '\\' : x <+> "->" <+> showTer e
showTer (Fst e)             = showTer e ++ ".1"
showTer (Snd e)             = showTer e ++ ".2"
showTer (Sigma e0 e1)       = "Sigma" <+> showTers [e0,e1]
showTer (SPair e0 e1)       = "pair" <+> showTers [e0,e1]
showTer (Where e d)         = showTer e <+> "where" <+> showDecls d
showTer (Var x)             = x
showTer (Con c es)          = c <+> showTers es
showTer (Split l _)         = "split " ++ show l
showTer (Sum l _)           = "sum " ++ show l
showTer (Undef _)           = "undefined"
showTer (NamedSnd i e)      = showTer1 e ++ "." ++ show i
showTer (NamedPair i e0 e1) = ("Cpair " ++ show i) <+> showTers [e0,e1]

showTers :: [Ter] -> String
showTers = hcat . map showTer1

showTer1 :: Ter -> String
showTer1 U           = "U"
showTer1 (Con c [])  = c
showTer1 (Var x)     = x
showTer1 u@(Split{}) = showTer u
showTer1 u@(Sum{})   = showTer u
showTer1 u           = parens $ showTer u

showDecls :: Decls -> String
showDecls defs = ccat (map (\((x,_),_,d) -> x <+> "=" <+> show d) defs)

instance Show Val where
  show = showVal

showVal :: Val -> String
showVal VU              = "U"
showVal (Ter t f env)   = show t <+> show env
showVal (VId a u v)     = "Id" <+> showVal1 a <+> showVal1 u <+> showVal1 v
showVal (VCon c us)     = c <+> showVals us
showVal (VPi a f)       = "Pi" <+> showVals [a,f]
showVal (VApp u v)      = showVal u <+> showVal1 v
showVal (VSplit u v)    = showVal u <+> showVal1 v
showVal (VVar x d)      = x <+> showDim d
showVal (VSPair u v)    = "pair" <+> showVals [u,v]
showVal (VSigma u v)    = "Sigma" <+> showVals [u,v]
showVal (VFst u)        = showVal u ++ ".1"
showVal (VSnd u)        = showVal u ++ ".2"
showVal (VNSnd i u)     = showVal u ++ "." ++ show i
showVal (VNSPair i u v) = "Cpair" ++ show i  <+> showVals [u,v]

showDim :: Show a => [a] -> String
showDim = parens . ccat . map show

showVals :: [Val] -> String
showVals = hcat . map showVal1

showVal1 :: Val -> String
showVal1 VU          = "U"
showVal1 (VCon c []) = c
showVal1 u@(VVar{})  = showVal u
showVal1 u           = parens $ showVal u
