{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, OverlappingInstances #-}
module CTT where

import Control.Applicative
import Data.List
import Data.Maybe
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
type Brc     = (Label,([Binder],Ter))
type VBrc    = (Label,([Binder],Val))

-- Telescope (x1 : A1) .. (xn : An)
type Tele   = [(Binder,Ter)]
data VTele  = VNil | VCons Val (Val -> VTele)

mkTele k VNil = []
mkTele k (VCons ty tele) = v : mkTele (k+1) (tele v)
  where v = mkVar k ty

-- Labelled sum: c (x1 : A1) .. (xn : An)
type LblSum  = [(Binder,Tele)]
type VLblSum = [(Binder,VTele)]

-- Context gives type values to identifiers
type Ctxt   = [(Binder,Val)]

-- Mutual recursive definitions: (x1 : A1) .. (xn : An) and x1 = e1 .. xn = en
type Decls  = [(Binder,Ter,Ter)]

declIdents :: Decls -> [Ident]
declIdents decl = [ x | ((x,_),_,_) <- decl]

declTers :: Decls -> [Ter]
declTers decl = [ d | (_,_,d) <- decl]

declTele :: Decls -> Tele
declTele decl = [ (x,t) | (x,t,_) <- decl]

declDefs :: Decls -> [(Binder,Ter)]
declDefs decl = [ (x,d) | (x,_,d) <- decl]


gensym :: [Color] -> Color
gensym xs = head $ (map show [0..]) \\ xs

gensyms :: [Color] -> [Color]
gensyms d = let x = gensym d in x : gensyms (x : d)

class Nominal a where
  swap :: a -> (Color,Color) -> a
  support :: a -> [Color]

fresh :: Nominal a => a -> Color
fresh = gensym . support

freshs :: Nominal a => a -> [Color]
freshs = gensyms . support

type Color = String

instance Nominal Color where
  swap k (i,j) | k == i = j
               | k == j = i
               | otherwise = k

  support i = [i]

instance (Nominal a, Nominal b) => Nominal (a, b) where
  support (a, b) = support a `union` support b
  swap (a, b) xy = (swap a xy, swap b xy)

instance (Nominal a, Nominal b, Nominal c) => Nominal (a, b, c) where
  support (a, b,c) = support a `union` support b `union` support c
  swap (a, b,c) xy = (swap a xy, swap b xy,swap c xy)

instance Nominal a => Nominal [a] where
  support vs = foldr union [] (map support vs)
  swap vs xy = [swap v xy | v <- vs]

instance Nominal a => Nominal (Maybe a) where
  support = maybe [] support
  swap v xy = fmap (\u -> swap u xy) v

-- Terms
data Ter = App Ter Ter
         | Pi Ter Ter
         | Lam Binder Ter Ter -- TODO: The type is not needed here
         | Sigma Ter Ter
         | SPair Ter Ter
         | Fst Ter
         | Snd Ter
         | Where Ter Decls
         | Var Ident
         | U
         | Param Color Ter
         -- constructor c Ms
         | Con Label [Ter]
         -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Split Loc [Brc]
         -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | Sum Binder LblSum
         | Undef Loc
  deriving Eq

mkApps :: Ter -> [Ter] -> Ter
mkApps (Con l us) vs = Con l (us ++ vs)
mkApps t ts          = foldl App t ts

-- mkLams :: [String] -> Ter -> Ter
-- mkLams bs t = foldr Lam t [ noLoc b | b <- bs ]

mkWheres :: [Decls] -> Ter -> Ter
mkWheres []     e = e
mkWheres (d:ds) e = Where (mkWheres ds e) d

--------------------------------------------------------------------------------
-- | Values

data Val = VU
         | VLam Val {- type -} (Val -> Val) -- Better name: Closure
         | VPi Val Val
         | VSigma Val Val
         | VSPair Val Val
         | VCon Ident [Val]
         | VApp Val Val            -- the first Val must be neutral
         | VSplit Val Val          -- the second Val must be neutral
         | VVar String Val {- type -}
         | VFst Val
         | VSnd Val
         | VCPair Color Val Val Val
         | VParam Color Val -- (Color -> Val)
         -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | VSum Binder VLblSum
  -- deriving Eq

mkVar :: Int -> Val -> Val
mkVar k ty = VVar ('X' : show k) ty

isNeutral :: Val -> Bool
isNeutral (VApp u _)   = isNeutral u
isNeutral (VSplit _ v) = isNeutral v
isNeutral (VVar _ _)   = True
isNeutral (VFst v)     = isNeutral v
isNeutral (VSnd v)     = isNeutral v
isNeutral _            = False

instance Nominal Val where
  support VU = []
  support (VLam t e) = support (t,e (VVar "fresh" t))
  support (VCPair i a b t) = support (i,[a,b,t])
  support (VParam x v) = delete x $ support v
  support (VPi v1 v2) = support [v1,v2]
  support (VCon _ vs) = support vs
  support (VApp u v) = support (u, v)
  support (VSplit u v) = support (u, v)
  support (VVar _ t) = support t
  support (VSigma u v) = support (u,v)
  support (VSPair u v) = support (u,v)
  support (VFst u) = support u
  support (VSnd u) = support u
  support v = error ("support " ++ show v)

  swap u ij =
    let sw u = swap u ij
    in case u of
      VU -> VU
      VLam t e -> VLam t (\x -> sw (e x))
      VPi a f -> VPi (sw a) (sw f)
      VParam k v -> VParam (sw k) (sw v)
      VCPair i a b t -> VCPair (sw i) (sw a) (sw b) (sw t)
      VSigma a f -> VSigma (sw a) (sw f)
      VSPair u v -> VSPair (sw u) (sw v)
      VFst u -> VFst (sw u)
      VSnd u -> VSnd (sw u)
      VCon c vs -> VCon c (sw vs)
      VVar x t -> VVar x (sw t)
      VApp u v -> VApp (sw u) (sw v)
      VSplit u v -> VSplit (sw u) (sw v)

--------------------------------------------------------------------------------
-- | Environments

data Env = Empty
         | Pair Env (Binder,Val)
         | PDef [(Binder,Ter)] Env
  -- deriving Eq

instance Show Env where
  show Empty            = ""
  show (PDef xas env)   = show env
  show (Pair env (x,u)) = parens $ showEnv1 env ++ show u
    where
      showEnv1 (Pair env (x,u)) = showEnv1 env ++ show u ++ ", "
      showEnv1 e                = show e

upds :: Env -> [(Binder,Val)] -> Env
upds = foldl Pair

lookupIdent :: Ident -> [(Binder,a)] -> Maybe (Binder, a)
lookupIdent x defs = lookup x [ (y,((y,l),t)) | ((y,l),t) <- defs]

getIdent :: Ident -> [(Binder,a)] -> Maybe a
getIdent x defs = snd <$> lookupIdent x defs

valOfEnv :: Env -> [Val]
valOfEnv Empty            = []
valOfEnv (Pair env (_,v)) = v : valOfEnv env
valOfEnv (PDef _ env)     = valOfEnv env

--------------------------------------------------------------------------------
-- | Pretty printing

instance Show Loc where
  show (Loc name (i,j)) = name ++ "_L" ++ show i ++ "_C" ++ show j

instance Show Ter where
  show = showTer

showTer :: Ter -> String
showTer U               = "U"
showTer (App e0 e1)     = showTer e0 <+> showTer1 e1
showTer (Pi e0 e1)      = "Pi" <+> showTers [e0,e1]
showTer (Lam (x,_) t e) = '\\' : x <+> ":" <+> showTer t <+> "->" <+> showTer e
showTer (Fst e)         = showTer e ++ ".1"
showTer (Snd e)         = showTer e ++ ".2"
showTer (Sigma e0 e1)   = "Sigma" <+> showTers [e0,e1]
showTer (SPair e0 e1)   = "pair" <+> showTers [e0,e1]
showTer (Where e d)     = showTer e <+> "where" <+> showDecls d
showTer (Var x)         = x
showTer (Con c es)      = c <+> showTers es
showTer (Split l _)     = "split " ++ show l
showTer (Sum l _)       = "sum " ++ show l
showTer (Undef _)       = "undefined"

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
showVal VU           = "U"
showVal (VLam t e)  = '\\' : showVal x <+> ":" <+> showVal t <+> "->" <+> showVal (e x)
  where x = VVar "fresh" t
showVal (VCon c us)  = c <+> showVals us
showVal (VPi a f)    = "Pi" <+> showVals [a,f]
showVal (VApp u v)   = showVal u <+> showVal1 v
showVal (VSplit u v) = showVal u <+> showVal1 v
showVal (VVar x _)     = x
showVal (VSPair u v) = "pair" <+> showVals [u,v]
showVal (VSigma u v) = "Sigma" <+> showVals [u,v]
showVal (VFst u)     = showVal u ++ ".1"
showVal (VSnd u)     = showVal u ++ ".2"

showDim :: Show a => [a] -> String
showDim = parens . ccat . map show

showVals :: [Val] -> String
showVals = hcat . map showVal1

showVal1 :: Val -> String
showVal1 VU          = "U"
showVal1 (VCon c []) = c
showVal1 u@(VVar{})  = showVal u
showVal1 u           = parens $ showVal u
