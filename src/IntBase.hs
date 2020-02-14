{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}

module IntBase where

import           Data.Functor.Foldable (Fix (..), Recursive, Corecursive, Base, project, embed)
import           Data.Function (on)
import           Data.Group (Group, invert)
import           Data.List.NonEmpty (NonEmpty, NonEmpty ((:|)), (<|))
import qualified Data.List.NonEmpty as NE
import           GHC.Real (reduce)

-- N.B. this entire file is currently experimental/untested/WIP!

data ℤ where
  Prev ∷ ℤ → ℤ
  Zero ∷     ℤ
  Next ∷ ℤ → ℤ

data IntegerF a where
  PrevF ∷ a → IntegerF a
  ZeroF ∷     IntegerF a
  NextF ∷ a → IntegerF a
deriving instance Functor  IntegerF
deriving instance Foldable IntegerF

-- case analysis
int ∷ (a → a) → a → (a → a) → ℤ → a
int prev z next (Prev i) = prev (int prev z next i)
int _    z _     Zero    = z
int prev z next (Next i) = next (int prev z next i)

intf ∷ (a → b) → b → (a → b) → IntegerF a → b
intf prev _ _    (PrevF a) = prev a
intf _    z _     ZeroF    = z
intf _    _ next (NextF a) = next a

instance Num ℤ where
  (+) ∷ ℤ → ℤ → ℤ
  (+)       x   Zero    =             x
  (+)  Zero          y  =                 y
  (+) (Next x) (Next y) = Next (Next (x + y))
  (+) (Prev x) (Prev y) = Prev (Prev (x + y))
  (+) (Next x) (Prev y) =             x + y
  (+) (Prev x) (Next y) =             x + y
  (*) ∷ ℤ → ℤ → ℤ
  (*)       _   Zero    = Zero
  (*)  Zero          _  = Zero
  (*) (Next x) (Next y) = Next (x * y + x + y) -- (x + 1) * (y + 1) = xy + x + y + 1
  (*) (Prev x) (Next y) = Prev (x * y + x - y) -- (x - 1) * (y + 1) = xy + x - y - 1
  (*) (Next x) (Prev y) = Prev (x * y - x + y) -- (x + 1) * (y - 1) = xy - x + y - 1
  (*) (Prev x) (Prev y) = Next (x * y - x - y) -- (x - 1) * (y - 1) = xy - x - y + 1
  (-) ∷ ℤ → ℤ → ℤ
  (-)       x   Zero    =             x
  (-)  Zero          y  =          negate y
  (-) (Next x) (Next y) =             x - y   -- (x + 1) - (y + 1) =  x - y       (monotonicity of addition)
  (-) (Prev x) (Prev y) =             x - y   -- (x - 1) - (y - 1) =  x - y       (monotonicity of subtraction)
  (-) (Next x) (Prev y) = Next (Next (x - y)) -- (x + 1) - (y - 1) = (x - y) + 2
  (-) (Prev x) (Next y) = Prev (Prev (x - y)) -- (x - 1) - (y + 1) = (x - y) - 2
  negate ∷ ℤ → ℤ
  negate = invert
  fromInteger ∷ Integer → ℤ
  fromInteger i | i < 0 = Prev (fromInteger (1 + i    ))
  fromInteger 0         = Zero
  fromInteger i | i > 0 = Next (fromInteger (    i - 1))
  abs ∷ ℤ → ℤ
  abs = undefined    -- FIXME implement
  signum ∷ ℤ → ℤ
  signum = undefined -- FIXME implement

instance Real ℤ where
  toRational ∷ ℤ → Rational
  toRational = (flip reduce `on` toInteger) (Next Zero)
instance Integral ℤ where
  toInteger ∷ ℤ → Integer
  toInteger = int pred 0 succ
  quotRem ∷ ℤ → ℤ → (ℤ, ℤ)
  quotRem = undefined -- FIXME implement

instance Semigroup ℤ where
  (<>) ∷ ℤ → ℤ → ℤ
  (<>) = (+)
instance Monoid ℤ where
  mempty  ∷ ℤ
  mempty  = Zero
  mappend ∷ ℤ → ℤ → ℤ
  mappend = (<>)
instance Group ℤ where
  invert ∷ ℤ → ℤ
  invert = int Next Zero Prev

instance Show ℤ where
  show ∷ ℤ → String
  show = show . toInteger

instance Eq ℤ where
  (==) ∷ ℤ → ℤ → Bool
  (==) = (==) `on` toInteger
instance Ord ℤ where
  compare ∷ ℤ → ℤ → Ordering
  compare = compare `on` toInteger
-- N.B. this is not a bijection!
instance Enum ℤ where
  toEnum ∷ Int → ℤ
  toEnum i | i <  0 = Prev (toEnum (i + 1))
           | i == 0 = Zero
           | i >  0 = Next (toEnum (i - 1))

  fromEnum ∷ ℤ → Int
  fromEnum = int pred 0 succ
  succ ∷ ℤ → ℤ
  succ = Next
  pred ∷ ℤ → ℤ
  pred = Prev

instance Recursive Integer where
  project ∷ Integer → Base Integer Integer
  project i | i <  0 = PrevF (1 + i    )
            | i == 0 = ZeroF
            | i >  0 = NextF (    i - 1)

instance Corecursive Integer where
  embed ∷ Base Integer Integer → Integer
  embed (PrevF i) =     i - 1
  embed  ZeroF    =     0
  embed (NextF i) = 1 + i

type instance Base Integer = IntegerF
-- type Integer' = Fix IntegerF


toOrderings ∷ ℤ → NonEmpty Ordering
toOrderings (Prev i) = LT <| toOrderings i
toOrderings Zero     = EQ :| []
toOrderings (Next i) = GT <| toOrderings i

toBits ∷ ℤ → [Bool]
toBits (Prev i) = False : toBits i
toBits Zero     = []
toBits (Next i) = True  : toBits i

-- TODO better name
toBits' ∷ ℤ → [Either ℤ ℤ]
toBits' (Prev i) = Right i : toBits' i
toBits' Zero     = []
toBits' (Next i) = Left  i : toBits' i

