{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveTraversable  #-}

module NatPBase where

import           Data.Function (on)
import           Data.Functor.Contravariant (Predicate (..))
import           Numeric.Natural (Natural)
import           Prelude hiding (even, odd)
import           Common (ordering)


-- N.B. this entire file is currently experimental/untested/WIP!

-- TODO ideally can just reuse most of src/NatBase.hs but going to want to check edge cases


-- Ideally would name this type `ℕ⁺`, to represent ℕ \ {0}, but the GHC doesn't like that
data ℕ¹ where
  One ∷      ℕ¹
  Suc ∷ ℕ¹ → ℕ¹

type Natural1 = ℕ¹

-- case analysis
nat1 ∷ a → (a → a) → ℕ¹ → a
nat1 o _ One     = o
nat1 o s (Suc n) = s (nat1 o s n)

data Nat1F a where
  OneF ∷     Nat1F a
  SucF ∷ a → Nat1F a
deriving instance Functor     Nat1F
deriving instance Foldable    Nat1F
deriving instance Traversable Nat1F

toNatural ∷ ℕ¹ → Natural
toNatural = nat1 1 succ

-- FIXME TODO
instance Num ℕ¹ where
  -- FIXME add tests
  (+) ∷ ℕ¹ → ℕ¹ → ℕ¹
  (+) = flip nat1 Suc . Suc
  (*) ∷ ℕ¹ → ℕ¹ → ℕ¹
  (*) = nat1 id ((=<<) (+))
  abs ∷ ℕ¹ → ℕ¹
  -- abs    = nat1 One Suc
  abs = id
  -- FIXME TODO
  fromInteger ∷ Integer → ℕ¹
  fromInteger i = ordering (error "fromInteger") One (Suc (fromInteger (pred i))) (compare i 1)
  signum ∷ ℕ¹ → ℕ¹
  -- signum = nat1 One (const One)
  signum =              const One
  negate ∷ ℕ¹ → ℕ¹
  negate = error "negate"

instance Semigroup ℕ¹ where
  (<>) ∷ ℕ¹ → ℕ¹ → ℕ¹
  (<>) = (*)
instance Monoid ℕ¹ where
  mempty ∷ ℕ¹
  mempty = One

instance Show ℕ¹ where
  show ∷ ℕ¹ → String
  show = show . toNatural

-- N.B. this is not a bijection!
instance Enum ℕ¹ where
  toEnum ∷ Int → ℕ¹
  toEnum i | i == 1 = One
           | i >  1 = Suc (toEnum (i - 1))
           | i <  1 = error "toEnum"
  fromEnum ∷ ℕ¹ → Int
  fromEnum = nat1 1 succ
  succ ∷ ℕ¹ → ℕ¹
  succ = Suc
  pred ∷ ℕ¹ → ℕ¹
  pred  One    = error "pred"
  pred (Suc n) = n
instance Eq ℕ¹ where
  (==) ∷ ℕ¹ → ℕ¹ → Bool
  (==) = (==) `on` toNatural
instance Ord ℕ¹ where
  compare ∷ ℕ¹ → ℕ¹ → Ordering
  compare = compare `on` toNatural

even ∷ Predicate ℕ¹
even = Predicate (nat1 False not)

odd ∷ Predicate ℕ¹
odd = Predicate (nat1 True not)

positive ∷ Predicate ℕ¹
-- positive = Predicate (nat1 True (const True))
positive = Predicate (const True)
