{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveTraversable  #-}

module NatPBase where

import           Control.Applicative (liftA2)
import           Data.Function (on)
import           Data.Functor.Contravariant (Predicate (..))
import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE (reverse)
import           GHC.Real (reduce)
import           Numeric.Natural (Natural)
import           Prelude hiding (even, odd)
import           Common ((‥), (⋄), (⊲), liftA4, ordering)


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
  (*) = nat1 id ((<*>) (+))
  abs ∷ ℕ¹ → ℕ¹
  -- abs    = nat1 One Suc
  abs = id
  fromInteger ∷ Integer → ℕ¹
  fromInteger = liftA4 ordering (Suc . fromInteger . pred) (const One) (error "fromInteger") (compare 1)
  signum ∷ ℕ¹ → ℕ¹
  -- signum = nat1 One (const One)
  signum =              const One
  negate ∷ ℕ¹ → ℕ¹
  negate = error "negate"
  (-) ∷ ℕ¹ → ℕ¹ → ℕ¹
  (-) = fromIntegral ‥ ((-) `on` toInteger)

instance Real ℕ¹ where
  toRational ∷ ℕ¹ → Rational
  toRational = (flip reduce `on` toInteger) One

instance Integral ℕ¹ where
  quotRem ∷ ℕ¹ → ℕ¹ → (ℕ¹, ℕ¹)
  quotRem = undefined -- FIXME implement
  toInteger ∷ ℕ¹ → Integer
  toInteger = nat1 1 succ

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
  toEnum = liftA4 ordering (Suc . toEnum . pred) (const One) (error "toEnum") (compare 0)
  fromEnum ∷ ℕ¹ → Int
  fromEnum = nat1 0 succ
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

-- Some call this "strictly positive" but I consider it just "positive".
positive ∷ Predicate ℕ¹
-- positive = Predicate (nat1 True (const True))
positive = Predicate (const True)

-- TODO
brgc1 ∷ ℕ¹ → NonEmpty (NonEmpty Bool)
brgc1 = nat1 (       (⋄) (pure (pure False)) (pure (pure True)             ))
             (liftA2 (⋄) (fmap ((⊲)  False)) (fmap ((⊲)  True) . NE.reverse))
