{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module NatBase where

import           Data.Function (on)
import           Numeric.Natural (Natural)
import           Data.Functor.Contravariant (Predicate (..))
import           Prelude hiding (even, odd)

-- N.B. this entire file is currently experimental/untested/WIP!

data ℕ where
  Zero ∷     ℕ
  Succ ∷ ℕ → ℕ

-- essentially a newtype of `Maybe`
data NatF a where
  ZeroF ∷     NatF a
  SuccF ∷ a → NatF a
deriving instance Functor     NatF
deriving instance Foldable    NatF
deriving instance Traversable NatF

-- case analysis
nat ∷ a → (a → a) → ℕ → a
nat z _ Zero     = z
nat z s (Succ n) = s (nat z s n)

-- N.B. `maybe ∷ b → (a → b) → Maybe a → b`
natf ∷ b → (a → b) → NatF a → b
natf z _ ZeroF     = z
natf _ s (SuccF a) = s a

toNatural ∷ ℕ → Natural
toNatural = nat 0 succ

instance Num ℕ where
  (+) ∷ ℕ → ℕ → ℕ
  (+) = flip nat succ
  (*) ∷ ℕ → ℕ → ℕ
  (*) = nat Zero . (+)
  abs ∷ ℕ → ℕ
  abs = id
  signum ∷ ℕ → ℕ
  signum = nat Zero (const (Succ Zero))
  fromInteger ∷ Integer → ℕ
  fromInteger i | i == 0 = Zero
                | i >  0 = Succ (fromInteger (i - 1))
                | i <  0 = error "fromInteger"
  negate ∷ ℕ → ℕ
  negate = error "negate"
  (-) ∷ ℕ → ℕ → ℕ
  (-) = undefined -- FIXME implement

instance Semigroup ℕ where
  (<>) ∷ ℕ → ℕ → ℕ
  (<>) = (+)
instance Monoid ℕ where
  mempty ∷ ℕ
  mempty  = Zero

instance Show ℕ where
  show ∷ ℕ → String
  show = show . toNatural

-- N.B. this is not a bijection!
instance Enum ℕ where
  toEnum ∷ Int → ℕ
  toEnum i | i == 0 = Zero
           | i >  0 = Succ (toEnum (i - 1))
           | i <  0 = error "toEnum"
  fromEnum ∷ ℕ → Int
  fromEnum = nat 0 succ
  succ ∷ ℕ → ℕ
  succ = Succ
  pred ∷ ℕ → ℕ
  pred  Zero    = error "pred"
  pred (Succ n) = n
instance Eq ℕ where
  (==) ∷ ℕ → ℕ → Bool
  (==) = (==) `on` toNatural
instance Ord ℕ where
  compare ∷ ℕ → ℕ → Ordering
  compare = compare `on` toNatural

even ∷ Predicate ℕ
even = Predicate (nat True not)

odd ∷ Predicate ℕ
odd = Predicate (nat False not)
