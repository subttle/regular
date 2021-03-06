{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveTraversable  #-}

module NatBase where

import           Control.Applicative (Alternative (..), Applicative (..))
import           Control.Selective (Selective (..), selectA)
import           Control.Monad.Fix (MonadFix (..))
import           Data.Function (on, (&))
import           Data.Functor.Contravariant (Contravariant (..), Predicate (..), Op (..))
import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE (reverse)
import           GHC.Real (reduce)
import           Numeric.Natural (Natural)
import           Prelude hiding (even, odd)
import           Common ((‥), (⋄), liftA4, ordering, quoteWith)

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

instance (Show a) ⇒ Show (NatF a) where
  show ∷ NatF a → String
  show = natf "ZeroF" (quoteWith "(SuccF " ")" . show)

instance Applicative NatF where
  pure ∷ a → NatF a
  pure = SuccF
  (<*>) ∷ NatF (a → b) → NatF a → NatF b
  (<*>) = natf (const ZeroF) fmap

instance Alternative NatF where
  empty ∷ NatF a
  empty = ZeroF
  (<|>) ∷ NatF a → NatF a → NatF a
  (<|>) = natf id (const id)

instance Selective NatF where
  select ∷ NatF (Either a b) → NatF (a → b) → NatF b
  select = selectA

instance Monad NatF where
  (>>=) ∷ NatF a → (a → NatF b) → NatF b
  (>>=) = natf (const ZeroF) (&)

instance MonadFix NatF where
  mfix ∷ ∀ a . (a → NatF a) → NatF a
  mfix f = f a
    where
      a ∷ a
      a = unfix (f a)
        where
          unfix ∷ NatF a → a
          unfix (SuccF a') = a'
          unfix ZeroF      = undefined

-- case analysis
nat ∷ a → (a → a) → ℕ → a
nat z _ Zero     = z
nat z s (Succ n) = s (nat z s n)

-- N.B. `maybe ∷ b → (a → b) → Maybe a → b`
natf ∷           b
     → (     a → b)
     → (NatF a → b)
natf z _ ZeroF     = z
natf _ s (SuccF a) = s a

unfoldn ∷ ∀ a b
        . (b → NatF (a, b))
        → (b →      [a]   )
unfoldn h = getOp (contramap h c)
  where
    c ∷ Op [a] (NatF (a, b))
    c = Op (natf [] (\(a, b) → a : unfoldn h b))

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
  fromInteger = liftA4 ordering (Succ . fromInteger . pred) (const Zero) (error "fromInteger") (compare 0)
  negate ∷ ℕ → ℕ
  negate = error "negate"
  (-) ∷ ℕ → ℕ → ℕ
  (-) = fromIntegral ‥ ((-) `on` toInteger)

instance Real ℕ where
  toRational ∷ ℕ → Rational
  toRational = (flip reduce `on` toInteger) (Succ Zero)

instance Integral ℕ where
  quotRem ∷ ℕ → ℕ → (ℕ, ℕ)
  quotRem = undefined -- FIXME implement
  toInteger ∷ ℕ → Integer
  toInteger = nat 0 succ

instance Semigroup ℕ where
  (<>) ∷ ℕ → ℕ → ℕ
  (<>) = (+)
instance Monoid ℕ where
  mempty ∷ ℕ
  mempty = Zero

instance Show ℕ where
  show ∷ ℕ → String
  show = show . toNatural

-- N.B. this is not a bijection!
instance Enum ℕ where
  toEnum ∷ Int → ℕ
  toEnum = liftA4 ordering (Succ . toEnum . pred) (const Zero) (error "toEnum") (compare 0)
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

positive ∷ Predicate ℕ
-- positive = Predicate (nat False (const True))
positive = Predicate (> 0)

-- TODO
brgc ∷ ℕ → NonEmpty [Bool]
brgc = nat (pure mempty) (liftA2 (⋄) (fmap (False :)) (fmap (True :) . NE.reverse))

-- c.f. `replicateM`
replicateA ∷ (Applicative f) ⇒ ℕ → f a → f [a]
replicateA = nat (const (pure mempty)) ((<*>) (liftA2 (:)))
