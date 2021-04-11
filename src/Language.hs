{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE FlexibleInstances         #-}

module Language where

import           Data.Bool.Unicode ((∧), (∨))
import           Data.Foldable (toList)
import           Data.Foldable.Unicode ((∋))
import           Data.Function ((&))
import           Data.Functor.Contravariant (Contravariant (..), Predicate (..))
import           Data.List (inits, tails, genericLength)
import qualified Data.List.NonEmpty as NE
import           Numeric.Natural.Unicode (ℕ)
import           Common (list, partitions, (>&<), (‥))
import           Finite (Finite (..), Σ (..), restricted)

-- N.B. This is /not/ the type for regular languages (but I am adding it to help test some properties)
-- In Agda (with termination checking) this can be used as a type for decidable languages, and while this
-- is not necessarily the case in Haskell, it is assumed to be total in this library to represent decidable languages.

-- Language over Σ
type ℒ s = Predicate [s]

-- TODO I should experiment more because
-- TODO I bet it would be much cleaner for some parts to implement in terms of monoid instead of list

instance (Finite s) ⇒ Σ (ℒ s) s
instance (Finite s) ⇒ Σ ([s] → Bool) s

-- provided for convenience/clarity.
-- ℓ `accepts` w ≡ ℓ w
accepts ∷ ℒ s → [s] → Bool
accepts = getPredicate

-- iff ε ∈ ℒ
nullable ∷ ℒ s → Bool
nullable = flip accepts []

-- the language which accepts no strings
empty ∷ ℒ s
empty = Predicate (const False)

-- the language which accepts only the empty string
epsilon ∷ ℒ s
epsilon = Predicate null

-- the language which accepts only a single literal
-- want version of `null` for NE? `isSingleton`?
lit ∷ ∀ s . (Eq s) ⇒ s → ℒ s
lit σ = Predicate p
  where
    p ∷ [s] → Bool
    p [σ'] = σ == σ'
    p _    = False

-- TODO better name?
fromLang ∷ (Eq s) ⇒ [[s]] → ℒ s
fromLang = Predicate . (∋)

-- remove all strings in ℒ that are not of the specified length
-- e.g. {"", "a", "ab", "abc", "abcd"} `onlyLength` 3 = {"abc"}
-- TODO consider renaming `ofLength`? I like the exactness of `only`, however
onlyLength ∷ ℒ a → ℕ → ℒ a
-- onlyLength ℓ n = Predicate (\w → accepts ℓ w ∧ genericLength w == n)
onlyLength = Predicate ‥ (\ℓ n w → accepts ℓ w ∧ n == genericLength w)

complement ∷ ℒ s → ℒ s
-- complement = Predicate . (not ‥ getPredicate)
-- complement = Predicate . (not ‥ accepts)
complement (Predicate ℓ) = Predicate (not . ℓ)

reversed ∷ ℒ s → ℒ s
reversed = contramap reverse

union ∷ ℒ s → ℒ s → ℒ s
union        (Predicate ℓ₁) (Predicate ℓ₂) = Predicate (\w → ℓ₁ w ∨ ℓ₂ w)

intersection ∷ ℒ s → ℒ s → ℒ s
intersection (Predicate ℓ₁) (Predicate ℓ₂) = Predicate (\w → ℓ₁ w ∧ ℓ₂ w)
-- intersection = Predicate ‥ (\ℓ₁ ℓ₂ w → accepts ℓ₁ w ∧ accepts ℓ₂ w)
-- intersection = Predicate ‥ (\ℓ₁ ℓ₂ → liftA2 (∧) (accepts ℓ₁) (accepts ℓ₂))
-- intersection = Predicate ‥ (\ℓ₁ ℓ₂ → (∧) <$> accepts ℓ₁ <*> accepts ℓ₂)
-- intersection = Predicate ‥ (\ℓ₁ ℓ₂ → (∧) <$> accepts ℓ₁ <*> accepts ℓ₂)
-- intersection = (<>) -- :P

concatenate ∷ ℒ s → ℒ s → ℒ s
concatenate  (Predicate ℓ₁) (Predicate ℓ₂) = Predicate (\w → any (\(w₁ , w₂) → ℓ₁ w₁ ∧ ℓ₂ w₂) (zip (inits w) (tails w)))

-- Kleene star
star ∷ ∀ s . ℒ s → ℒ s
star = Predicate . (\ℓ → list True (any (all (accepts ℓ . toList)) ‥ (partitions ‥ (:))))

-- inverse homomorphism
invhom ∷ ([s] → [g]) → ℒ g → ℒ s
invhom = contramap

-- inverse homomorphic image of ℓ under h
invhomimage ∷ (s → [g]) → ℒ g → ℒ s
invhomimage = contramap . concatMap

-- ε-free inverse homomorphic image of ℓ under h
invhomimageEpsFree ∷ (s → NE.NonEmpty g) → ℒ g → ℒ s
invhomimageEpsFree h = invhomimage (toList . h)

invhomimagew ∷ (Eq g) ⇒ (s → [g]) → [g] → ℒ s
-- invhomimagew = Predicate ‥ (\h w₁ w₂ → w₁ == concatMap h w₂)
invhomimagew h w = Predicate ((w ==) . concatMap h)

-- TODO leaving in refactor as comments for now, will delete later

-- derivative with respect to some symbol in Σ
derivative ∷ ℒ s → s → ℒ s
-- derivative (Predicate ℓ) a = Predicate (\w → ℓ (a : w))
-- derivative (Predicate ℓ) a = Predicate (\w → ℓ ((:) a w))
-- derivative (Predicate ℓ) a = Predicate (ℓ . ((:) a))
-- derivative (Predicate ℓ) a = Predicate (ℓ . (:) a)
-- derivative (Predicate ℓ) = Predicate . (ℓ ‥ (:))
--
-- derivative p s = contramap (s :) p
-- derivative = flip (contramap . (:))
-- derivative p s = (>&<) p (s :)
-- derivative p s = (>&<) p ((:) s)
-- derivative p = (>&<) p . (:)
derivative = (. (:)) . (>&<)

-- derivative with respect to some word ∈ Σ★
derivative' ∷ ℒ s → [s] → ℒ s
-- derivative' (Predicate ℓ) w₁ = Predicate (\w₂ → ℓ (w₁ ++ w₂))
-- derivative' (Predicate ℓ) = Predicate . (ℓ ‥ (++))
-- derivative' = Predicate ‥ (\ℓ w₁ w₂ → accepts ℓ (w₁ ++ w₂))
-- derivative' = Predicate ‥ (\ℓ → accepts ℓ ‥ (++))
--
-- derivative' p w = contramap (w ++) p
-- derivative' = flip (contramap . (++))
derivative' = (. (++)) . (>&<)

-- FIXME untested, need to check
antiderivative' ∷ ℒ s → [s] → ℒ s
-- antiderivative' l w = contramap (w ++) (reversed l)
-- antiderivative' = flip (contramap . (++)) . reversed
-- antiderivative' l w = (>&<) (reversed l) (w ++)
-- antiderivative' l w = (>&<) (reversed l) ((++) w)
-- antiderivative' l = (>&<) (reversed l) . (++)
antiderivative' = (. (++)) . (>&<) . reversed

-- TODO experimental, probably has a more meaningful name too
drop₁ ∷ ℒ s → ℒ s
drop₁ = contramap (drop 1) -- `tail` without the error

drop₂ ∷ ℒ s → ℒ s
drop₂ = contramap (drop 2)

take₁ ∷ ℒ s → ℒ s
take₁ = contramap (take 1) -- `init` without the error

take₂ ∷ ℒ s → ℒ s
take₂ = contramap (take 2)

-- some useful instances are defined over this type
-- predicate ∷ ℒ s → Predicate [s]
-- predicate = Predicate
predicate ∷ ℒ s → Predicate [s]
predicate (Predicate ℓ) = Predicate ℓ -- ℒ.ℒ -- TODO lol

-- N.B. this is a convenience function, it does not terminate even for finite languages!
language ∷ (Finite s) ⇒ ℒ s → [[s]]
language (Predicate ℓ) = filter ℓ (sigmaStar ℓ)

-- TODO
bellₗ ∷ ℒ ℕ
bellₗ = contramap NE.fromList restricted

-- ℒ (bellₙ 3) = {"000", "001", "010", "011", "012"}
-- c.f. `asList @ (RGS Fin₃)` :)
bellₙ ∷ ℕ → ℒ ℕ
bellₙ = onlyLength bellₗ

-- FIXME just for illustrative purposes for now
-- language' ∷ ℒ ℕ → [[ℕ]]
-- language' (Predicate ℓ) = filter ℓ (freeSemigroup [0 .. 9])
