{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE FlexibleInstances         #-}

module Language where

import           Common
import           Finite
import           Data.Bool.Unicode
import           Data.List
import qualified Data.List.NonEmpty as NE
import           Data.Functor.Contravariant

-- N.B. This is /not/ the type for regular languages (but I am adding it to help test some properties)
-- In Agda (with termination checking) this can be used as a type for decidable languages, and while this
-- is not necessarily the case in Haskell, it is assumed to be total in this library to represent decidable languages.

-- Language over Σ
type ℒ s = Predicate [s]

-- TODO I should experiment more because
-- TODO I bet it would be much cleaner for some parts to implement in terms of monoid instead of list

instance (Finite s) ⇒ Σ (ℒ s) s

-- provided for convenience/clarity.
-- ℓ `accepts` w ≡ ℓ w
accepts ∷ ℒ s → [s] → Bool
accepts = getPredicate

-- iff ε ∈ ℒ
nullable ∷ ℒ s → Bool
nullable (Predicate ℓ) = ℓ []

-- the language which accepts no strings
empty ∷ ℒ s
empty = Predicate (const False)

-- the language which accepts only the empty string
epsilon ∷ ℒ s
epsilon = Predicate null

-- the language which accepts only a single literal
-- want version of `null` for NE? `isSingleton`?
lit ∷ forall s . (Eq s) ⇒ s → ℒ s
lit σ = Predicate p
  where p ∷ [s] → Bool
        p [σ'] = σ == σ'
        p _    = False

complement ∷ ℒ s → ℒ s
complement (Predicate ℓ) = Predicate (not . ℓ)

reversed ∷ ℒ s → ℒ s
reversed = contramap reverse

union ∷ ℒ s → ℒ s → ℒ s
union        (Predicate ℓ₁) (Predicate ℓ₂) = Predicate (\w → ℓ₁ w ∨ ℓ₂ w)

intersection ∷ ℒ s → ℒ s → ℒ s
intersection (Predicate ℓ₁) (Predicate ℓ₂) = Predicate (\w → ℓ₁ w ∧ ℓ₂ w)
-- intersection = (<>) -- :P

concatenate ∷ ℒ s → ℒ s → ℒ s
concatenate  (Predicate ℓ₁) (Predicate ℓ₂) = Predicate (\w → any (\(w₁ , w₂) → ℓ₁ w₁ ∧ ℓ₂ w₂) (zip (inits w) (tails w)))

-- Kleene star
star ∷ forall s . ℒ s → ℒ s
star (Predicate ℓ) = Predicate p
  where
    -- TODO express in terms of `epsilon + any ...`?
    p ∷ [s] → Bool
    p [] = True
    p w  = any (all (ℓ . NE.toList)) (partitions w)

-- inverse homomorphism
invhom ∷ ([s] → [g]) → ℒ g → ℒ s
invhom = contramap

-- inverse homomorphic image of ℓ under h
invhomimage ∷ (s → [g]) → ℒ g → ℒ s
invhomimage h = contramap (concatMap h)

-- ε-free inverse homomorphic image of ℓ under h
invhomimageEpsFree ∷ (s → NE.NonEmpty g) → ℒ g → ℒ s
invhomimageEpsFree h = contramap (concatMap (NE.toList . h))

invhomimagew ∷ (Eq g) ⇒ (s → [g]) → [g] → ℒ s
invhomimagew h w = Predicate ((w ==) . concatMap h)

-- derivative with respect to some symbol in Σ
derivative ∷ ℒ s → s → ℒ s
derivative (Predicate ℓ) a = Predicate (\w → ℓ (a : w))

-- derivative with respect to some word ∈ Σ★
derivative' ∷ ℒ s → [s] → ℒ s
derivative' (Predicate ℓ) w₁ = Predicate (\w₂ → ℓ (w₁ ++ w₂))

-- some useful instances are defined over this type
-- predicate ∷ ℒ s → Predicate [s]
-- predicate = Predicate
predicate ∷ ℒ s → Predicate [s]
predicate (Predicate ℓ) = Predicate ℓ -- ℒ.ℒ -- TODO lol

-- N.B. this is a convenience function, it does not terminate even for finite languages!
-- language ∷ (Finite s) ⇒ ℒ s → [[s]]
-- language (Predicate ℓ) = filter ℓ (sigmaStar ℓ)
