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
type ℒ s = [s] → Bool

instance (Finite s) ⇒ Σ (ℒ s) s

-- provided for convenience/clarity.
-- ℓ `accepts` w ≡ ℓ w
accepts ∷ ℒ s → [s] → Bool
accepts = id

-- iff ε ∈ ℒ
nullable ∷ ℒ s → Bool
nullable ℓ = ℓ []

-- the language which accepts no strings
empty ∷ ℒ s
empty = const False

-- the language which accepts only the empty string
epsilon ∷ ℒ s
epsilon [] = True
epsilon _  = False

-- the language which accepts only a single literal
lit ∷ (Eq s) ⇒ s → ℒ s
lit σ [σ'] = σ == σ'
lit _ _    = False

complement ∷ ℒ s → ℒ s
complement ℓ = not . ℓ

reversed ∷ ℒ s → ℒ s
reversed ℓ = ℓ . reverse

union ∷ ℒ s → ℒ s → ℒ s
union ℓ₁ ℓ₂ w = ℓ₁ w ∨ ℓ₂ w

intersection ∷ ℒ s → ℒ s → ℒ s
intersection ℓ₁ ℓ₂ w = ℓ₁ w ∧ ℓ₂ w

concatenate ∷ ℒ s → ℒ s → ℒ s
concatenate ℓ₁ ℓ₂ w =  any (\(w₁ , w₂) → ℓ₁ w₁ ∧ ℓ₂ w₂) (zip (inits w) (tails w))

-- Kleene star
star ∷ ℒ s → ℒ s
star _ [] = True
star ℓ w  = any (all (ℓ . NE.toList)) (partitions w)

-- inverse homomorphism
invhom ∷ ([s] → [g]) → ℒ g → ℒ s
invhom h ℓ = ℓ . h

-- inverse homomorphic image of ℓ under h
invhomimage ∷ (s → [g]) → ℒ g → ℒ s
invhomimage h ℓ = ℓ . concatMap h

-- ε-free inverse homomorphic image of ℓ under h
invhomimageEpsFree ∷ (s → NE.NonEmpty g) → ℒ g → ℒ s
invhomimageEpsFree h ℓ = ℓ . concatMap (NE.toList . h)

invhomimagew ∷ (Eq g) ⇒ (s → [g]) → [g] → ℒ s
invhomimagew h w = (w ==) . concatMap h

-- derivative with respect to some symbol in Σ
derivative ∷ ℒ s → s → ℒ s
derivative ℓ a w = ℓ (a : w)

-- derivative with respect to some word ∈ Σ★
derivative' ∷ ℒ s → [s] → ℒ s
derivative' ℓ v w = ℓ (v ++ w)

-- some useful instances are defined over this type
predicate ∷ ℒ s → Predicate [s]
predicate = Predicate

-- N.B. this is a convenience function, it does not terminate even for finite languages!
language ∷ (Finite s) ⇒ ℒ s → [[s]]
language ℓ = filter ℓ (sigmaStar ℓ)
