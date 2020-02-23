{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# OPTIONS_GHC -Wall                  #-}
-- {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module DA where

import           Common (RenameMe, renameme, (…))
import qualified Language
import           Language (ℒ)
import           Finite
import           Data.Bool.Unicode
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Divisible
import           Data.These (These, These(..), these)
import           Data.Void

-- Experiment based on:
-- http://www.few.vu.nl/~cgr600/linkedfiles/swansea_slides.pdf
-- Using Proofs by Coinduction to Find “Traditional” Proofs Clemens Grabmayer
-- And some work by Jan Rutten
-- Automata and Coinduction (An Exercise in Coalgebra) J.J.M.M. Rutten 
-- http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.221.6957&rep=rep1&type=pdf

-- Deterministic Automaton
-- N.B. that DA does not require `q` or `s` to be finite, but when they are
-- then DA has the same power as an FA (without the initial state(s)).
data DA q s =                 -- q is the set of states, Q
                              -- s is the alphabet
     DA { output     ∷ Predicate q
        , transition ∷ q → (s → q)
        }

-- A DA constructor where the `q` type parameter is an existential
data SomeDA s where
  SomeDFA ∷ (Show q, Finite q) ⇒ DA q s → SomeDA s

instance (Finite q) ⇒ Q (DA q s) q
instance (Finite s) ⇒ Σ (DA q s) s

instance Contravariant (DA q) where
  contramap ∷ (g → s) → DA q s → DA q g
  contramap h (DA o t) = DA o (\q → t q . h)

-- FIXME: these instances (`Divisible`, `Decidable`, and `RenameMe`) are just experimental for now
instance Divisible (DA q) where
  divide ∷ (s → (g₁, g₂)) → DA q g₁ → DA q g₂ → DA q s
  divide h (DA o₁ t₁) (DA o₂ t₂) = DA (o₁ <> o₂) (\q → uncurry (t₂ . t₁ q) . h)

  conquer ∷ DA q a
  conquer = DA conquer const

instance Decidable (DA q) where
  lose ∷ (a → Void) → DA q a
  lose _ = empty

  choose ∷ (s → Either g₁ g₂) → DA q g₁ → DA q g₂ → DA q s
  choose h (DA (Predicate o₁) t₁) (DA (Predicate o₂) t₂) = DA (Predicate (\q →         o₁ q ∨ o₂ q     ))
                                                                         (\q → either (t₁ q) (t₂ q) . h)

instance RenameMe (DA q) where
  renameme ∷ (s → These g₁ g₂) → DA q g₁ → DA q g₂ → DA q s
  renameme h (DA o₁ t₁) (DA o₂ t₂) = DA (o₁ <> o₂) (\q → these (t₁ q) (t₂ q) (t₂ . t₁ q) . h)
  {-
  renameme h (DA (Predicate o₁) t₁) (DA (Predicate o₂) t₂) = DA (Predicate (\q →        o₁ q ∨ o₂ q                 ))
                                                                           (\q → these (t₁ q) (t₂ q) (t₂ . t₁ q) . h)
  -}

literal ∷ ∀ s . (Finite s) ⇒ s → (DA.DA Ordering s, Ordering)
literal σ = (DA (Predicate (== EQ)) t, LT)
  where
    t ∷ Ordering → s → Ordering
    t LT s | s == σ = EQ
    t _  _          = GT

language ∷ DA q s → q → ℒ s
language (DA o t) = (>$$<) o . foldl t

accepts ∷ DA q s → q → [s] → Bool
accepts = getPredicate … language

nullable ∷ DA q s → q → Bool
nullable m q = accepts m q []

-- "automaton of languages" or "the final automaton of languages"
-- "This automaton has the pleasing property that the language accepted by a state L in ℒ [the set of all languages] is precisely L itself."
-- Automata and Coinduction (An Exercise in Coalgebra) J.J.M.M. Rutten
automaton ∷ DA (ℒ s) s
automaton = DA (Predicate Language.nullable) Language.derivative

empty ∷ DA q s
empty = DA (Predicate (const False)) const

complement ∷ DA q s → DA q s
complement (DA (Predicate o) t) = DA (Predicate (not . o)) t

intersection ∷ DA q s → DA p s → DA (q, p) s
intersection (DA (Predicate o₁) t₁) (DA (Predicate o₂) t₂) = DA (Predicate (\(q , p)   →  o₁ q   ∧ o₂ p  ))
                                                                           (\(q , p) σ → (t₁ q σ , t₂ p σ))

union ∷ DA q s → DA p s → DA (q, p) s
union (DA (Predicate o₁) t₁) (DA (Predicate o₂) t₂) = DA (Predicate (\(q , p)   →  o₁ q   ∨ o₂ p  ))
                                                                    (\(q , p) σ → (t₁ q σ , t₂ p σ))

difference ∷ DA q s → DA p s → DA (q, p) s
difference m = intersection m . complement

ot ∷ DA q s → q → (Bool, s → q)
ot (DA (Predicate o) t) q = (o q, t q)
