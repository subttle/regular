{-# LANGUAGE MultiParamTypeClasses     #-}
{-# OPTIONS_GHC -Wall                  #-}

module DA where

-- import           Common
import qualified Language
import           Language (ℒ)
-- import           Finite
import           Data.Bool.Unicode
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Divisible
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

instance Contravariant (DA q) where
    contramap ∷ (b → a) → DA q a → DA q b
    contramap h m@(DA _ t) = m { transition = \a → t a . h }

language ∷ forall q s . DA q s → q → ℒ s
language (DA (Predicate o) t) q = Predicate (o . foldl t q)

accepts ∷ DA q s → q → [s] → Bool
accepts m = getPredicate . language m

-- "automaton of languages" or "the final automaton of languages"
-- "This automaton has the pleasing property that the language accepted by a state L in ℒ [the set of all languages] is precisely L itself."
-- Automata and Coinduction (An Exercise in Coalgebra) J.J.M.M. Rutten
automaton ∷ DA (ℒ s) s
automaton = DA (Predicate Language.nullable) Language.derivative

empty ∷ DA q s
empty = DA (Predicate (const False)) const

complement ∷ DA q s → DA q s
complement m@(DA (Predicate o) _) = m { output = Predicate (not . o) }

intersection ∷ DA q s → DA p s → DA (q, p) s
intersection (DA (Predicate o₁) t₁) (DA (Predicate o₂) t₂) = DA (Predicate (\(q , p)   →  o₁ q   ∧ o₂ p  ))
                                                                           (\(q , p) σ → (t₁ q σ , t₂ p σ))

union ∷ DA q s → DA p s → DA (q, p) s
union (DA (Predicate o₁) t₁) (DA (Predicate o₂) t₂) = DA (Predicate (\(q , p)   →  o₁ q   ∨ o₂ p  ))
                                                                    (\(q , p) σ → (t₁ q σ , t₂ p σ))

difference ∷ DA q s → DA p s → DA (q, p) s
difference m₁ m₂ = intersection m₁ (complement m₂)
