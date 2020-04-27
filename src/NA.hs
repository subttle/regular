{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# OPTIONS_GHC -Wall                  #-}

module NA where

-- import qualified Language
-- import           Language (ℒ)
import           Finite
-- import           Data.Bool.Unicode
import           Data.Functor.Contravariant (Predicate, Predicate (..))
-- import           Data.Void (Void)

-- Experiment based on:
-- http://www.few.vu.nl/~cgr600/linkedfiles/swansea_slides.pdf
-- Using Proofs by Coinduction to Find “Traditional” Proofs Clemens Grabmayer
-- And some work by Jan Rutten
-- Automata and Coinduction (An Exercise in Coalgebra) J.J.M.M. Rutten
-- http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.221.6957&rep=rep1&type=pdf

-- Nondeterministic Automaton
data NA q s =
     NA { output     ∷ Predicate q
        , transition ∷ q → (s → Predicate q)
        }

-- A NA constructor where the `q` type parameter is an existential
data SomeNA s where
  SomeNA ∷ (Show q, Finite q) ⇒ NA q s → SomeNA s

