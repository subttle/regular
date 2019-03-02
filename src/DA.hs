{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# OPTIONS_GHC -Wall                  #-}

module DA where

-- import           Common
import qualified Language
import           Language (ℒ)
-- import           Finite
-- import           Data.Bool.Unicode
-- import           Data.Functor.Contravariant
-- import           Data.Functor.Contravariant.Divisible
-- import           Data.Void

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
     DA { output     ∷ q → Bool
        , transition ∷ q → (s → q)
        }

language ∷ DA q s → q → ℒ s
language (DA o _) q []      = o q
language (DA o t) q (a : w) = language (DA o t) (t q a) w

-- "automaton of languages"
automaton ∷ DA (ℒ s) s
automaton = DA { output     = Language.nullable
               , transition = Language.derivative
               }

empty ∷ DA q s
empty = DA { output     = const False
           , transition = const
           }

complement ∷ DA q s → DA q s
complement m@(DA o _) = m { output = not . o }
