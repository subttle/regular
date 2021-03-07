{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# OPTIONS_GHC -Wall                  #-}
-- {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module DA where

import           Data.Bool.Unicode ((∧), (∨))
import           Data.Can   (Can   (..), can)
import           Data.Functor.Contravariant (Contravariant (..), Predicate (..), (>$$<))
import           Data.Functor.Contravariant.Divisible (Divisible (..), Decidable (..))
import qualified Data.List as List
import           Data.Smash (Smash (..), smash)
import           Data.These (These (..), these)
import           Data.Void (Void)
import           Data.Wedge (Wedge (..), wedge)
import           Common (ContraCan (..), ContraSmash (..), ContraThese (..), ContraWedge (..), Set' (..), equation, quoteWith, (‥))
import           Finite (Finite (..), Q (..), Σ (..))
import qualified Language
import           Language (ℒ)

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
  SomeDA ∷ (Show q, Finite q) ⇒ DA q s → SomeDA s

instance (Finite q) ⇒ Q (DA q s) q
instance (Finite s) ⇒ Σ (DA q s) s

instance Contravariant (DA q) where
  contramap ∷ (g → s) → DA q s → DA q g
  contramap h (DA o t) = DA o (\q → t q . h)

-- FIXME: these instances (`Divisible`, `Decidable`, `ContraThese`, `ContraCan`, `ContraSmash`, and `ContraWedge`) are just experimental for now
instance Divisible (DA q) where
  divide ∷ (s → (g₁, g₂)) → DA q g₁ → DA q g₂ → DA q s
  divide h (DA o₁ t₁) (DA o₂ t₂) = DA (o₁ <> o₂) (\q → uncurry (t₂ . t₁ q) . h)

  conquer ∷ DA q a
  conquer = DA conquer const

instance Decidable (DA q) where
  lose ∷ (a → Void) → DA q a
  lose = const empty

  choose ∷ (s → Either g₁ g₂) → DA q g₁ → DA q g₂ → DA q s
  choose h (DA (Predicate o₁) t₁) (DA (Predicate o₂) t₂) = DA (Predicate (\q →         o₁ q ∨ o₂ q     ))
                                                                         (\q → either (t₁ q) (t₂ q) . h)
{-
-- FIXME
asdf h (DA (Predicate o₁) t₁) (DA (Predicate o₂) t₂) = DA (Predicate (\q →   _)) --      o₁ q ∨ o₂ q
                                                                     (\q → destructor _ _ _ . h)
asdf h (DA o₁ t₁) (DA o₂ t₂) = DA (o₁ <> o₂) _
-}
instance ContraThese (DA q) where
  contrathese ∷ (s → These g₁ g₂) → DA q g₁ → DA q g₂ → DA q s
  contrathese h (DA o₁ t₁) (DA o₂ t₂) = DA (o₁ <> o₂) (\q → these (t₁ q) (t₂ q) (t₂ . t₁ q) . h)

-- `Can` is basically `Maybe (Either (Either a b) (a, b))`
instance ContraCan (DA q) where
  contracan ∷ (s → Can g₁ g₂) → DA q g₁ → DA q g₂ → DA q s
  contracan h (DA o₁ t₁) (DA o₂ t₂) = DA undefined (\q → can q (t₁ q) (t₂ q) (t₂ . t₁ q) . h)

-- `Smash` is basically `Maybe (a, b)`
instance ContraSmash (DA q) where
  contrasmash ∷ (s → Smash g₁ g₂) → DA q g₁ → DA q g₂ → DA q s
  contrasmash h (DA o₁ t₁) (DA o₂ t₂) = DA undefined (\q → smash q (t₂ . t₁ q) . h)

-- `Wedge` is basically `Maybe (Either a b)`
instance ContraWedge (DA q) where
  contrawedge ∷ (s → Wedge g₁ g₂) → DA q g₁ → DA q g₂ → DA q s
  contrawedge h (DA o₁ t₁) (DA o₂ t₂) = DA undefined (\q → wedge q (t₁ q) (t₂ q) . h)

{-
asdf2e ∷ ∀ q p s . DA q s → DA p s → DA (Either q p) s
asdf2e (DA (Predicate o₁) t₁) (DA (Predicate o₂) t₂) = DA o t
  where
    o ∷ Predicate (Either q p)
    o = Predicate (either o₁ o₂)
    t ∷ Either q p → s → Either q p
    t c σ = either (Left . flip t₁ σ) (Right . flip t₂ σ) c
    -- t = (flip r)
    --   where
    --     r ∷ s → Either q p → Either q p
    --     r = getOp (contramap (liftA2 bimap (flip t₁) (flip t₂)) (Op id))

-}

-- TODO could probably clean this up a bit
instance (Show q, Finite q, Show s, Finite s) ⇒ Show (DA q s) where
  show ∷ DA q s → String
  show m@(DA (Predicate o) t) = quoteWith "( " " )" $ List.intercalate "\n, "
                                [ equation "Q"              ((show . Set' . qs   ) m)
                                , equation "Σ"              ((show . Set' . sigma) m)
                                -- TODO or S → S^A
                                , quoteWith "t : Q → Σ → Q" formatt "\n"
                                , quoteWith "o : Q → Bool"  formato "\n"
                                ]
    where
      formatt ∷ String
      formatt = List.intercalate "\n" ts
        where
          ts ∷ [String]
          ts = fmap (\(q, s) → quoteWith ("  t" ++ quoteWith "(" ")" (show q) ++ quoteWith "(" ")" (show s)) (show (t q s)) " ↦ ") (asList ∷ [(q, s)])
      formato ∷ String
      formato = List.intercalate "\n" os
        where
          os ∷ [String]
          os = fmap (\q → quoteWith ("  o" ++ quoteWith "(" ")" (show q)) (show (o q)) " ↦ ") (asList ∷ [q])

instance (Show s, Finite s) ⇒ Show (SomeDA s) where
  show ∷ SomeDA s → String
  show (SomeDA m) = show m

literal ∷ ∀ s . (Finite s) ⇒ s → (DA.DA Ordering s, Ordering)
literal σ = (DA (Predicate (== EQ)) t, LT)
  where
    t ∷ Ordering → s → Ordering
    t LT s | s == σ = EQ
    t _  _          = GT

language ∷ DA q s → q → ℒ s
language (DA o t) = (>$$<) o . foldl t

accepts ∷ DA q s → q → [s] → Bool
accepts = getPredicate ‥ language

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
