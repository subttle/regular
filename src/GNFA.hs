{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wall                  #-}

module GNFA where

import           Prelude hiding ((*), (+))
import           Common
import           Finite
import           RegExp as RE
import qualified Data.List as List
import           Data.Set as Set
-- import           Data.Set.Unicode
import           Data.Bool.Unicode
import qualified Data.Map as Map (fromList)
-- import           Data.Either
-- import           Control.Selective
import           Data.Void
import           Data.Pointed
-- import           Data.Functor.Contravariant
-- import           Data.Functor.Contravariant.Divisible
import           Data.Profunctor as Profunctor

-- Generalization of Nondeterministic Finite Automaton with ε-transitions

-- FIXME I haven't yet proven the instances given below to be lawful

-- By using types in this way we can enforce many conditions for GNFA
-- (e.g. qᵢ can have no incoming arrows, qᶠ can have no outgoing arrows)
data GNFA q s where
  -- δ : (Q \ {qᶠ}) × (Q \ {qᵢ}) → Regular Expression
  GNFA ∷ { delta ∷ (Either Init q, Either Final q) → RE.RegExp s } → GNFA q s

instance (Finite q) ⇒ Q (GNFA q s) (Either (Either Init Final) q)
instance (Finite s) ⇒ Σ (GNFA q s) s

instance Pointed (GNFA Void) where
  point = GNFA.literal

instance Pointed (GNFA q) where
  point ∷ s → GNFA q s
  point σ = GNFA { delta = const (point σ) }

instance Functor (GNFA q) where
  fmap ∷ (s → g) → GNFA q s → GNFA q g
  fmap g (GNFA δ) = GNFA { delta = fmap g . δ }

instance Applicative (GNFA q) where
  pure ∷ s → GNFA q s
  pure = point

  (<*>) ∷ GNFA q (s → g) → GNFA q s → GNFA q g
  (<*>) (GNFA δ₁) (GNFA δ₂) = GNFA { delta = \(q, p) → δ₁ (q, p) <*> δ₂ (q, p) }

instance Profunctor.Profunctor GNFA where
  rmap ∷ (s → g) → GNFA q s → GNFA q g
  rmap = fmap
  lmap ∷ (p → q) → GNFA q s → GNFA p s
  lmap f (GNFA δ) = GNFA { delta = \(p₁, p₂) → δ (fmap f p₁, fmap f p₂) }

instance (Show q, Finite q, Show s, Finite s) ⇒ Show (GNFA q s) where
  show ∷ GNFA q s → String
  show m = List.intercalate "\n, " 
           [ "( Q  = "                                              ++ (show . Set' . qs)              m
           ,   "Σ  = "                                              ++ (show . Set' . sigma)           m
           ,   "δ : (Q ∖ {qᶠ}) × (Q ∖ {qᵢ}) → Regular Expression\n" ++ (format . Map.fromList . table) m
           ,   "qᵢ = "                                              ++ show (Init  ())
           ,   "qᶠ = "                                              ++ show (Final ()) ++ ")"
           ]

accepts ∷ (Finite q, Ord s) ⇒ GNFA q s → [s] → Bool
accepts = RE.matches . toRE

table ∷ ∀ q s . (Finite q) ⇒ GNFA q s → [((Either Init q, Either Final q), RE.RegExp s)]
table (GNFA δ) = zip domain image
    where domain = asList ∷ [(Either Init q, Either Final q)]
          image  = fmap δ domain

-- Rip out all of `q` leaving only a two state GNFA (only the two qᵢ and qᶠ states)
reduce ∷ (Finite q, Ord s) ⇒ GNFA q s → GNFA Void s
reduce m = lmap absurd (Set.foldl rip m asSet)

-- δ₁(q, p) = δ(q, r) ⊗ δ(r, r)⋆ ⊗ δ(r, p) ⊕ δ(q, p) where q, p, r ∈ Q, and r is the state to "rip"
rip ∷ ∀ q s . (Eq q, Ord s) ⇒ GNFA q s → q → GNFA q s
rip (GNFA δ) qᵣ' = GNFA { delta = δ₁ }
  where qᵣ ∷ Either a q
        qᵣ = Right qᵣ'
        δ₁ (q, p) | (q == qᵣ) ∨ (p == qᵣ) = zero -- We are ripping qᵣ out, so if qᵣ is an arg to δ₁, return Zero
        δ₁ (q, p)                         = δ (q, qᵣ) * (star (δ (qᵣ, qᵣ)) * δ (qᵣ, p)) + δ (q, p)
        -- or
        -- δ₁ (q, p)                         = δ (q, p) + (δ (q, qᵣ) * (star (δ (qᵣ, qᵣ)) * δ (qᵣ, p)))

extract ∷ GNFA Void s → RE.RegExp s
extract (GNFA δ) = δ (Left (Init ()), Left (Final ()))

toRE ∷ (Finite q, Ord s) ⇒ GNFA q s → RE.RegExp s
toRE = extract . reduce

fromRE ∷         RegExp s → GNFA Void s
fromRE α = GNFA { delta = const α }

empty   ∷                   GNFA Void s
empty   =  fromRE RE.Zero

-- The GNFA, epsilon, such that
-- ℒ(epsilon) = {ε}
epsilon ∷                   GNFA Void s
epsilon =  fromRE RE.One

-- Given a symbol, σ, contstruct a GNFA which recognizes exactly that symbol and nothing else
literal ∷               s → GNFA Void s
literal =  fromRE . RE.Lit

fromSet ∷ (Ord s) ⇒ Set s → GNFA Void s
fromSet =  fromRE . RE.fromSet

fromList ∷            [s] → GNFA Void s
fromList = fromRE . RE.fromList
