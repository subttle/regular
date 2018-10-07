{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables, InstanceSigs, UnicodeSyntax #-}

module GFA where

import           Prelude hiding ((*), (+))
import           Common
import           Finite
import           RE
import qualified EFA
import           Data.Set as Set
import           Data.Set.Unicode
import           Data.Bool.Unicode
import qualified Data.Map as Map (fromList)
import           Data.Either
import           Data.Void
import           Data.Pointed
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Divisible
import qualified Data.Profunctor as Profunctor

-- Generalized Nondeterministic Finite Automaton with ε-transitions

-- FIXME I haven't yet proven the instances given below to be lawful

-- By using types in this way we can enforce many conditions for GFA
-- (e.g. qᵢ can have no incoming arrows, qᶠ can have no outgoing arrows)
data GFA q s =   -- δ : (Q \ {qᶠ}) × (Q \ {qᵢ}) → Regular Expression
     GFA { delta ∷ (Either Init q, Either Final q) → RE.RegExp s }

instance (Finite q) ⇒ Q (GFA q s) (Either (Either Init Final) q)
instance (Finite s) ⇒ Σ (GFA q s) s

instance Pointed (GFA Void) where
  point = GFA.literal

instance Pointed (GFA q) where
  point ∷ s → GFA q s
  point σ = GFA { delta = const (point σ) }

instance Functor (GFA q) where
  fmap ∷ (s → g) → GFA q s → GFA q g
  fmap g (GFA δ) = GFA { delta = fmap g . δ }

instance Applicative (GFA q) where
  pure ∷ s → GFA q s
  pure = point

  (<*>) ∷ GFA q (s → g) → GFA q s → GFA q g
  (<*>) (GFA δ₁) (GFA δ₂) = GFA { delta = δ }
      where δ (q, p) = δ₁ (q, p) <*> δ₂ (q, p)

instance Profunctor.Profunctor GFA where
  rmap ∷ (s → g) → GFA q s → GFA q g
  rmap = fmap
  lmap ∷ (p → q) → GFA q s → GFA p s
  lmap f (GFA δ) = GFA { delta = \(p₁, p₂) → δ (fmap f p₁, fmap f p₂) }

instance (Show q, Finite q, Show s, Finite s) ⇒ Show (GFA q s) where
  show m = "( Q      = " ++ (show . Set' . qs)                   m ++
         "\n, Σ      = " ++ (show . Set' . sigma)                m ++
         "\n, δ : (Q ∖ {qᶠ}) × (Q ∖ {qᵢ}) → Regular Expression"    ++
         "\n"            ++ (format . Map.fromList . table)      m ++
         "\n, qᵢ = "     ++ show (Init  ())                        ++
         "\n, qᶠ = "     ++ show (Final ())                        ++ ")"

table ∷ ∀ q s . (Finite q) ⇒ GFA q s → [((Either Init q, Either Final q), RE.RegExp s)]
table m@(GFA δ) = zip domain image
    where domain = asList :: [(Either Init q, Either Final q)]
          image  = fmap δ domain

reduce ∷ ∀ q s . (Finite q, Ord s) ⇒ GFA q s → GFA Void s
reduce m = GFA { delta  = δ₁ }
     where m' = Set.foldl rip m (asSet :: Set q)  -- rip out all of `Right q`
           δ₁ ∷ (Either Init Void, Either Final Void) → RegExp s
           δ₁ (Left (Init ()), Left (Final ())) = delta m' (Left (Init ()), Left (Final ()))

-- δ₁(q, p) = δ(q, r) ⊗ δ(r, r)⋆ ⊗ δ(r, p) ⊕ δ(q, p) where q, p, r ∈ Q, and r is the state to "rip"
rip ∷ ∀ q s . (Ord s, Ord q) ⇒ GFA q s → q → GFA q s
rip (GFA δ) qᵣ' = GFA { delta = δ₁ }
  where qᵣ ∷ Either a q
        qᵣ = Right qᵣ'
        δ₁ (q, p) | (q == qᵣ) ∨ (p == qᵣ) = zero -- We are ripping qᵣ out, so if qᵣ is an arg to δ₁, return Zero
        δ₁ (q, p)                         = δ (q, qᵣ) * (star (δ (qᵣ, qᵣ)) * δ (qᵣ, p)) + δ (q, p)
        -- or
        -- δ₁ (q, p) = δ (q, p) + (δ (q, qᵣ) * (star (δ (qᵣ, qᵣ)) * δ (qᵣ, p)))

extract ∷ GFA Void s → RE.RegExp s
extract (GFA δ) = δ (Left (Init ()), Left (Final ()))

toRE ∷ (Ord s, Finite q) ⇒ GFA q s → RE.RegExp s
toRE = extract . reduce

fromRE ∷         RegExp s → GFA Void s
fromRE α = GFA { delta = const α }

empty   ∷                   GFA Void s
empty   =  fromRE RE.Zero

-- The GFA, epsilon, such that
-- ℒ(epsilon) = {ε}
epsilon ∷                   GFA Void s
epsilon =  fromRE RE.One

-- Given a symbol, σ, contstruct a GFA which recognizes exactly that symbol and nothing else
literal ∷               s → GFA Void s
literal =  fromRE . RE.Lit

fromSet ∷ (Ord s) ⇒ Set s → GFA Void s
fromSet =  fromRE . RE.fromSet

fromList ∷            [s] → GFA Void s
fromList = fromRE . RE.fromList