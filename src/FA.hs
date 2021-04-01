{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wall                  #-}

module FA where

import           Algebra.Graph.Relation (postSet, stars)
import           Data.Bool.Unicode ((∧))
import           Data.Functor.Contravariant (Contravariant (..))
import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Ord.Unicode ((≤), (≥))
import           Data.Set as Set (Set, filter, map, powerSet, singleton, toList)
import           Data.Set.Unicode ((∅), (∈))
import           Prelude hiding (map)
import qualified TransitionGraph as TG
import           Common (Set' (..), (×), (⊎), intersects, size', quoteWith, equation, format')
import           Config (Configuration (toGraph, eval, delta', deltaD, accessible, (⊢), occupied, complete, codeterministic, deterministic, reachable, delta''))
import qualified Config
import           Finite (Finite (..), Q (..), Σ (..))

-- This is essentially an NFA with multiple start states
-- Having this type simplifies some algorithms (such as Brzozowski minimization)
data FA q s where
  FA ∷ { delta ∷ (q, s) → Set q, initial ∷ Set q, final ∷ Set q } → FA q s

data SomeFA s where
  SomeFA ∷ (Finite q, Show q) ⇒ FA q s → SomeFA s

instance (Finite q) ⇒ Q (FA q s) q
instance (Finite s) ⇒ Σ (FA q s) s
instance (Finite s) ⇒ Σ (SomeFA s) s

instance Contravariant (FA q) where
  contramap ∷ (g → s) → FA q s → FA q g
  contramap h (FA δ i f) = FA (\(q, γ) → δ (q, h γ)) i f

instance (Finite q, Finite s) ⇒ Configuration FA q s (Set q) where
  deterministic ∷ FA q s → Bool
  deterministic m@(FA _ i _) = size' i == 1 ∧ all ((≤ 1) . size') (image m)

  codeterministic ∷ FA q s → Bool
  codeterministic = deterministic . reversal

  complete ∷ FA q s → Bool
  complete                   =                all ((≥ 1) . size') . image

  occupied ∷ FA q s → Set q → Set q
  occupied = const id

  initial ∷ FA q s → Set q
  initial = initial

  final   ∷ FA q s → Set q
  final   = final

  (⊢) ∷ FA q s → (Set q, [s]) → (Set q, [s])
  (⊢) _          (states,    []) = (states,                           [])
  (⊢) (FA δ _ _) (states, σ : w) = (foldMap δ (states × singleton σ), w )

  accessible ∷ FA q s → Set q
  accessible m = foldMap (reachable m) (initial m)

  -- TODO unchecked/untested
  deltaD ∷ FA q s → (Set q, s) → Set q
  deltaD (FA δ _ _) (states, σ) = foldMap δ (states × singleton σ) -- fst ((⊢) m (states, [σ]))

  delta'' ∷ FA q s → (Set q, [s]) → Set q
  delta'' (FA δ _ _) = uncurry (Prelude.foldl (\states σ → foldMap (\q → δ (q,  σ)) states))

  delta' ∷ FA q s → (q, [s]) → Set q
  delta' m (q, w) = delta'' m (singleton q, w)

  eval ∷ FA q s → [s] → Set q
  eval m@(FA _ i _) w = delta'' m (i, w)

  toGraph ∷ FA q s → TG.TG q s
  toGraph (FA δ _ _) = TG.TG (\s → stars (fmap (\q → (q, Set.toList (δ (q, s)))) (asList ∷ [q])))

-- The FA, empty, such that
-- ℒ(empty) = ∅
empty ∷ FA q s
empty = FA (const (∅)) (∅) (∅)

-- FIXME change this to fit according to whatever constraints will be needed
-- The FA, epsilon, such that
-- ℒ(epsilon) = {ε}
epsilon ∷ FA () s
epsilon = FA (const (∅)) (singleton ()) (singleton ())

-- Given a symbol, construct an FA which recognizes exactly that symbol and nothing else
literal ∷ ∀ s . (Eq s) ⇒ s → FA Bool s
literal σ' = FA δ (singleton False) (singleton True)
  where
    δ ∷ (Bool, s) → Set Bool
    δ (False, σ) | σ == σ' = singleton True
    δ _                    = (∅)

{-
-- TODO
-- Given a symbol, construct an FA which recognizes exactly that symbol and nothing else
literal ∷ ∀ s . (Eq s) ⇒ s → FA Bool s
literal = fa (singleton False) (singleton True) . uncurry . (bool (singleton True) (∅) … (flip . ((∨) ‥ (≠))))
  where
    fa ∷ Set q → Set q → ((q, s) → Set q) → FA q s
    fa = flip . (flip FA.FA)

-- TODO
literal' ∷ ∀ s . Equivalence s → s → FA Bool s
literal' = undefined
-}

-- Given a set of symbols, construct an FA which recognizes exactly those set of literals and nothing else
-- Much like a character class of a regular expression.
fromSet ∷ ∀ s . (Ord s) ⇒ Set s → FA Bool s
fromSet s = FA δ (singleton False) (singleton True)
  where
    δ ∷ (Bool, s) → Set Bool
    δ (False, σ) | σ ∈ s = singleton True
    δ _                  = (∅)

-- Given two FAs m₁ and m₂, return an FA which recognizes any string from
-- m₁ immediately followed by any string from m₂
concatenate ∷ ∀ q p s . (Ord q, Ord p) ⇒ FA q s → FA p s → FA (Either q p) s
concatenate (FA δ₁ i₁ f₁) (FA δ₂ i₂ f₂) = FA δ (map Left  i₁) (map Right f₂)
  where
    δ ∷ (Either q p, s) → Set (Either q p)
    -- if this state, q, is a final state, merge q's transitions with p₀'s transitions
    δ (Left  q, σ) | q ∈ f₁ = (δ₁ (q, σ)) ⊎ foldMap (\p₀ → δ₂ (p₀, σ)) i₂  -- merge any last state of m₁ with p₀
    δ (Left  q, σ)          = (δ₁ (q, σ)) ⊎ (∅)
    δ (Right p, σ)          = (∅)         ⊎ (δ₂ (p,  σ))

-- The product construction
synchronous ∷ (Ord q, Ord p) ⇒ FA q s → FA p s → FA (q, p) s
synchronous (FA δ₁ i₁ f₁) (FA δ₂ i₂ f₂) = FA (\((q, p), σ) → δ₁ (q, σ) × δ₂ (p, σ)) (i₁ × i₂) (f₁ × f₂)

asynchronous ∷ ∀ q p s g . (Ord q, Ord p) ⇒ FA q s → FA p g → FA (q, p) (Either s g)
asynchronous (FA δ₁ i₁ f₁) (FA δ₂ i₂ f₂) = FA δ (i₁ × i₂) (f₁ × f₂)
  where
    δ ∷ ((q, p), Either s g) → Set (q, p)
    δ ((q, p), Left  σ) = δ₁ (q, σ)   × singleton p
    δ ((q, p), Right γ) = singleton q × δ₂ (p, γ)

-- reverse the graph, swap initial and final states
reversal ∷ (Finite q, Finite s) ⇒ FA q s → FA q s
reversal m = fromGraph (TG.reverse (toGraph m)) (final m) (initial m)

fromGraph ∷ (Finite s, Finite q) ⇒ TG.TG q s → Set q → Set q → FA q s
fromGraph (TG.TG t) = FA (\(q, s) → postSet q (t s))

instance (Show q, Finite q, Show s, Finite s) ⇒ Show (FA q s) where
  show ∷ FA q s → String
  show m = quoteWith "( " " )" $ List.intercalate "\n, "
           [ equation "Q"                 ((show    . Set'         . qs     ) m)
           , equation "Σ"                 ((show    . Set'         . sigma  ) m)
           , quoteWith "δ : Q × Σ → P(Q)" ((format' . Map.fromList . table  ) m) "\n"
           , equation "I"                 ((show    . Set'         . initial) m)
           , equation "F"                 ((show    . Set'         . final  ) m)
           ]

-- Determinize the FA without transforming it to a DFA type
determinization ∷ (Finite q) ⇒ FA q s → FA (Set q) s
determinization m@(FA δ i f) = FA (\(states, σ) → map (\q → δ (q, σ)) states)
                                  (map singleton i)
                                  (Set.filter (intersects f) (powerSet (qs m)))

-- Pg 32 https://www.dcc.fc.up.pt/~nam/web/resources/rafaelamsc.pdf
codeterminization ∷ (Finite q, Finite s) ⇒ FA q s → FA (Set q) s
codeterminization = reversal . determinization . reversal

-- minimize with `FA` so there is no need to add extra states when reversing (because of single start state) as with NFA
-- Brzozowski minimization
minimize ∷ (Finite q, Finite s) ⇒ FA q s → FA (Set (Set q)) s
minimize = determinization . codeterminization

deltaToMap ∷ (Finite q, Finite s) ⇒ FA q s → Map (q, s) (Set q)
deltaToMap m@(FA δ _ _) = Map.fromSet δ (domain m)

domain ∷ (Finite q, Finite s) ⇒ FA q s → Set (q, s)
domain m = qs m × sigma m

image ∷ (Finite q, Finite s) ⇒ FA q s → Set (Set q)
image m@(FA δ _ _) = map δ (domain m)

table ∷ (Finite q, Finite s) ⇒ FA q s → [((q, s), Set q)]
table = Map.toAscList . deltaToMap
