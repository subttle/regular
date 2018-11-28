{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE InstanceSigs              #-}
{-# OPTIONS_GHC -Wall                  #-}

module FA where

import qualified Data.List as List
import           Data.Set as Set
import           Data.Set.Unicode
import           Data.Bool.Unicode
import           Data.Ord.Unicode
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Functor.Contravariant
import           Common
import           Config hiding (initial, final)
import qualified Config
import           Finite
import qualified TransitionGraph as TG
import           Algebra.Graph.Relation as Relation

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
    contramap h m@(FA δ _ _) = m { delta = \(q, γ) → δ (q, h γ) }

instance (Finite q, Finite s) ⇒ Configuration FA q s (Set q) where
  deterministic ∷ FA q s → Bool
  deterministic m@(FA _ i _) = size' i == 1 ∧ all ((≤ 1) . size') (range m)

  codeterministic ∷ FA q s → Bool
  codeterministic = deterministic . reversal

  complete ∷ FA q s → Bool
  complete      m            =                all ((≥ 1) . size') (range m)

  occupied ∷ FA q s → Set q → Set q
  occupied _ = id

  initial ∷ FA q s → Set q
  initial (FA _ i _) = i

  final   ∷ FA q s → Set q
  final   (FA _ _ f) = f

  (⊢) ∷ FA q s → (Set q, [s]) → (Set q, [s])
  (⊢) _          (states,    []) = (states,                           [])
  (⊢) (FA δ _ _) (states, σ : w) = (foldMap δ (states × singleton σ), w )

  accessible ∷ FA q s → Set q
  accessible m = foldMap (reachable m) (initial m)
  
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
empty = FA { delta   = const (∅)
           , initial = (∅)
           , final   = (∅)
           }

-- FIXME change this to fit according to whatever constraints will be needed
-- The FA, epsilon, such that
-- ℒ(epsilon) = {ε}
epsilon ∷ FA () s
epsilon = FA { delta   = const (∅)
             , initial = singleton ()
             , final   = singleton ()
             }

-- Given a symbol, construct an FA which recognizes exactly that symbol and nothing else
literal ∷ (Eq s) ⇒ s → FA Bool s
literal σ' = FA { delta   = δ
                , initial = singleton False
                , final   = singleton True
                } where δ (False, σ) | σ == σ' = singleton True
                        δ _                    = (∅)

-- Given a set of symbols, construct an FA which recognizes exactly those set of literals and nothing else
-- Much like a character class of a regular expression.
fromSet ∷ (Ord s) ⇒ Set s → FA Bool s
fromSet s = FA { delta   = δ
               , initial = singleton False
               , final   = singleton True
               } where δ (False, σ) | σ ∈ s = singleton True
                       δ _                  = (∅)

-- Given two FAs m₁ and m₂, return an FA which recognizes any string from
-- m₁ immediately followed by any string from m₂
concatenate ∷ (Ord q, Ord p) ⇒ FA q s → FA p s → FA (Either q p) s
concatenate (FA δ₁ i₁ f₁) (FA δ₂ i₂ f₂) = FA { delta   = δ
                                             , initial = Set.map Left  i₁
                                             , final   = Set.map Right f₂
                                             -- if this state, q, is a final state, merge q's transitions with p0's transitions
                                             } where δ (Left  q, σ) | q ∈ f₁ =               δ₁ (q, σ) ⊎ foldMap (\p₀ → δ₂ (p₀, σ)) i₂  -- merge any last state of m₁ with p₀
                                                     δ (Left  q, σ)          = Set.map Left (δ₁ (q, σ))
                                                     δ (Right p, σ)          =                           Set.map Right (δ₂ (p,  σ))

-- The product construction
synchronous ∷ (Ord q, Ord p) ⇒ FA q s → FA p s → FA (q, p) s
synchronous (FA δ₁ i₁ f₁) (FA δ₂ i₂ f₂) = FA { delta   = δ
                                             , initial = i₁ × i₂
                                             , final   = f₁ × f₂
                                             } where δ ((q, p), σ) = δ₁ (q, σ) × δ₂ (p, σ)

asynchronous ∷ (Ord q, Ord p) ⇒ FA q s → FA p g → FA (q, p) (Either s g)
asynchronous (FA δ₁ i₁ f₁) (FA δ₂ i₂ f₂) = FA { delta   = δ
                                              , initial = i₁ × i₂
                                              , final   = f₁ × f₂
                                              } where δ ((q, p), Left  σ) = δ₁ (q, σ)   × singleton p
                                                      δ ((q, p), Right γ) = singleton q × δ₂ (p, γ)

reversal ∷ (Finite q, Finite s) ⇒ FA q s → FA q s
reversal m@(FA.FA _ i f) = fromGraph (TG.reverse (toGraph m)) f i

fromGraph ∷ (Finite s, Finite q) ⇒ TG.TG q s → Set q → Set q → FA q s
fromGraph (TG.TG a) i f = FA { delta   = δ
                             , initial = i
                             , final   = f
                             } where δ (q, s) = postSet q (a s)

instance (Show q, Finite q, Show s, Finite s) ⇒ Show (FA q s) where
  show m = List.intercalate "\n, "
           ["( Q = "               ++ (show . Set' .      qs)          m
           ,  "Σ = "               ++ (show . Set' .   sigma)          m
           ,  "δ : Q × Σ → P(Q)\n" ++ (format' . Map.fromList . table) m
           ,  "I = "               ++ (show . Set' . initial)          m
           ,  "F = "               ++ (show . Set' .   final)          m ++ " )"
           ]

-- Determinize the FA without transforming it to a DFA type
determinization ∷ (Finite q) ⇒ FA q s → FA (Set q) s
determinization m@(FA δ i f) = FA { delta   = \(states, σ) → Set.map (\q → δ (q, σ)) states
                                  , initial = Set.map singleton i
                                  , final   = Set.filter (intersects f) (powerSet (qs m))
                                  }

-- Pg 32 http://www.dcc.fc.up.pt/~nam/web/resources/rafaelamsc.pdf
codeterminization ∷ (Finite q, Finite s) ⇒ FA q s → FA (Set q) s
codeterminization = reversal . determinization . reversal

-- minimize with `FA` so there is no need to add extra states when reversing (because of single start state) as with NFA
-- Brzozowski minimization
minimize ∷ (Finite q, Finite s) ⇒ FA q s → FA (Set (Set q)) s
minimize = determinization . reversal . determinization . reversal -- or even `determinization . codeterminization`

deltaToMap ∷ (Finite q, Finite s) ⇒ FA q s → Map (q, s) (Set q)
deltaToMap m@(FA δ _ _) = Map.fromSet δ (corange m)

corange ∷ (Finite q, Finite s) ⇒ FA q s → Set (q, s)
corange m = qs m × sigma m

range ∷ (Finite q, Finite s) ⇒ FA q s → Set (Set q)
range m@(FA δ _ _) = Set.map δ (corange m)

table ∷ (Finite q, Finite s) ⇒ FA q s → [((q, s), Set q)]
table m = Map.toAscList (deltaToMap m)