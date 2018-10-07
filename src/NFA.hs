{-# LANGUAGE GADTs, InstanceSigs, FlexibleInstances, MultiParamTypeClasses, IncoherentInstances, RankNTypes, UnicodeSyntax #-}
{-# OPTIONS -Wall #-}
module NFA where

import           Common
import           Data.Map            as Map (Map, fromList)
import qualified Data.Map            as Map (fromSet, toAscList)
import           Data.Set            as Set hiding (foldl)
import qualified Data.List.NonEmpty  as NE
import           Data.Set.Unicode
import           Data.Ord.Unicode
import qualified EFA
import qualified FA
import qualified TransitionGraph as TG
import           Finite
import           Data.Functor.Contravariant
-- import           Data.Functor.Invariant
-- import           Data.Functor.Contravariant.Divisible
import           Algebra.Graph.Relation as Relation hiding (domain)
import           Config
-- import           Data.Maybe (fromJust)

-- Nondeterministic Finite Automaton
data NFA q s =
     NFA { delta ∷ (q, s) → Set q -- δ : Q × Σ → P(Q)
         ,    q0 ∷ q              -- The initial state
         ,    fs ∷ Set q          -- The final states
         }

data SomeNFA s where
  SomeNFA ∷ (Finite q, Show q) ⇒ NFA q s → SomeNFA s

instance (Finite q) ⇒ Q (NFA q s) q
instance (Finite s) ⇒ Σ (NFA q s) s
instance (Finite s) ⇒ Σ (SomeNFA s) s

instance Contravariant (NFA q) where
  contramap ∷ (g → s) → NFA q s → NFA q g
  contramap h m@(NFA δ _ _) = m { delta = \(q, γ) → δ (q, h γ) }

instance Contravariant SomeNFA where
  contramap h (SomeNFA m) = SomeNFA (contramap h m)

instance (Show q, Finite q, Show s, Finite s) ⇒ Show (NFA q s) where
  show m@(NFA _ q₀ f) = "( Q  = " ++ (show . Set' . qs)               m ++
                      "\n, Σ  = " ++ (show . Set' . sigma)            m ++
                      "\n, δ  : Q × Σ → P(Q)"                           ++
                      "\n"        ++ (format' . Map.fromList . table) m ++
                      "\n, q0 = " ++  show q₀                           ++
                      "\n, F  = " ++ (show . Set' $ f)                  ++ " )"

instance (Show s, Finite s) ⇒ Show (SomeNFA s) where
  show (SomeNFA m) = show m

instance (Finite q, Finite s) ⇒ Configuration NFA q s (Set q) where
  deterministic ∷ NFA q s → Bool
  deterministic m = all ((≤ 1) . size') (range m)
  
  codeterministic ∷ NFA q s → Bool
  codeterministic = deterministic . FA.reversal . toFA

  complete ∷ NFA q s → Bool
  complete m = all ((≥ 1) . size') (range m)

  occupied ∷ NFA q s → Set q → Set q
  occupied _ = id
  
  initial ∷ NFA q s → Set q
  initial (NFA _ q₀ _) = singleton q₀

  final   ∷ NFA q s → Set q
  final   (NFA _ _  f) = f

  -- Given an NFA, m, and a configuration, return what it yields in one step
  (⊢) ∷ NFA q s → (Set q, [s]) → (Set q, [s])
  (⊢) _           (states,    []) = (states,                           [])
  (⊢) (NFA δ _ _) (states, σ : w) = (foldMap δ (states × singleton σ),  w)

  accessible ∷ NFA q s → Set q
  accessible m@(NFA _ q₀ _) = reachable m q₀

  -- δ⋆ : Q × Σ★ → P(Q)
  -- "Extended delta"
  -- Take an NFA and a starting state, q, for that NFA,
  -- then compute the set of states P such that δ★(q, w) = P
  delta' ∷ NFA q s → (q, [s]) → Set q  -- TODO untested
  delta' m (q, w) = delta'' m (singleton q, w)

  -- δ★ : P(Q) × Σ★ → P(Q)  -- TODO untested
  delta'' ∷ NFA q s → (Set q, [s]) → Set q
  delta'' (NFA δ _ _) = uncurry (foldl (\states σ → foldMap δ (states × singleton σ)))

  -- Take an NFA, m, and a string, and then compute the resulting states, which may be an empty set
  eval ∷ NFA q s → [s] → Set q
  eval m@(NFA _ q₀ _) w = delta' m (q₀, w)

corange ∷ (Finite q, Finite s) ⇒ NFA q s → Set (q, s)
corange m = qs m × sigma m

deltaToMap ∷ (Finite q, Finite s) ⇒ NFA q s → Map (q, s) (Set q)
deltaToMap m@(NFA δ _ _) = Map.fromSet δ (corange m)

range ∷ (Finite q, Finite s) ⇒ NFA q s → Set (Set q)
range m@(NFA δ _ _) = Set.map δ (corange m)

-- The transition table of the NFA
table ∷ (Finite q, Finite s) ⇒ NFA q s → [((q, s), Set q)]
table m = Map.toAscList (deltaToMap m)

-- The NFA, empty, such that
-- ℒ(empty) = ∅
empty ∷ NFA () s
empty = NFA { delta = const (∅)
            , q0    = ()
            , fs    = (∅)
            }

-- The NFA, epsilon, such that
-- ℒ(epsilon) = {ε}
epsilon ∷ NFA () s
epsilon = NFA { delta = const (∅)
              , q0    = ()
              , fs    = singleton ()
              }

-- Given a symbol, construct an NFA which recognizes exactly that symbol and nothing else
literal ∷ (Eq s) ⇒ s → NFA Bool s
literal σ' = NFA { delta = δ
                 , q0    = False
                 , fs    = singleton True
                 } where δ (False, σ) | σ == σ' = singleton True
                         δ _                    = (∅)

fromSet ∷ (Ord s) ⇒ Set s → NFA Bool s
fromSet s = NFA { delta = δ
                , q0    = False
                , fs    = singleton True
                } where δ (False, σ) | σ ∈ s = singleton True
                        δ _                  = (∅)

-- Avoid using `foldl` because the base case introduces more states than necessary, i.e.
-- `foldl (\(SomeNFA acc) σ → SomeNFA (concatenate acc (literal σ))) (SomeNFA epsilon)`
-- will concatenate the last symbol in the string with epsilon.
-- Could also just use `fromRE` instead... Confirm this way is better?
fromList ∷ (Eq s) ⇒ [s] → SomeNFA s
fromList []      = SomeNFA epsilon
fromList (σ : w) = fromNE (σ NE.:| w)

fromNE ∷ (Eq s) ⇒ NE.NonEmpty s → SomeNFA s
fromNE  w = foldl1 (\(SomeNFA acc) (SomeNFA σ) → SomeNFA (concatenate acc σ)) (fmap (SomeNFA . literal) w)

-- Given two NFAs m₁ and m₂, return an NFA which recognizes any string from
-- m₁ immediately followed by any string from m₂
concatenate ∷ (Ord q, Ord p) ⇒ NFA q s → NFA p s → NFA (Either q p) s
concatenate (NFA δ₁ q₀ f₁) (NFA δ₂ p₀ f₂) = NFA { delta = δ
                                                , q0    = Left q₀
                                                , fs    = Set.map Right f₂
                                                -- if this state, q, is a final state, merge q's transitions with p0's transitions
                                                } where δ (Left  q, σ) | q ∈ f₁ =               δ₁ (q, σ) ⊎ δ₂ (p₀, σ)  -- merge any last state of m₁ with p₀
                                                        δ (Left  q, σ)          = Set.map Left (δ₁ (q, σ))
                                                        δ (Right p, σ)          =            Set.map Right (δ₂ (p,  σ))

-- The product construction
-- Essentially this runs two NFAs (which both share the same alphabet) "in parallel" together in lock step
synchronous ∷ (Ord q, Ord p) ⇒ NFA q s → NFA p s → NFA (q, p) s
synchronous (NFA δ₁ q₀ f₁) (NFA δ₂ p₀ f₂) = NFA { delta = δ
                                                , q0    = (q₀, p₀)
                                                , fs    = f₁ × f₂
                                                } where δ ((q, p), σ) = δ₁ (q, σ) × δ₂ (p, σ)

-- The asynchronous product of two NFA
-- Essentially this runs two NFAs with different alphabets "in parallel" independently
asynchronous ∷ (Ord q, Ord p) ⇒ NFA q s → NFA p g → NFA (q, p) (Either s g)
asynchronous (NFA δ₁ q₀ f₁) (NFA δ₂ p₀ f₂) = NFA { delta = δ
                                                 , q0    = (q₀, p₀)
                                                 , fs    = f₁ × f₂
                                                 } where δ ((q, p), Left  σ) = δ₁ (q, σ)   × singleton p
                                                         δ ((q, p), Right γ) = singleton q × δ₂ (p, γ)

toFA ∷ (Finite q) ⇒ NFA q s → FA.FA q s
toFA (NFA δ q₀ f) = FA.FA { FA.delta   = δ
                          , FA.initial = singleton q₀
                          , FA.final   = f
                          }

minimize ∷ (Finite q, Finite s) ⇒ NFA q s → NFA (Set (Set q)) s
minimize = undefined -- fromJust . fromFA' . FA.minimize . toFA

-- Given an NFA, m, convert m to an equivalant EFA (which produces exactly the same language)
toEFA ∷ NFA q s → EFA.EFA q s
toEFA (NFA δ q₀ f) = EFA.EFA { EFA.delta = δₑ
                             , EFA.q0    = q₀
                             , EFA.fs    = f
                             } where δₑ (q, Just  σ) = δ (q, σ)
                                     δₑ (_, Nothing) = (∅)

-- Determinize the NFA without transforming it to a DFA
-- TODO test property that `determinisitic (NFA.determinization m)` is always true
-- TODO also test that ℒ(m) = ℒ(det(m))
determinization ∷ (Finite q) ⇒ NFA q s → NFA (Set q) s
determinization m@(NFA δ q₀ f) = NFA { delta = δ₁
                                     , q0    = singleton q₀
                                     , fs    = Set.filter (intersects f) (powerSet (qs m))
                                     } where δ₁ (states, σ) = Set.map (\q → δ (q, σ)) states

-- Take an EFA and generate an equivalent NFA (Stanford Coursera algo Nondeterminism lecture)
-- TODO also offer subset construction method?
fromEFA ∷ (Finite q) ⇒ EFA.EFA q s → NFA q s
fromEFA m@(EFA.EFA δ q₀ f) = NFA { delta = δₙ
                                 , q0    = q₀
                                 -- Any state which can reach a final state via epsilon transitions
                                 , fs    = Set.filter (intersects f . EFA.eclosure m . singleton) (qs m)
                                 } where δₙ (q, σ) = foldMap (\p → δ (p, Just σ)) (EFA.eclosure m (singleton q))

-- For testing if a particular sequence of moves will work
noEpsilonClosures ∷ (Finite q) ⇒ EFA.EFA q s → NFA q (Maybe s)
noEpsilonClosures (EFA.EFA δ q₀ f) = NFA { delta = δ
                                         , q0    = q₀
                                         , fs    = f
                                         }

fromFA ∷ (Finite q) ⇒ FA.FA q s → NFA (Either () q) s
fromFA = NFA.fromEFA . EFA.fromFA

-- If the FA only exactly one initial state then we may convert it to an NFA without adding an extra state
fromFA' ∷ FA.FA q s → Maybe (NFA q s)
fromFA' m | size' (FA.initial m) == 1 = Just NFA { delta = FA.delta m
                                                 , q0    = elemAt 0 (FA.initial m)
                                                 , fs    = FA.final m
                                                 }
          | otherwise                 = Nothing

toGraph ∷ ∀ q s . (Finite q) ⇒ NFA q s → TG.TG q s
toGraph (NFA δ _ _) = TG.TG (\s -> stars (fmap (\q → (q, Set.toList (δ (q, s)))) asList))

fromGraph ∷ (Finite s, Finite q) ⇒ TG.TG q s → q → Set q → NFA q s
fromGraph (TG.TG a) q₀ f = NFA { delta = δ
                               , q0    = q₀
                               , fs    = f
                               } where δ (q, s) = postSet q (a s)
