{-# LANGUAGE InstanceSigs, MultiParamTypeClasses,
    ExistentialQuantification, FlexibleInstances,
    GADTs,
    FlexibleContexts,
    ScopedTypeVariables,
    UnicodeSyntax #-}
{-# OPTIONS_GHC -Wall #-}

module DFA where

import           Data.Functor.Contravariant
import           Prelude             hiding (map)
import           Data.Set            as Set hiding (foldl, intersection)
import           Data.Set.Unicode
import           Data.Bool.Unicode
import qualified Data.Map            as Map
import           Common
import           Finite
import           Config
import           Algebra.Graph.Relation as Relation hiding (domain)
import qualified TG
import qualified NFA
import qualified EFA
import qualified GFA
import qualified RE
import qualified FA
-- import qualified PDA

-- Deterministic Finite Automaton
data DFA q s =                 -- q is the set of states, Q
                               -- s is the set of symbols Σ
     DFA { delta ∷ (q, s) → q  -- The (total) transition function, δ : Q × Σ → Q
         ,    q0 ∷ q           -- The initial state,               q₀ ∈ Q
         ,    fs ∷ Set q       -- The final states,                F ⊆ Q
         }

data SomeDFA s where
  SomeDFA ∷ (Show q, Finite q) ⇒ DFA q s → SomeDFA s

instance (Finite q) ⇒ Q (DFA q s) q
instance (Finite s) ⇒ Σ (DFA q s) s
instance (Finite s) ⇒ Σ (SomeDFA s) s

instance Contravariant (DFA q) where
  contramap ∷ (g → s) → DFA q s → DFA q g
  contramap h m@(DFA δ _ _) = m { delta = \(q, γ) → δ (q, h γ) }

instance Contravariant SomeDFA where
  contramap ∷ (g → s) → SomeDFA s → SomeDFA g
  contramap h (SomeDFA m) = SomeDFA (contramap h m)

instance (Show q, Finite q, Show s, Finite s) ⇒ Show (DFA q s) where
  show m@(DFA _ q₀ f) = "( Q  = " ++ (show . Set' . qs)    m ++
                      "\n, Σ  = " ++ (show . Set' . sigma) m ++
                      "\n, δ  : Q × Σ → Q"                   ++
                      "\n"        ++ (format . deltaToMap) m ++
                      "\n, q₀ = " ++  show  q₀               ++
                      "\n, F  = " ++ (show . Set' $ f)       ++ " )"

instance (Show s, Finite s) ⇒ Show (SomeDFA s) where
  show (SomeDFA m) = show m

instance (Finite q, Finite s) ⇒ Configuration DFA q s q where
  -- By construction of a DFA type this will be `True`
  deterministic ∷ DFA q s → Bool
  deterministic _ = True

  -- By construction of a DFA type this will be `True`
  complete      ∷ DFA q s → Bool
  complete      _ = True

  occupied ∷ DFA q s → q → Set q 
  occupied _ = singleton

  initial ∷ DFA q s → q
  initial (DFA _ q₀ _) = q₀

  final   ∷ DFA q s → Set q
  final   (DFA _ _  f) = f

  -- Given a DFA, m, and a configuration, return what it yields in one step
  (⊢) ∷ DFA q s → (q, [s]) → (q, [s])
  (⊢) _           (q,    []) = (q,        [])
  (⊢) (DFA δ _ _) (q, σ : w) = (δ (q, σ), w )

  -- Determine which states are accessible in the given DFA, i.e.
  -- { q ∈ Q | ∃w ∈ Σ★, δ★(q₀, w) = q }
  accessible ∷ DFA q s → Set q
  accessible m@(DFA _ q₀ _) = reachable m q₀
  
  -- δ★ : Q × Σ★ → Q
  -- "Extended delta" - The delta function extended from single symbols to strings (lists of symbols).
  -- Take a DFA and a starting state, q, for that DFA, then compute the state p such that δ★(q, w) = p
  delta' ∷ DFA q s → (q, [s]) → q
  delta' (DFA δ _ _) = uncurry (foldl (curry δ))

  -- δ′′ : P(Q) × Σ★ → P(Q)
  delta'' ∷ DFA q s → (Set q, [s]) → Set q
  delta'' (DFA δ _ _) = uncurry (foldl (\states σ → map (\q → δ (q,  σ)) states))

  -- Evaluate a string
  -- Take a DFA, m, and a string of symbols, w, and then compute the resulting state, q
  -- δ★(q₀, w) = q
  eval ∷ DFA q s → [s] → q
  eval m@(DFA _ q₀ _) w = delta' m (q₀, w)

  -- Take a DFA, m, and a string, w, and decide if that string is accepted/recognized
  -- m accepts a string w ∈ Σ★ iff δ★(q₀, w) ∈ F
  accepts ∷ DFA q s → [s] → Bool
  accepts m@(DFA _ _ f) w = eval m w ∈ f

  -- Take a DFA, m, and a string, w, and decide if that string is not accepted
  rejects ∷ DFA q s → [s] → Bool
  rejects m@(DFA _ _ f) w = eval m w ∉ f

-- Determine if a string, w, synchronizes (or "resets") a DFA, m
-- http://www.math.uni.wroc.pl/~kisiel/auto/eppstein.pdf
-- A string, w, "resets" a DFA when ∃w ∈ Σ★, ∀q ∈ Q, δ★(q, w) = p for some p ∈ Q
-- evaluate the same word from all states of Q, not just q₀
-- i.e. |{ δ★(q, w) | q ∈ Q }| = 1
synchronizes ∷ (Finite q, Finite s) ⇒ DFA q s → [s] → Bool
synchronizes m w = size' (delta'' m (qs m, w)) == 1

-- Lazily generate all the rejected strings of the given DFA
rejected ∷ (Finite q, Finite s) ⇒ DFA q s → [[s]]
rejected = language . complement

-- Brzozowski derivative
-- ∂σ(ℒ(m)) = { w | σw ∈ ℒ(m) }
derivative ∷ DFA q s → s → DFA q s
derivative m@(DFA δ q₀ _) σ = m { q0 = δ (q₀, σ) }

-- Brzozowski derivative extended to strings
derivative' ∷ (Finite q, Finite s) ⇒ DFA q s → [s] → DFA q s
derivative' m wrt           = m { q0 = eval m wrt }

-- The "right language" of m wrt some state q
right ∷ DFA q s → q → DFA q s
right m q = m { q0 = q }

-- The "left language" of q
left ∷ DFA q s → q → DFA q s
left m q = m { fs = singleton q }

-- Two states having the same right language are indistinguishable
-- they both lead to the same words being accepted.
indistinguishable ∷ (Finite q, Finite s) ⇒ DFA q s → q → q → Bool
indistinguishable m q p = right m q `DFA.equal` right m p

-- The equivalence relation formed on Q by indistinguishable states for m
indistinguishability ∷ (Finite q, Finite s) ⇒ DFA q s → Equivalence q
indistinguishability m = Equivalence { getEquivalence = indistinguishable m }

-- Given two states, q₁ and q₂, determine the (possibly empty) set of
-- symbols which will take you directly from q₁ to q₂
transitions ∷ (Eq q, Finite s) ⇒ DFA q s → q → q → Set s
transitions m@(DFA δ _ _) q₁ q₂ = foldl (\acc σ → if δ (q₁, σ) == q₂ then insert σ acc else acc) (∅) (sigma m)

corange ∷ (Finite q, Finite s) ⇒ DFA q s → Set (q, s)
corange m = qs m × sigma m

deltaToMap ∷ (Finite q, Finite s) ⇒ DFA q s → Map.Map (q, s) q
deltaToMap m@(DFA δ _ _) = Map.fromSet δ (corange m)

-- The transition table of the DFA's δ function
table ∷ (Finite q, Finite s) ⇒ DFA q s → [((q, s), q)]
table m = Map.toAscList (deltaToMap m)

-- ℒ(m) is cofinite in Σ★ iff the complement of ℒ(m) (in Σ★) is finite.
cofinite ∷ (Finite q, Finite s) ⇒                       DFA q s → Bool
cofinite = finite . complement

codeterministic ∷ (Finite q, Finite s) ⇒                DFA q s → Bool
codeterministic = undefined -- m = deterministic (toFAReverse m)

-- Bideterministic automata are deterministic automata with
-- the property of their reversal automata also being deterministic.
-- An automaton M is called bideterministic if both M and its reversal automaton, Mʳ, are deterministic
bideterministic ∷ (Finite q, Finite s) ⇒                DFA q s → Bool
bideterministic m = deterministic m  ∧  codeterministic m

-- Theorem (Cerny, 1964): A DFA M is (directable) synchronizing iff ∀q ∈ Q, ∃p ∈ Q, ∃w ∈ Σ★: δ(q,w) = δ(p, w)
-- That is, there exists a word w, such that evaluation of w from from any state, q, always ends up in the same state, p.
synchronizing ∷ (Finite q, Finite s) ⇒                  DFA q s → Bool
synchronizing = not . isZero . power
          where power ∷ (Finite q) ⇒ DFA q s → DFA (Set q) s -- FIXME supposed to be a non-empty set -- TODO alter this to check for shortest path to get shortest reset word?
                power m@(DFA δ _ _) = DFA { delta = \(states, σ) → map (\q → δ (q, σ)) states
                                          , q0    = qs m
                                          , fs    = map singleton (qs m)
                                          }

-- A palindrome is a word w such that w = wʳ.
-- Let ℒ ⊆ Σ★, ℒ is palindromic if every word w ∈ ℒ is a palindrome.
-- ℒ(M) is palindromic if and only if { x ∈ ℒ(M) : |x| < 3n } is
-- palindromic, where n is the number of states of M.
-- TODO this is the (untested) naive implementation
palindromic ∷ (Finite q, Finite s) ⇒                    DFA q s → Bool
palindromic m = all palindrome (upToLength (3 * n) (language m))
          where n = size' (qs m)

-- Given two DFAs, decide if they produce the exact same language, i.e.
-- ℒ(m₁) ≟ ℒ(m₂)
equal ∷ (Finite q, Finite p, Finite s) ⇒      DFA q s → DFA p s → Bool
equal     m₁ m₂ = contained m₁ m₂ ∧ contained m₂ m₁

-- Given two DFAs, m₁ and m₂, decide if ℒ(m₁) ⊆ ℒ(m₂)
contained ∷ (Finite q, Finite p, Finite s) ⇒  DFA q s → DFA p s → Bool
contained m₁ m₂ = isZero   (m₁ `intersection` complement m₂)

-- Given two DFAs, m₁ and m₂,
-- ℒ(m₁) ∩ ℒ(m₂) ≟ ∅
disjoint ∷ (Finite q, Finite p, Finite s) ⇒   DFA q s → DFA p s → Bool
disjoint  m₁ m₂ = isZero   (m₁ `intersection` m₂)

-- Given two DFAs, m₁ and m₂,
-- ℒ(m₁) ∩ ℒ(m₂) ≠ ∅?
intersects ∷ (Finite q, Finite p, Finite s) ⇒ DFA q s → DFA p s → Bool
intersects m₁ m₂ = not (DFA.disjoint m₁ m₂)

-- The difference of two DFAs, m₁ and m₂, produces a new DFA, m₃, such that
-- ℒ(m₃) = ℒ(m₁) − ℒ(m₂)
difference ∷ (Finite q, Finite p) ⇒   DFA q s → DFA p s → DFA (q, p) s
difference m₁@(DFA _ _ f₁) m₂@(DFA _ _ f₂) = (synchronous m₁ m₂) { fs = Set.filter (\(q, p) → (q ∈ f₁) ∧ (p ∉ f₂)) (qs m₁ × qs m₂) }

-- The union of two DFAs, m₁ and m₂, produces a new DFA, m₃, such that
-- ℒ(m₃) = ℒ(m₁) ∪ ℒ(m₂)
-- F = (F₁ × Q₁) ∪ (Q₂ × F₂)
union ∷ (Finite q, Finite p) ⇒        DFA q s → DFA p s → DFA (q, p) s
union      m₁@(DFA _ _ f₁) m₂@(DFA _ _ f₂) = (synchronous m₁ m₂) { fs = Set.filter (\(q, p) → (q ∈ f₁) ∨ (p ∈ f₂)) (qs m₁ × qs m₂) }

-- The instersection of two DFAs, m₁ and m₂, produces a new DFA, m₃, such that
-- ℒ(m₃) = ℒ(m₁) ∩ ℒ(m₂)
intersection ∷ (Ord q, Ord p) ⇒       DFA q s → DFA p s → DFA (q, p) s
intersection = synchronous

-- The product construction
-- Essentially this runs two DFAs (which both share the same alphabet) "in parallel" together in lock step
synchronous ∷ (Ord q, Ord p) ⇒        DFA q s → DFA p s → DFA (q, p) s
synchronous (DFA δ₁ q₀ f₁) (DFA δ₂ p₀ f₂) = DFA { delta = δ
                                                , q0    = (q₀, p₀)
                                                , fs    = f₁ × f₂
                                                } where δ ((q, p), σ) = (δ₁ (q, σ), δ₂ (p, σ))

-- The asynchronous product of two DFA
-- Essentially this runs two DFAs with different alphabets "in parallel" independently
asynchronous ∷ (Ord q, Ord p) ⇒ DFA q s → DFA p g → DFA (q, p) (Either s g)
asynchronous (DFA δ₁ q₀ f₁) (DFA δ₂ p₀ f₂) = DFA { delta = δ
                                                 , q0    = (q₀, p₀)
                                                 , fs    = f₁ × f₂
                                                 } where δ ((q, p), Left  σ) = (δ₁ (q, σ), p        )
                                                         δ ((q, p), Right γ) = (q,         δ₂ (p, γ))

-- The symmetric difference ("exclusive or", or "xor") of two DFAs such that
-- ℒ(m₁) ⊕ ℒ(m₂) = (ℒ(m₁) - ℒ(m₂)) ∪ (ℒ(m₂) - ℒ(m₁))
xor ∷ (Finite q, Finite p, Finite (q, p), Finite (p, q)) ⇒ DFA q s → DFA p s → DFA ((q, p), (p, q)) s
xor m₁ m₂ = DFA.difference m₁ m₂ `DFA.union` DFA.difference m₂ m₁

-- ℒʳ
reversal ∷ (Finite q, Finite s) ⇒ DFA q s → DFA (Set q) s
reversal = DFA.fromFA . FA.reversal . toFA

-- ℒ(m₁)/ℒ(m₂) = { w | wx ∈ ℒ(m₁)  ∧  x ∈ ℒ(m₂) }
rquotient ∷ (Finite q, Finite p, Finite s) ⇒ DFA q s → DFA p s → DFA q s
rquotient m₁ m₂ = m₁ { fs = Set.filter (DFA.intersects m₂ . right m₁) (qs m₁) }

-- min(ℒ(m)) = ℒ(m) - ℒ(m)·Σ⁺ = { w | w ∈ ℒ(m) ∧ no proper prefix of w is in ℒ(m) }
-- a proper prefix of a string is a prefix of the string not empty and not equal to itself
min ∷ (Ord q) ⇒ DFA q s → DFA (Either () q) s
min (DFA δ q₀ f) = DFA { delta = δ₁
                       , q0    =         Right q₀
                       , fs    = Set.map Right f
                       } where δ₁ (Left (), _)         = Left ()          -- `Left ()` is a dead state with no way to transition out
                               δ₁ (Right q, _) | q ∈ f = Left ()          -- delete transitions out of final states by sending to the new dead state
                               δ₁ (Right q, σ)         = Right (δ (q, σ))

-- max(ℒ(m)) = { w | w ∈ ℒ(m) ∧ ∀x ≠ ε, wx ∉ ℒ(m) }
max ∷ (Finite q, Finite s) ⇒ DFA q s → DFA q s -- delete q because x cannot be ε
max m@(DFA _ _ f) = m { fs = Set.filter (\q → any (∈ delete q (reachable m q)) f) f }

-- Init(ℒ) = ℒ − (ℒ ∩ ℒΣ⁺) = { w ∈ Σ★ | wy ∈ ℒ for some y ∈ Σ★ }
-- F = { q | ∃w.δ★(q, w) ∈ F }
-- "Given a DFA M for ℒ, make each state q final if there is a path from q to a final state in the original machine"
init ∷ (Finite q, Finite s) ⇒ DFA q s → DFA q s
init m = m { fs = coaccessible m }

-- Given a DFA, m, return a new DFA, m', which recognizes only the rejected strings of m
-- such that ℒ(m') = Σ★ ∖ ℒ(m)
complement ∷ (Finite q) ⇒ DFA q s → DFA q s
complement m@(DFA _ _ f) = m { fs = qs m ∖ f }

-- Brzozowski minimization
-- Here we convert to FA to avoid introducing a new state with ε-transitions while reversing
-- The number of states, i.e. `size' (qs m)`, will increase but the number of accessible states will stay the same or decrease
-- N.B. `fromFA` performs the last determinization
-- TODO testme
-- FIXME need to map `(Set (Set q))` back down to `q` or smaller
minimize ∷ (Finite q, Finite s) ⇒ DFA q s → DFA (Set (Set q)) s
minimize = DFA.fromFA . FA.codeterminization . toFA

-- The DFA, empty, which produces the empty language, such that
-- ℒ(empty) = ∅
empty ∷ DFA () s
empty = DFA { delta = const ()
            , q0    = ()
            , fs    = (∅)
            }

-- The DFA, epsilon, which produces the language, such that
-- ℒ(epsilon) = {ε}
epsilon ∷ DFA Bool s
epsilon = DFA { delta = const False
              , q0    = True
              , fs    = singleton True
              }

-- Given a symbol of an alphabet, σ ∈ Σ, construct a DFA which recognizes only that symbol and nothing else, i.e.
-- ℒ(m) = {σ}
literal ∷ (Eq s) ⇒ s → DFA (Either () Bool) s
literal σ = DFA { delta = Right . δ
                , q0    = Left ()
                , fs    = singleton (Right True)
                } where δ (Left (), σ') = σ' == σ
                        δ _             = False

fromSet ∷ (Ord s) ⇒ Set s → DFA (Either () Bool) s
fromSet s = DFA { delta = Right . δ
                , q0    = Left ()
                , fs    = singleton (Right True)
                } where δ (Left (), σ) = σ ∈ s
                        δ _            = False

-- TODO untested
toSet ∷ (Finite q, Finite s) ⇒ DFA q s → Set s
toSet m@(DFA δ _ _) = foldMap (\(q, σ) → if δ (q, σ) ∈ useful m then singleton σ else (∅)) (useful m × sigma m)

dot ∷ (Finite s) ⇒ DFA (Either () Bool) s
dot = fromSet asSet

-- Convert an NFA with multiple start states to a DFA (performs determinization)
fromFA ∷ (Finite q) ⇒ FA.FA q s → DFA (Set q) s
fromFA m@(FA.FA δ i f) = DFA { delta = \(states, σ) → foldMap (\q → δ (q, σ)) states
                             , q0    = i
                             , fs    = Set.filter (Common.intersects f) (powerSet (qs m))
                             }

fromCDFA ∷ (Finite q, Finite s) ⇒ FA.FA q s → Maybe (DFA q s)
fromCDFA m@(FA.FA δ i f) | complete m && deterministic m = Just (DFA { delta = \(q, σ) → elemAt 0 (δ (q, σ))
                                                                     , q0 = elemAt 0 i
                                                                     , fs = f
                                                                     }
                                                                )
fromCDFA _                                               = Nothing

-- Take an NFA, and use subset construction to convert it to an equivalent DFA (performs determinization)
fromNFA ∷ (Finite q) ⇒ NFA.NFA q s → DFA (Set q) s
fromNFA m@(NFA.NFA δ q₀ f) = DFA { delta = \(states, σ) → foldMap (\q → δ (q, σ)) states
                                 , q0    = singleton q₀
                                 , fs    = Set.filter (Common.intersects f) (powerSet (qs m))
                                 }

-- Take an EFA and use (slightly modded (See (2.) page 77, HMU)) subset construction
-- to generate an equivalent DFA by "eliminating" epsilon transitions
fromEFA ∷ (Finite q) ⇒ EFA.EFA q s → DFA (Set q) s
fromEFA = fromNFA . NFA.fromEFA

toFAReverse ∷ (Finite s, Finite q) ⇒ DFA q s → FA.FA q s
toFAReverse = FA.reversal . toFA

-- Take a DFA, d, and convert it to an NFA, n, such that ℒ(d) = ℒ(n)
toNFA ∷ DFA q s → NFA.NFA q s
toNFA (DFA δ q₀ f) = NFA.NFA { NFA.delta = singleton . δ
                             , NFA.q0    = q₀
                             , NFA.fs    = f
                             }

-- min(ℒ(m)) = ℒ(m) - ℒ(m)·Σ⁺ = { w | w ∈ ℒ(m) ∧ no proper prefix of w is in ℒ(m) }
-- a proper prefix of a string is a prefix of the string not empty and not equal to itself
toNFAMin ∷ (Ord q) ⇒ DFA q s → NFA.NFA q s
toNFAMin m@(DFA δ _ f) = (toNFA m) { NFA.delta = δ₁ }
                   where δ₁ (q, _) | q ∈ f = (∅)  -- delete transitions out of final states
                         δ₁ (q, σ)         = singleton (δ (q, σ))

-- Convert the DFA to its Transition Graph.
-- N.B. information is lost in this conversion, i.e. q₀ and F will be dropped
toGraph ∷ ∀ q s . (Finite q) ⇒ DFA q s → TG.TG q s
toGraph (DFA δ _ _) = TG.TG (\s → fromAdjacencyList (fmap (\q → (q, [δ (q, s)])) asList))

-- Take a DFA, d, and convert it to an EFA, e, such that ℒ(d) = ℒ(e)
toEFA ∷ DFA q s → EFA.EFA q s
toEFA = NFA.toEFA . toNFA

-- cycle(ℒ) = { xy | yx ∈ ℒ }
-- A Second Course in Formal Languages and Automata Theory pg. 60
-- string conjugations
toEFACycle ∷ (Finite q) ⇒ DFA q s → EFA.EFA (Either () (q, q, Bool)) s
toEFACycle m@(DFA δ q₀ f) = EFA.EFA { EFA.delta = δ₁
                                    , EFA.q0    = Left ()
                                    , EFA.fs    = Set.map (\q → Right (q, q, True)) (qs m)
                                    } where δ₁ (Left             (), Nothing)         = Set.map (\q → Right (q, q, False)) (qs m)
                                            δ₁ (Right (q, p, False), Nothing) | q ∈ f = singleton (Right (q₀      , p, True))
                                            δ₁ (Right (q, p,     b), Just  σ)         = singleton (Right (δ (q, σ), p, b   )) -- Simulation
                                            δ₁ _                                      = (∅)

-- ½ℒ = { x ∈ Σ★ : there exists y ∈ Σ★ with |y| = |x| such that xy ∈ ℒ }.
-- A Second Course in Formal Languages and Automata Theory pg. 59
-- for all even length strings w ∈ ℒ, take the first half of w, producing ½ℒ
toEFAHalf ∷ forall q s . (Finite q, Finite s) ⇒ DFA q s → EFA.EFA (Either () (q, q, q)) s
toEFAHalf m@(DFA δ q₀ f) = EFA.EFA { EFA.delta = δ₁
                                   , EFA.q0    = Left ()
                                   , EFA.fs    = Set.map (\(q, qᶠ) → Right (q, q, qᶠ)) (qs m × f)
                                   } where δ₁ (Left         (), Nothing) = Set.map (\q  → Right (q,       q₀,         q)) (qs m)
                                           δ₁ (Right (q, p, r), Just  σ) = Set.map (\σ' → Right (q, δ (p, σ), δ (r, σ'))) (sigma m)
                                           δ₁ _                          = (∅)

toFA ∷ (Finite q) ⇒ DFA q s → FA.FA q s
toFA = NFA.toFA . toNFA

toGFA ∷ (Finite s, Ord q) ⇒ DFA q s → GFA.GFA q s
toGFA m@(DFA _ q₀ f) = GFA.GFA { GFA.delta = δ }
     where
       -- Connect the new (forced) GFA start state to q₀ with an epsilon.
       δ (Left  (Init ()), Right          p) | p == q₀ = RE.one
       -- Connect the new (forced) GFA final state to each element of f with an epsilon.
       δ (Right         q, Left  (Final ())) | q ∈ f   = RE.one
       -- If q and p were connected (often via multiple transitions) in the DFA,
       -- lift all symbols into RE.Lit, and let multiple transitions be represented
       -- by the union of said literals. If no transitions between q and p in DFA then, RE.zero.
       δ (Right         q, Right          p)           = RE.fromSet (transitions m q p)
       -- Besides the explicitly given epsilon connections, no connections
       -- to the new final state nor from the new start state should exist.
       δ _                                             = RE.zero

toRE ∷ (Finite q, Finite s) ⇒ DFA q s → RE.RegExp s
toRE = GFA.toRE . toGFA

{-
-- Take a DFA, m, and convert it to an PDA, p, such that ℒ(m) = ℒ(p)
toPDA ∷ DFA q s → PDA.PDA q () s
toPDA (DFA δ q₀ f) = PDA.PDA { PDA.delta = δₚ
                             , PDA.q0    = q₀
                             , PDA.fs    = f
                             , PDA.z0    = ()
                             } where δₚ (q, Just  σ, _) = singleton (δ (q, σ), [()])
                                     δₚ (_, Nothing, _) = (∅)

-- http://infolab.stanford.edu/~ullman/ialc/spr10/slides/cfl5.pdf 34
-- Stanford Automata, 4 - 3 - 15. Decision and closure properties for CFL-'s (35 min.).mp4 @ 34:00
-- Intuitively this runs a PDA and DFA in parallel and accepts a word if both accept individually.
toPDAIntersection ∷ ∀ q p s z . (Ord p, Ord q, Ord z) ⇒ DFA q s → PDA.PDA p z s → PDA.PDA (q, p) z s
toPDAIntersection (DFA δ q₀ f) (PDA.PDA δₚ p₀ z₀ fₚ) = PDA.PDA { PDA.delta = δ₁
                                                               , PDA.q0    = (q₀, p₀)
                                                               , PDA.z0    = z₀
                                                               -- The final states are (q, p) such that q ∈ f and p ∈ fₚ
                                                               , PDA.fs    = f × fₚ
                                                               } where δ₁ ∷ ((q, p), Maybe s, z) → Set ((q, p), [z])
                                                                       δ₁ ((q, p), Nothing, z) = Set.map (\(p', zs) → ((q,        p'), zs)) (δₚ (p, Nothing, z))
                                                                       δ₁ ((q, p), Just  σ, z) = Set.map (\(p', zs) → ((δ (q, σ), p'), zs)) (δₚ (p, Just  σ, z))
-}                                                                       
