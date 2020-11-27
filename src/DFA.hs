{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wall                  #-}

module DFA where

import           Algebra.Graph.Relation as Relation hiding (domain)
import           Data.Bool (bool)
import           Data.Functor.Contravariant (Contravariant, contramap, Equivalence (..), Predicate (..))
import           Data.Function (on)
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty  as NE
import qualified Data.List           as List
import qualified Data.Map            as Map
import           Data.Set            as Set hiding (foldl, intersection)
import           Data.Set.Unicode ((∅), (∈), (∉), (∖), (∪))
import           Data.Bool.Unicode ((∧), (∨))
import           Numeric.Algebra.Class (sumWith)
import           Prelude             hiding (map)
import           Common
import           Finite
import           Config
import qualified TransitionGraph as TG
import qualified NFA
import qualified EFA
import qualified GNFA
import qualified FA
import qualified DA
import qualified RegExp as RE
import           Language (ℒ)

-- Deterministic Finite Automaton
data DFA q s =                 -- q is the set of states, Q
                               -- s is the set of symbols Σ
     DFA { delta ∷ (q, s) → q  -- The (total) transition function, δ : Q × Σ → Q
         ,    q0 ∷ q           -- The initial state,               q₀ ∈ Q
         ,    fs ∷ Set q       -- The final states,                F ⊆ Q
         }

-- A DFA constructor where the `q` type parameter is an existential
data SomeDFA s where
  SomeDFA ∷ (Show q, Finite q) ⇒ DFA q s → SomeDFA s

instance (Finite q) ⇒ Q (DFA q s) q
instance (Finite s) ⇒ Σ (DFA q s) s
instance (Finite s) ⇒ Σ (SomeDFA s) s

instance Contravariant (DFA q) where
  contramap ∷ (s → g) → DFA q g → DFA q s
  -- contramap h (DFA δ q₀ f) = DFA (\(q, σ) →              δ (q, h σ)) q₀ f
  contramap h (DFA δ q₀ f) = DFA (\(q, σ) →       (curry δ) q (h σ)) q₀ f

invhomimage ∷ (s → [g]) → DFA q g → DFA q s
invhomimage h (DFA δ q₀ f) = DFA (\(q, σ) → foldl (curry δ) q (h σ)) q₀ f

instance Contravariant SomeDFA where
  contramap ∷ (g → s) → SomeDFA s → SomeDFA g
  contramap h (SomeDFA m) = SomeDFA (contramap h m)

instance (Show q, Finite q, Show s, Finite s) ⇒ Show (DFA q s) where
  show ∷ DFA q s → String
  show m = quoteWith "( " " )" $ List.intercalate "\n, "
           [ equation "Q "              ((show . Set' . qs   ) m)
           , equation "Σ "              ((show . Set' . sigma) m)
           , quoteWith "δ  : Q × Σ → Q" ((format . deltaToMap) m) "\n"
           , equation "q₀"              ((show . q0          ) m)
           , equation "F "              ((show . Set' . fs   ) m)
           ]

instance (Show s, Finite s) ⇒ Show (SomeDFA s) where
  show ∷ SomeDFA s → String
  show (SomeDFA m) = show m

instance (Finite q, Finite s) ⇒ Configuration DFA q s q where
  -- By construction of a DFA type this will be `True`
  deterministic ∷ DFA q s → Bool
  deterministic   = const True

  codeterministic ∷ DFA q s → Bool
  codeterministic = deterministic . FA.reversal . toFA

  -- By construction of a DFA type this will be `True`
  complete      ∷ DFA q s → Bool
  complete        = const True

  occupied ∷ DFA q s → q → Set q 
  occupied = const singleton

  deltaD  ∷ DFA q s → ((q, s) → q)
  deltaD  = delta

  initial ∷ DFA q s → q
  initial = q0

  final   ∷ DFA q s → Set q
  final   = fs

  -- Given a DFA, m, and a configuration, return what it yields in one step
  (⊢) ∷ DFA q s → (q, [s]) → (q, [s])
  (⊢) _           (q,     []) = (   q    , [])
  (⊢) (DFA δ _ _) (q, σ : w ) = (δ (q, σ), w )

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

  -- trace δ★(q, w)
  traced ∷ DFA q s → [s] → (q, [(q, s)])
  traced (DFA δ q₀ _) = List.mapAccumL (\q σ → (δ (q, σ), (q, σ))) q₀

  -- Take a DFA, m, and a string, w, and decide if that string is accepted/recognized
  -- m accepts a string w ∈ Σ★ iff δ★(q₀, w) ∈ F
  accepts ∷ DFA q s → [s] → Bool
  accepts m@(DFA _ _ f) w = eval m w ∈ f

  -- Take a DFA, m, and a string, w, and decide if that string is not accepted
  rejects ∷ DFA q s → [s] → Bool
  rejects m@(DFA _ _ f) w = eval m w ∉ f

  -- Convert the DFA to its Transition Graph.
  -- N.B. information is lost in this conversion, i.e. q₀ and F will be dropped
  toGraph ∷ DFA q s → TG.TG q s
  toGraph (DFA δ _ _) = TG.TG (\s → stars (fmap (\q → (q, [δ (q, s)])) asList))

-- Determine if a string, w, synchronizes (or "resets") a DFA, m
-- http://www.math.uni.wroc.pl/~kisiel/auto/eppstein.pdf
-- A string, w, "resets" a DFA when ∃w ∈ Σ★, ∀q ∈ Q, δ★(q, w) = p for some p ∈ Q
-- evaluate the same word from all states of Q, not just q₀
-- i.e. |{ δ★(q, w) | q ∈ Q }| = 1
synchronizes ∷ (Finite q, Finite s) ⇒ DFA q s → [s] → Bool
-- synchronizes m w = size' (delta'' m (qs m, w)) == 1
synchronizes m w = (==) 1 (size' (delta'' m (qs m, w)))

-- Lazily generate all the rejected strings of the given DFA
rejected ∷ (Finite q, Finite s) ⇒ DFA q s → [[s]]
rejected = language . complement

-- TODO can delete this because it is redundant given `eval` already defined,
-- TODO however for now I'm keeping it for reference
evaluate ∷ DFA q s → [s] → q
evaluate (DFA δ q₀ _) w =    foldl (curry δ) q₀ w

-- Trace the path the DFA takes for a word
trace ∷ DFA q s → [s] → NonEmpty q
trace    (DFA δ q₀ _) w = NE.scanl (curry δ) q₀ w

-- Brzozowski derivative
-- ∂σ(ℒ(m)) = { w | σw ∈ ℒ(m) }
derivative ∷ DFA q s → s → DFA q s
derivative  (DFA δ q₀ f) σ = DFA δ (      (curry δ) q₀ σ) f

-- Brzozowski derivative extended to strings
derivative' ∷ (Finite q, Finite s) ⇒ DFA q s → [s] → DFA q s
derivative' (DFA δ q₀ f) w = DFA δ (foldl (curry δ) q₀ w) f

-- The "right language" of m wrt some state q
right ∷ DFA q s → q → DFA q s
right (DFA δ _ f) q = DFA δ q f

-- The "left language" of q
left ∷ DFA q s → q → DFA q s
left (DFA δ q₀ _) = DFA δ q₀ . singleton

-- The equivalence relation formed on Q by indistinguishable states for m
-- Two states having the same right language are indistinguishable
-- they both lead to the same words being accepted.
indistinguishability ∷ (Finite q, Finite s) ⇒ DFA q s → Equivalence q
indistinguishability = Equivalence . (DFA.equal `on`) . right

domain ∷ (Finite q, Finite s) ⇒ DFA q s → Set (q, s)
domain m = qs m × sigma m

deltaToMap ∷ (Finite q, Finite s) ⇒ DFA q s → Map.Map (q, s) q
deltaToMap m@(DFA δ _ _) = Map.fromSet δ (domain m)

-- The transition table of the DFA's δ function
table ∷ (Finite q, Finite s) ⇒ DFA q s → [((q, s), q)]
table = Map.toAscList . deltaToMap

-- ℒ(m) is cofinite in Σ★ iff the complement of ℒ(m) (in Σ★) is finite.
cofinite ∷ (Finite q, Finite s) ⇒ Predicate (DFA q s)
cofinite = Predicate (finite . complement)

-- Theorem (Cerny, 1964): A DFA M is (directable) synchronizing iff ∀q ∈ Q, ∃p ∈ Q, ∃w ∈ Σ★: δ(q,w) = δ(p, w)
-- That is, there exists a word w, such that evaluation of w from from any state, q, always ends up in the same state, p.
-- "A DFA is synchronizing if there exists a word that sends all states of the automaton to the same state." - https://arxiv.org/abs/1507.06070
synchronizing ∷ (Finite q, Finite s) ⇒ Predicate (DFA q s)
synchronizing = Predicate (not . isZero . power)
  where
    -- FIXME supposed to be a non-empty set
    power ∷ (Finite q) ⇒ DFA q s → DFA (Set q) s -- TODO alter this to check for shortest path to get shortest reset word?
    power m@(DFA δ _ _) = DFA (\(states, σ) → map (\q → δ (q, σ)) states) (qs m) (map singleton (qs m))

-- A palindrome is a word w such that w = wʳ.
-- Let ℒ ⊆ Σ★, ℒ is palindromic if every word w ∈ ℒ is a palindrome.
-- ℒ(M) is palindromic if and only if { x ∈ ℒ(M) : |x| < 3n } is
-- palindromic, where n is the number of states of M.
-- TODO this is the (untested) naive implementation
palindromic ∷ (Finite q, Finite s) ⇒ Predicate (DFA q s)
palindromic = Predicate (\m → all palindrome (upToLength (3 * size' (qs m)) (language m)))

-- An automaton M = (S, I, δ, s₀, F) is said to be a permutation
-- automaton, or more simply a p-automaton, if and only if δ(sᵢ, a) = δ(sⱼ, a), where sᵢ, sⱼ ∈ S, a ∈ I, implies that sᵢ = sⱼ.
-- Permutation Automata by G. THIERRIN
-- TODO untested
-- TODO better to place in src/FA.hs?
permutation ∷ (Finite q, Finite s) ⇒ Predicate (DFA q s)
permutation = Predicate (\m@(DFA δ _ _) → all (\(qᵢ, qⱼ) →
                                                all (\σ → (δ (qᵢ, σ) == δ (qⱼ, σ)) `implies` (qᵢ == qⱼ)) (sigma m)
                                              ) (qs m × qs m))

-- Given two DFAs, decide if they produce the exact same language, i.e.
-- ℒ(m₁) ≟ ℒ(m₂)
equal ∷ (Finite q, Finite p, Finite s) ⇒      DFA q s → DFA p s → Bool
equal m₁ m₂ = contained m₁ m₂ ∧ contained m₂ m₁

-- Given two DFAs, m₁ and m₂, decide if ℒ(m₁) ⊆ ℒ(m₂)
contained ∷ (Finite q, Finite p, Finite s) ⇒  DFA q s → DFA p s → Bool
contained m = isZero . intersection m . complement

-- Given two DFAs, m₁ and m₂,
-- ℒ(m₁) ∩ ℒ(m₂) ≟ ∅
disjoint ∷ (Finite q, Finite p, Finite s) ⇒   DFA q s → DFA p s → Bool
disjoint = isZero ‥ intersection

-- Given two DFAs, m₁ and m₂,
-- ℒ(m₁) ∩ ℒ(m₂) ≠ ∅?
intersects ∷ (Finite q, Finite p, Finite s) ⇒ DFA q s → DFA p s → Bool
intersects = not ‥ DFA.disjoint

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
synchronous (DFA δ₁ q₀ f₁) (DFA δ₂ p₀ f₂) = DFA (\((q, p), σ) → (δ₁ (q, σ), δ₂ (p, σ))) (q₀, p₀) (f₁ × f₂)

-- The asynchronous product of two DFA
-- Essentially this runs two DFAs with different alphabets "in parallel" independently
asynchronous ∷ ∀ q p s g . (Ord q, Ord p) ⇒ DFA q s → DFA p g → DFA (q, p) (Either s g)
asynchronous (DFA δ₁ q₀ f₁) (DFA δ₂ p₀ f₂) = DFA δ (q₀, p₀) (f₁ × f₂)
  where
    δ ∷ ((q, p), Either s g) → (q, p)
    δ ((q, p), Left  σ) = (δ₁ (q, σ), p        )
    δ ((q, p), Right γ) = (q,         δ₂ (p, γ))

perfectShuffle ∷ ∀ q p s . (Ord q, Ord p) ⇒ DFA q s → DFA p s → DFA (q, p, Bool) s
perfectShuffle (DFA δ₁ q₀ f₁) (DFA δ₂ p₀ f₂) = DFA δ (q₀, p₀, False) (Set.map (\(q, p) → (q, p, False)) (f₁ × f₂))
  where
    δ ∷ ((q, p, Bool), s) → (q, p, Bool)
    δ ((q, p, False), σ) = (δ₁ (q, σ),     p    , True )
    δ ((q, p, True ), σ) = (    q    , δ₂ (p, σ), False)

{-
import qualified Data.Can as Can (Can (..))
import           Data.Can

-- FIXME rename, consider https://lotsofwords.com/*chronous
asdf1 ∷ ∀ q p s g . (Ord q, Ord p) ⇒ DFA q s → DFA p g → DFA (q, p) (Can s g)
asdf1 (DFA δ₁ q₀ f₁) (DFA δ₂ p₀ f₂) = DFA δ (q₀, p₀) (f₁ × f₂)
  where
    δ ∷ ((q, p), Can s g) → (q, p)
    δ ((q, p),  Can.Non     ) = (q,         p        )
    δ ((q, p), (Can.One σ  )) = (δ₁ (q, σ), p        )
    δ ((q, p), (Can.Eno   γ)) = (q,         δ₂ (p, γ))
    δ ((q, p), (Can.Two σ γ)) = (δ₁ (q, σ), δ₂ (p, γ))

asdf2 ∷ ∀ q p s g . (Ord q, Ord p) ⇒ DFA q s → DFA p s → DFA (Can q p) s
asdf2 (DFA δ₁ q₀ f₁) (DFA δ₂ p₀ f₂) = DFA δ (Can.Two q₀ p₀) (Set.map (uncurry Can.Two) (f₁ × f₂))
  where
    δ ∷ (Can q p, s) → Can q p
    δ (Can.Non    , _) = Can.Non
    δ (Can.One q  , σ) = Can.One (δ₁ (q, σ))
    δ (Can.Eno   p, σ) = Can.Eno             (δ₂ (p, σ))
    δ (Can.Two q p, σ) = Can.Two (δ₁ (q, σ)) (δ₂ (p, σ))
-}

-- The symmetric difference ("exclusive or", or "xor") of two DFAs
-- ℒ(m₁) ⊕ ℒ(m₂) = (ℒ(m₁) - ℒ(m₂)) ∪ (ℒ(m₂) - ℒ(m₁))
xor ∷ (Finite q, Finite p) ⇒ DFA q s → DFA p s → DFA ((q, p), (p, q)) s
xor m₁ m₂ = DFA.difference m₁ m₂ `DFA.union` DFA.difference m₂ m₁

-- ℒʳ
reversal ∷ (Finite q, Finite s) ⇒ DFA q s → DFA (Set q) s
reversal = DFA.fromFA . FA.reversal . toFA

-- ℒ(m₁)/ℒ(m₂) = { w | wx ∈ ℒ(m₁)  ∧  x ∈ ℒ(m₂) }
rquotient ∷ (Finite q, Finite p, Finite s) ⇒ DFA q s → DFA p s → DFA q s
rquotient m₁ m₂ = m₁ { fs = Set.filter (DFA.intersects m₂ . right m₁) (qs m₁) }

-- min(ℒ(m)) = ℒ(m) - ℒ(m)·Σ⁺ = { w | w ∈ ℒ(m) ∧ no proper prefix of w is in ℒ(m) }
-- a proper prefix of a string is a prefix of the string not empty and not equal to itself
min ∷ ∀ q s . (Ord q) ⇒ DFA q s → DFA (Either () q) s
min (DFA δ q₀ f) = DFA δ₁ (Right q₀) (Set.map Right f)
  where
    δ₁ ∷ (Either () q, s) → Either () q
    δ₁ (Left (), _)         = Left ()          -- `Left ()` is a dead state with no way to transition out
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

-- Quotient automaton
-- FIXME see about necessarily starting with trim automaton, may have to return `Maybe (DFA q s)`
-- FIXME or maybe something like trim the `DFA` as a `SomeDFA`
quotient ∷ ∀ q s . (Finite q, Finite s) ⇒ DFA q s → DFA q s
quotient m@(DFA δ q₀ f) = DFA (rep . δ) (rep q₀) (Set.map rep f)
  where
    rep ∷ q → q
    rep = representative (indistinguishability m)

-- The DFA, empty, which produces the empty language, such that
-- ℒ(empty) = ∅
empty ∷ DFA () s
empty = DFA (const ()) () (∅)

-- The DFA, epsilon, which produces the language, such that
-- ℒ(epsilon) = {ε}
epsilon ∷ DFA Bool s
epsilon = DFA (const False) True (singleton True)

-- Given a symbol of an alphabet, σ ∈ Σ, construct a DFA which recognizes only that symbol and nothing else, i.e.
-- ℒ(m) = {σ}
literal ∷ ∀ s . (Ord s) ⇒ s → DFA Ordering s
literal σ = DFA δ LT (singleton EQ)
  where
    δ ∷ (Ordering, s) → Ordering
    δ (LT, σ') | σ' == σ = EQ
    δ _                  = GT

fromSet ∷ ∀ s . (Ord s) ⇒ Set s → DFA Ordering s
fromSet s = DFA δ LT (singleton EQ)
  where
    δ ∷ (Ordering, s) → Ordering
    δ (LT, σ) | σ ∈ s = EQ
    δ _               = GT

-- TODO untested
toSet ∷ (Finite q, Finite s) ⇒ DFA q s → Set s
toSet m@(DFA δ _ _) = foldMap (\(q, σ) → bool (∅) (singleton σ) (δ (q, σ) ∈ useful m)) (useful m × sigma m)

dot ∷ (Finite s) ⇒ DFA Ordering s
dot = fromSet asSet

-- Convert an NFA with multiple start states to a DFA (performs determinization)
fromFA ∷ (Finite q) ⇒ FA.FA q s → DFA (Set q) s
fromFA m@(FA.FA δ i f) = DFA (\(states, σ) → foldMap (\q → δ (q, σ)) states) i (Set.filter (Common.intersects f) (powerSet (qs m)))

fromCDFA ∷ (Finite q, Finite s) ⇒ FA.FA q s → Maybe (DFA q s)
fromCDFA m@(FA.FA δ i f) | complete      m
                         ∧ deterministic m = Just (DFA (\(q, σ) → elemAt 0 (δ (q, σ))) (elemAt 0 i) f)
fromCDFA _                                 = Nothing

-- Take an NFA, and use subset construction to convert it to an equivalent DFA (performs determinization)
fromNFA ∷ (Finite q) ⇒ NFA.NFA q s → DFA (Set q) s
fromNFA m@(NFA.NFA δ q₀ f) = DFA (\(states, σ) → foldMap (\q → δ (q, σ)) states) -- for each occupied state,
                                                                                 -- transition to next state,
                                                                                 -- then union all the results
                                 (singleton q₀)
                                 (Set.filter (Common.intersects f) (powerSet (qs m)))

-- Take an EFA and use (slightly modded (See (2.) page 77, HMU)) subset construction
-- to generate an equivalent DFA by "eliminating" epsilon transitions
fromEFA ∷ (Finite q) ⇒ EFA.EFA q s → DFA (Set q) s
fromEFA = fromNFA . NFA.fromEFA

-- Take a DFA, d, and convert it to an NFA, n, such that ℒ(d) = ℒ(n)
toNFA ∷ DFA q s → NFA.NFA q s
toNFA (DFA δ q₀ f) = NFA.NFA (singleton . δ) q₀ f

-- min(ℒ(m)) = ℒ(m) - ℒ(m)·Σ⁺ = { w | w ∈ ℒ(m) ∧ no proper prefix of w is in ℒ(m) }
-- a proper prefix of a string is a prefix of the string not empty and not equal to itself
toNFAMin ∷ ∀ q s . (Ord q) ⇒ DFA q s → NFA.NFA q s
toNFAMin m@(DFA δ _ f) = (toNFA m) { NFA.delta = δ₁ }
  where
    δ₁ ∷ (q, s) → Set q
    δ₁ (q, _) | q ∈ f = (∅)  -- delete transitions out of final states
    δ₁ (q, σ)         = singleton (δ (q, σ))

-- TODO untested
toNFAShuffle ∷ forall q p s . (Ord q, Ord p) ⇒ DFA q s → DFA p s → NFA.NFA (q, p) s
toNFAShuffle (DFA δ₁ q₀ f₁) (DFA δ₂ p₀ f₂) = NFA.NFA δ (q₀, p₀) (f₁ × f₂)
  where
    δ ∷ ((q, p), s) → Set (q, p)
    δ ((q, p), σ) = Set.singleton (δ₁ (q, σ),     p    )
                  ∪ Set.singleton (    q    , δ₂ (p, σ))

-- Take a DFA, d, and convert it to an EFA, e, such that ℒ(d) = ℒ(e)
toEFA ∷ DFA q s → EFA.EFA q s
toEFA = NFA.toEFA . toNFA

-- cycle(ℒ) = { xy | yx ∈ ℒ }
-- A Second Course in Formal Languages and Automata Theory pg. 60
-- string conjugations
toEFACycle ∷ ∀ q s . (Finite q) ⇒ DFA q s → EFA.EFA (Either () (q, q, Bool)) s
toEFACycle m@(DFA δ q₀ f) = EFA.EFA δ₁ (Left ()) (Set.map (\q → Right (q, q, True)) (qs m))
  where
    δ₁ ∷ (Either () (q, q, Bool), Maybe s) → Set (Either () (q, q, Bool))
    δ₁ (Left             (), Nothing)         = Set.map (\q → Right (q, q, False)) (qs m)
    δ₁ (Right (q, p, False), Nothing) | q ∈ f = singleton (Right (q₀      , p, True))
    δ₁ (Right (q, p,     b), Just  σ)         = singleton (Right (δ (q, σ), p, b   )) -- Simulation
    δ₁ _                                      = (∅)

-- ½ℒ = { x ∈ Σ★ : there exists y ∈ Σ★ with |y| = |x| such that xy ∈ ℒ }.
-- A Second Course in Formal Languages and Automata Theory pg. 59
-- for all even length strings w ∈ ℒ, take the first half of w, producing ½ℒ
toEFAHalf ∷ ∀ q s . (Finite q, Finite s) ⇒ DFA q s → EFA.EFA (Either () (q, q, q)) s
toEFAHalf m@(DFA δ q₀ f) = EFA.EFA δ₁ (Left ()) (Set.map (\(q, qᶠ) → Right (q, q, qᶠ)) (qs m × f))
  where
    δ₁ ∷ (Either () (q, q, q), Maybe s) → Set (Either () (q, q, q))
    δ₁ (Left         (), Nothing) = Set.map (\q  → Right (q,       q₀,         q)) (qs m)
    δ₁ (Right (q, p, r), Just  σ) = Set.map (\σ' → Right (q, δ (p, σ), δ (r, σ'))) (sigma m)
    δ₁ _                          = (∅)

toFA ∷ (Finite q) ⇒ DFA q s → FA.FA q s
toFA = NFA.toFA . toNFA

toDA ∷ (Ord q) ⇒ DFA q s → (DA.DA q s, q)
toDA (DFA δ q₀ f) = (DA.DA (Predicate (∈ f)) (curry δ), q₀)

fromDA ∷ (Finite q) ⇒ (DA.DA q s, q) → DFA q s
fromDA (DA.DA o t, q₀) = DFA (uncurry t) q₀ (predicateToSet o)

-- Convert a DFA to a Generalized Nondeterministic Finite Automaton with ε-transitions
-- δ(q₁, σ) = q₂ ⟺ δ'(q₁, q₂) = σ
toGNFA ∷ ∀ q s . (Finite s, Ord q) ⇒ DFA q s → GNFA.GNFA q s
toGNFA m@(DFA δ q₀ f) = GNFA.GNFA δ'
  where
    δ' ∷ (Either Init q, Either Final q) → RE.RegExp s
    -- Connect the new (forced) GNFA start state to q₀ with an ε.
    δ' (Left  (Init _), Right        q₂) | q₂ == q₀ = RE.one
    -- Connect the new (forced) GNFA final state to each element of f with an ε.
    δ' (Right       q₁, Left  (Final _)) | q₁ ∈ f   = RE.one
    -- If q₁ and q₂ were connected (often via multiple transitions) in the DFA,
    -- lift all symbols into RE.Lit, and let multiple transitions be represented
    -- by the union of said literals. If no transitions between q₁ and q₂ in DFA then, RE.zero.
    δ' (Right       q₁, Right        q₂)            = sumWith RE.Lit (Set.filter (\σ → δ (q₁, σ) == q₂) (sigma m))
    -- Besides the explicitly given epsilon connections, no connections
    -- to the new final state nor from the new start state should exist.
    δ' _                                            = RE.zero

toRE ∷ (Finite q, Finite s) ⇒ DFA q s → RE.RegExp s
toRE = GNFA.toRE . toGNFA

toLanguage ∷ (Finite q, Finite s) ⇒ DFA q s → Language.ℒ s
toLanguage = RE.toLanguage . toRE
