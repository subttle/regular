{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wall                  #-}

module NFA where

import           Common
import           Data.Map            as Map (Map, fromList)
import qualified Data.Map            as Map (fromSet, toAscList)
import           Data.Set            as Set hiding (foldl)
import qualified Data.List           as List
import qualified Data.List.NonEmpty  as NE
import           Data.Set.Unicode ((∅), (∈), (∉))
import           Data.Ord.Unicode ((≥), (≤))
import           Data.Bool.Unicode ((∧), (∨))
import qualified EFA
import qualified FA
import qualified TransitionGraph as TG
import           Finite
import           Data.Functor.Contravariant (Contravariant, contramap)
-- import           Data.Functor.Invariant
-- import           Data.Functor.Contravariant.Divisible
import           Algebra.Graph.Relation as Relation hiding (domain)
import           Config

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
  contramap h (NFA δ q₀ f) = NFA (\(q, γ) → δ (q, h γ)) q₀ f

instance Contravariant SomeNFA where
  contramap ∷ (g → s) → SomeNFA s → SomeNFA g
  contramap h (SomeNFA m) = SomeNFA (contramap h m)

instance (Show q, Finite q, Show s, Finite s) ⇒ Show (NFA q s) where
  show ∷ NFA q s → String
  show m@(NFA _ q₀ f) = List.intercalate "\n, "
                        [ "( Q  = "               ++ (show . Set' . qs)               m
                        ,   "Σ  = "               ++ (show . Set' . sigma)            m
                        ,   "δ  : Q × Σ → P(Q)\n" ++ (format' . Map.fromList . table) m
                        ,   "q₀ = "               ++  show q₀
                        ,   "F  = "               ++ (show . Set' $ f) ++ " )"
                        ]

instance (Show s, Finite s) ⇒ Show (SomeNFA s) where
  show ∷ SomeNFA s → String
  show (SomeNFA m) = show m

instance (Finite q, Finite s) ⇒ Configuration NFA q s (Set q) where
  complete      ∷ NFA q s → Bool
  complete      = all ((≥ 1) . size') . image

  deterministic ∷ NFA q s → Bool
  deterministic = all ((≤ 1) . size') . image
  
  codeterministic ∷ NFA q s → Bool
  codeterministic = deterministic . FA.reversal . toFA

  occupied ∷ NFA q s → Set q → Set q
  occupied _ = id
  
  initial ∷ NFA q s → Set q
  initial (NFA _ q₀ _) = singleton q₀

  final   ∷ NFA q s → Set q
  final   (NFA _ _  f) = f

  -- Given an NFA, m, and a configuration, return what it yields in one step
  (⊢) ∷ NFA q s → (Set q, [s]) → (Set q, [s])
  (⊢) _           (states,     []) = (           states               , [])
  (⊢) (NFA δ _ _) (states, σ : w ) = (foldMap δ (states × singleton σ), w )

  accessible ∷ NFA q s → Set q
  accessible m@(NFA _ q₀ _) = reachable m q₀

  deltaD ∷ NFA q s → (Set q, s) → Set q
  deltaD (NFA δ _ _) (states, s) = foldMap (\q → δ (q, s)) states

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

  toGraph ∷ NFA q s → TG.TG q s
  toGraph (NFA δ _ _) = TG.TG (\s → stars (fmap (\q → (q, Set.toList (δ (q, s)))) asList))

domain ∷ (Finite q, Finite s) ⇒ NFA q s → Set (q, s)
domain m = qs m × sigma m

deltaToMap ∷ (Finite q, Finite s) ⇒ NFA q s → Map (q, s) (Set q)
deltaToMap m@(NFA δ _ _) = Map.fromSet δ (domain m)

image ∷ (Finite q, Finite s) ⇒ NFA q s → Set (Set q)
image m@(NFA δ _ _) = Set.map δ (domain m)

-- The transition table of the NFA
table ∷ (Finite q, Finite s) ⇒ NFA q s → [((q, s), Set q)]
table = Map.toAscList . deltaToMap

-- The NFA, empty, such that
-- ℒ(empty) = ∅
empty ∷ NFA () s
empty = NFA (const (∅)) () (∅)

-- The NFA, epsilon, such that
-- ℒ(epsilon) = {ε}
epsilon ∷ NFA () s
epsilon = NFA (const (∅)) () (singleton ())

-- Given a symbol, construct an NFA which recognizes exactly that symbol and nothing else
literal ∷ ∀ s . (Eq s) ⇒ s → NFA Bool s
literal σ' = NFA δ False (singleton True)
  where
    δ ∷ (Bool, s) → Set Bool
    δ (False, σ) | σ == σ' = singleton True
    δ _                    = (∅)

fromSet ∷ ∀ s . (Ord s) ⇒ Set s → NFA Bool s
fromSet s = NFA δ False (singleton True)
  where
    δ ∷ (Bool, s) → Set Bool
    δ (False, σ) | σ ∈ s = singleton True
    δ _                  = (∅)

-- Return an NFA whose language is all permutations of the given set
-- e.g. ℒ(permutations {0, 1, 2}) = {"012", "021", "102", "120", "201", "210"}
permutations ∷ ∀ s . (Ord s) ⇒ Set s → NFA (Set s) s
permutations s = NFA δ (∅) (singleton s)
  where
    δ ∷ (Set s, s) → Set (Set s)
    δ (q, σ) | σ ∈ s
             ∧ σ ∉ q
             ∨ Set.null s = singleton (σ `insert` q)
    δ _                   = (∅)

-- TODO Could just use `fromRE` instead... Confirm this way is better?
fromList ∷ (Eq s) ⇒ [s] → SomeNFA s
fromList []      = SomeNFA epsilon
fromList (σ : w) = fromNE (σ NE.:| w)

-- Avoid using `foldl` (as opposed to `foldl1`) because the base case introduces more states than
-- necessary, i.e. `foldl (\(SomeNFA acc) σ → SomeNFA (concatenate acc (literal σ))) (SomeNFA epsilon)`
-- will concatenate the last symbol in the string with epsilon.
fromNE ∷ (Eq s) ⇒ NE.NonEmpty s → SomeNFA s
fromNE = foldl1 (\(SomeNFA acc) (SomeNFA σ) → SomeNFA (concatenate acc σ)) . fmap (SomeNFA . literal)

-- Given two NFAs m₁ and m₂, return an NFA which recognizes any string from
-- m₁ immediately followed by any string from m₂
concatenate ∷ ∀ q p s . (Ord q, Ord p) ⇒ NFA q s → NFA p s → NFA (Either q p) s
concatenate (NFA δ₁ q₀ f₁) (NFA δ₂ p₀ f₂) = NFA δ (Left q₀) (Set.map Right f₂)
  where
    δ ∷ (Either q p, s) → Set (Either q p)
    -- if this state, q, is a final state, merge q's transitions with p₀'s transitions
    δ (Left  q, σ) | q ∈ f₁ = δ₁ (q, σ) ⊎ δ₂ (p₀, σ)  -- merge any last state of m₁ with p₀
    δ (Left  q, σ)          = δ₁ (q, σ) ⊎ (∅)
    δ (Right p, σ)          = (∅)       ⊎ δ₂ (p , σ)

-- The product construction
-- Essentially this runs two NFAs (which both share the same alphabet) "in parallel" together in lock step
synchronous ∷ (Ord q, Ord p) ⇒ NFA q s → NFA p s → NFA (q, p) s
synchronous (NFA δ₁ q₀ f₁) (NFA δ₂ p₀ f₂) = NFA (\((q, p), σ) → δ₁ (q, σ) × δ₂ (p, σ)) (q₀, p₀) (f₁ × f₂)

-- The asynchronous product of two NFA
-- Essentially this runs two NFAs with different alphabets "in parallel" independently
asynchronous ∷ ∀ q p s g . (Ord q, Ord p) ⇒ NFA q s → NFA p g → NFA (q, p) (Either s g)
asynchronous (NFA δ₁ q₀ f₁) (NFA δ₂ p₀ f₂) = NFA δ (q₀, p₀) (f₁ × f₂)
  where
    δ ∷ ((q, p), Either s g) → Set (q, p)
    δ ((q, p), Left  σ) = δ₁ (q, σ)   × singleton p
    δ ((q, p), Right γ) = singleton q × δ₂ (p, γ)

{-
import qualified Data.Can as Can (Can (..))
import           Data.Can
import           Data.Smash
import           Data.Wedge
import           Data.These

-- FIXME rename, consider https://lotsofwords.com/*chronous
asdf1c ∷ ∀ q p s g . (Ord q, Ord p) ⇒ NFA q s → NFA p g → NFA (q, p) (Can s g)
asdf1c (NFA δ₁ q₀ f₁) (NFA δ₂ p₀ f₂) = NFA δ (q₀, p₀) (f₁ × f₂)
  where
    δ ∷ ((q, p), Can s g) → Set (q, p)
    δ ((q, p),  Can.Non     ) = singleton q × singleton p
    δ ((q, p), (Can.One σ  )) = δ₁ (q, σ)   × singleton p
    δ ((q, p), (Can.Eno   γ)) = singleton q × δ₂ (p, γ)
    δ ((q, p), (Can.Two σ γ)) = δ₁ (q, σ)   × δ₂ (p, γ)

asdf2c ∷ ∀ q p s . (Ord q, Ord p) ⇒ NFA q s → NFA p s → NFA (Can q p) s
asdf2c (NFA δ₁ q₀ f₁) (NFA δ₂ p₀ f₂) = NFA δ (Can.Two q₀ p₀) (Set.map (uncurry Can.Two) (f₁ × f₂))
  where
    δ ∷ (Can q p, s) → Set (Can q p)
    δ (Can.Non    , _) = singleton        Can.Non -- TODO `(∅)`
    δ (Can.One q  , σ) = Set.map          Can.One   (δ₁ (q, σ))
    δ (Can.Eno   p, σ) = Set.map          Can.Eno                 (δ₂ (p, σ))
    δ (Can.Two q p, σ) = Set.map (uncurry Can.Two) ((δ₁ (q, σ)) × (δ₂ (p, σ)))

asdf1s ∷ ∀ q p s g . (Ord q, Ord p) ⇒ NFA q s → NFA p g → NFA (q, p) (Smash s g)
asdf1s (NFA δ₁ q₀ f₁) (NFA δ₂ p₀ f₂) = NFA δ (q₀, p₀) (f₁ × f₂)
  where
    δ ∷ ((q, p), Smash s g) → Set (q, p)
    δ ((q, p),  Nada      ) = singleton q × singleton p
    δ ((q, p), (Smash σ γ)) = δ₁ (q, σ)   × δ₂ (p, γ)

asdf1w ∷ ∀ q p s g . (Ord q, Ord p) ⇒ NFA q s → NFA p g → NFA (q, p) (Wedge s g)
asdf1w (NFA δ₁ q₀ f₁) (NFA δ₂ p₀ f₂) = NFA δ (q₀, p₀) (f₁ × f₂)
  where
    δ ∷ ((q, p), Wedge s g) → Set (q, p)
    δ ((q, p),  Nowhere     ) = singleton q × singleton p
    δ ((q, p), (Here    σ  )) = (δ₁ (q, σ)) × singleton p
    δ ((q, p), (There     γ)) = singleton q × (δ₂ (p, γ))

asdf1t ∷ ∀ q p s g . (Ord q, Ord p) ⇒ NFA q s → NFA p g → NFA (q, p) (These s g)
asdf1t (NFA δ₁ q₀ f₁) (NFA δ₂ p₀ f₂) = NFA δ (q₀, p₀) (f₁ × f₂)
  where
    δ ∷ ((q, p), These s g) → Set (q, p)
    δ ((q, p), (This  σ   )) = (δ₁ (q, σ)) × singleton p
    δ ((q, p), (That     γ)) = singleton q × (δ₂ (p, γ))
    δ ((q, p), (These σ  γ)) = (δ₁ (q, σ)) × (δ₂ (p, γ))

asdf2t ∷ ∀ q p s . (Ord q, Ord p) ⇒ NFA q s → NFA p s → NFA (These q p) s
asdf2t (NFA δ₁ q₀ f₁) (NFA δ₂ p₀ f₂) = NFA δ (These q₀ p₀) (Set.map (uncurry These) (f₁ × f₂))
  where
    δ ∷ (These q p, s) → Set (These q p)
    δ ((This  q  ), σ) = Set.map          This    (δ₁ (q, σ))
    δ ((That    p), σ) = Set.map          That                  (δ₂ (p, σ))
    δ ((These q p), σ) = Set.map (uncurry These) ((δ₁ (q, σ)) × (δ₂ (p, σ)))
-}

toFA ∷ (Finite q) ⇒ NFA q s → FA.FA q s
toFA (NFA δ q₀ f) = FA.FA δ (singleton q₀) f

minimize ∷ (Finite q, Finite s) ⇒ NFA q s → NFA (Set (Set q)) s
minimize = undefined -- fromJust . fromFA' . FA.minimize . toFA

-- Given an NFA, m, convert m to an equivalant EFA (which produces exactly the same language)
toEFA ∷ ∀ q s . NFA q s → EFA.EFA q s
toEFA (NFA δ q₀ f) = EFA.EFA δₑ q₀ f
  where
    δₑ ∷ (q, Maybe s) → Set q
    δₑ (q, Just  σ) = δ (q, σ)
    δₑ (_, Nothing) = (∅)

-- Determinize the NFA without transforming it to a DFA
-- TODO test property that `determinisitic (NFA.determinization m)` is always true
-- TODO also test that ℒ(m) = ℒ(det(m))
determinization ∷ (Finite q) ⇒ NFA q s → NFA (Set q) s
determinization m@(NFA δ q₀ f) = NFA (\(states, σ) → Set.map (\q → δ (q, σ)) states)
                                     (singleton q₀)
                                     (Set.filter (intersects f) (powerSet (qs m)))

-- Take an EFA and generate an equivalent NFA (Stanford Coursera algo Nondeterminism lecture)
-- TODO also offer subset construction method?
fromEFA ∷ (Finite q) ⇒ EFA.EFA q s → NFA q s
fromEFA m@(EFA.EFA δ q₀ f) = NFA (\(q, σ) → foldMap (\p → δ (p, Just σ)) (EFA.eclosure m (singleton q)))
                                 q₀
                                 -- Any state which can reach a final state via epsilon transitions
                                 (Set.filter (intersects f . EFA.eclosure m . singleton) (qs m))

-- For testing if a particular sequence of moves will work
noEpsilonClosures ∷ (Finite q) ⇒ EFA.EFA q s → NFA q (Maybe s)
noEpsilonClosures (EFA.EFA δ q₀ f) = NFA δ q₀ f

fromFA ∷ (Finite q) ⇒ FA.FA q s → NFA (Either () q) s
fromFA = NFA.fromEFA . EFA.fromFA

-- If the FA only exactly one initial state then we may convert it to an NFA without adding an extra state
fromFA' ∷ FA.FA q s → Maybe (NFA q s)
fromFA' m | size' (FA.initial m) == 1 = Just (NFA (FA.delta m) (elemAt 0 (FA.initial m)) (FA.final m))
          | otherwise                 = Nothing

fromGraph ∷ (Finite q, Finite s) ⇒ TG.TG q s → q → Set q → NFA q s
fromGraph (TG.TG t) = NFA (\(q, s) → postSet q (t s))
