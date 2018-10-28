{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE UnicodeSyntax             #-}
{-# OPTIONS_GHC -Wall                  #-}

module EFA where

import           Control.Monad
import           Data.Functor.Contravariant
import           Data.Map            as Map (Map, fromList)
import qualified Data.Map            as Map (fromSet, toAscList)
import           Prelude             hiding (map)
import           Data.Set            as Set hiding (foldl)
import           Data.Set.Unicode
import qualified Data.List.NonEmpty  as NE
import           Finite
import           Common
import qualified TransitionGraph as TG
import qualified FA
import qualified RegExp as RE
-- import           Algebra.Graph.Relation as Relation
import           Config

-- Nondeterministic Finite Automaton with ε-transitions
data EFA q s =
     EFA { delta ∷ (q, Maybe s) → Set q  -- δ : Q × (Σ ∪ {ε}) → P(Q)
         ,    q0 ∷ q                     -- The initial state
         ,    fs ∷ Set q                 -- The final states
         }

-- TODO Coend? http://www.staff.city.ac.uk/~ross/papers/Constructors.pdf
data SomeEFA s where
 SomeEFA ∷ (Show q, Finite q) ⇒ EFA q s → SomeEFA s

instance (Finite q) ⇒ Q (EFA q s) q
instance (Finite s) ⇒ Σ (EFA q s) s

instance (Finite s) ⇒ Σ (SomeEFA s) s

instance Contravariant (EFA q) where
  contramap ∷ (g → s) → EFA q s → EFA q g
  contramap h m@(EFA δ _ _) = m { delta = \(q, γ) → δ (q, fmap h γ) }

instance Contravariant SomeEFA where
  contramap ∷ (g → s) → SomeEFA s → SomeEFA g
  contramap h (SomeEFA m) = SomeEFA (contramap h m)

instance (Show q, Finite q, Show s, Finite s) ⇒ Show (EFA q s) where
  show m@(EFA _ q₀ f) = "( Q  = " ++ (show . Set' . qs)                m ++
                      "\n, Σ  = " ++ (show . Set' . sigma)             m ++
                      "\n, δ : Q × (Σ ∪ {ε}) → P(Q)"                     ++
                      "\n"        ++ (format'' . Map.fromList . table) m ++
                      "\n, q0 = " ++ show q₀                             ++
                      "\n, F  = " ++ (show . Set' $ f)                   ++ " )"

instance (Show s, Finite s) ⇒ Show (SomeEFA s) where
  show (SomeEFA m) = show m

instance (Finite q, Finite s) ⇒ Configuration EFA q s (Set q) where
  complete ∷ EFA q s → Bool
  complete = undefined -- FIXME implement when I restructure to allow conversions

  deterministic ∷ EFA q s → Bool -- FIXME implement when I restructure to allow conversions
  deterministic = undefined -- FIXME should I use the noEpsilonClosures ?

  codeterministic ∷ EFA q s → Bool
  codeterministic = undefined  -- FIXME

  occupied ∷ EFA q s → Set q → Set q
  occupied _ = id

  initial ∷ EFA q s → Set q
  initial m@(EFA _ q₀ _) = eclosure m (singleton q₀)

  final   ∷ EFA q s → Set q
  final     (EFA _ _  f) = f

  -- Given an EFA, m, and a configuration, return what it yields in one step
  (⊢) ∷ EFA q s → (Set q, [s]) → (Set q, [s])
  (⊢) _             (states,    []) = (states,                                                [])
  (⊢) m@(EFA δ _ _) (states, σ : w) = (eclosure m (foldMap δ (states × singleton (Just σ))),  w )

  accessible ∷ EFA q s → Set q
  accessible m@(EFA _ q₀ _) = reachable m q₀

  -- δ★ : Q × (Σ ∪ {ε})★ → P(Q)
  -- "Extended delta"
  -- Extend the δ function to accept strings of symbols
  -- TODO random untested/unclear design thought: might be able to define a morphism on Q which involves eclosure?
  delta' ∷ EFA q s → (q, [s]) → Set q
  delta' m (q, w) = delta'' m (singleton q, w)

  -- δ′′ : P(Q) × (Σ ∪ {ε})★ → P(Q)
  -- TODO untested, but if keeping then rewrite (⊢★) to use `= (delta'' ..., [])`?
  delta'' ∷ EFA q s → (Set q, [s]) → Set q
  delta'' m@(EFA δ _ _) (states, w) = foldl (\occupied' σ → eclosure m (foldMap δ (occupied' × singleton (Just σ))))
                                            (eclosure m states)
                                            w

  -- Take an EFA, m, and a string, and then compute the resulting states, which may be an empty set
  eval ∷ EFA q s → [s] → Set q
  eval m@(EFA _ q₀ _) w = delta' m (q₀, w)

  toGraph ∷ EFA q s → TG.TG q s
  toGraph = undefined  -- TODO epsilon elimination
  -- toGraph ∷ EFA q s → TG.ETG q s
  -- toGraph (EFA δ _ _) = TG.ETG (\s → stars (fmap (\q → (q, Set.toList (δ (q, s)))) asList))


-- Convert the transition function to a Map
deltaToMap ∷ (Finite q, Finite s) ⇒ EFA q s → Map (q, Maybe s) (Set q)
deltaToMap m@(EFA δ _ _) = Map.fromSet δ (corange m)

corange ∷ (Finite q, Finite s) ⇒ EFA q s → Set (q, Maybe s)
corange m = qs m × sigma_ε m

-- The range of the transition function
range ∷ (Finite q, Finite s) ⇒ EFA q s → Set (Set q)
range m@(EFA δ _ _) = Set.map δ (corange m)

-- The transition table of the EFA
table ∷ (Finite q, Finite s) ⇒ EFA q s → [((q, Maybe s), Set q)]
table m = Map.toAscList (deltaToMap m)

-- ε-closure of a set of states
-- Computes the set of states accessible from given state when no input can be consumed (0 or more ε-transitions)
-- Always contains at least the original state
eclosure ∷ (Ord q) ⇒ EFA q s → Set q → Set q
eclosure (EFA δ _ _) = fixedPoint closure
        where closure = foldMap (\q → q `Set.insert` δ (q, Nothing))

-- The EFA, empty, such that
-- ℒ(empty) = ∅
-- while adhering to Thompson's construction constraints
empty ∷ EFA Bool s
empty = EFA { delta = const (∅)
            , q0    = False
            , fs    = singleton True
            }

-- The EFA, epsilon, such that
-- ℒ(epsilon) = {ε}
-- while adhering to Thompson's construction constraints
epsilon ∷ EFA Bool s
epsilon = EFA { delta = δ
              , q0    = False
              , fs    = singleton True
              } where δ (False, Nothing) = singleton True
                      δ _                = (∅)

-- Given a symbol, construct an EFA which recognizes exactly that symbol and nothing else
literal ∷ (Eq s) ⇒ s → EFA Bool s
literal σ' = EFA { delta = δ
                 , q0    = False
                 , fs    = singleton True
                 } where δ (False, Just σ) | σ == σ' = singleton True
                         δ _                         = (∅)

-- Treat the given set as a set of literals to define a language
fromSet ∷ (Ord s) ⇒ Set s → EFA Bool s
fromSet s = EFA { delta = δ
                , q0    = False
                , fs    = singleton True
                } where δ (False, Just σ) | σ ∈ s = singleton True
                        δ _                       = (∅)

-- Avoid using `foldl` because the base case may introduce extra states
fromList ∷ (Eq s) ⇒ [s] → SomeEFA s
fromList []      = SomeEFA epsilon
fromList (σ : w) = fromNE (σ NE.:| w)

fromNE ∷ (Eq s) ⇒ NE.NonEmpty s → SomeEFA s
fromNE w = foldl1 (\(SomeEFA acc) (SomeEFA σ) → SomeEFA (concatenate acc σ)) (fmap (SomeEFA . literal) w)

-- TODO not really tested
fromLang ∷ (Eq s) ⇒ [[s]] → SomeEFA s
fromLang [] = SomeEFA EFA.empty
fromLang ws = foldl1 (\(SomeEFA m₁) (SomeEFA m₂) → SomeEFA (EFA.union m₁ m₂)) (fmap EFA.fromList ws)

-- TODO deleteme
-- lang ∷ (Finite s) ⇒ SomeEFA s → [[s]]
-- lang (SomeEFA m) = language m

-- Thompson's construction
fromRE ∷ (Eq s) ⇒ RE.RegExp s → SomeEFA s
fromRE RE.Zero     = SomeEFA EFA.empty
fromRE RE.One      = SomeEFA epsilon
fromRE (RE.Lit  σ) = SomeEFA (literal σ)
fromRE (α RE.:| β) = union'       (fromRE α) (fromRE β)
               where union'       ∷ SomeEFA s → SomeEFA s → SomeEFA s
                     union'       (SomeEFA m₁) (SomeEFA m₂) = SomeEFA (EFA.union       m₁ m₂)
fromRE (α RE.:. β) = concatenate' (fromRE α) (fromRE β)
               where concatenate' ∷ SomeEFA s → SomeEFA s → SomeEFA s
                     concatenate' (SomeEFA m₁) (SomeEFA m₂) = SomeEFA (EFA.concatenate m₁ m₂)
fromRE (RE.Star α) = star'        (fromRE α)
               where star'        ∷             SomeEFA s → SomeEFA s
                     star'                     (SomeEFA m)  = SomeEFA (EFA.star m)

-- Union for Thompson's construction
union ∷ (Ord q, Ord p) ⇒ EFA q s → EFA p s → EFA (Either Bool (Either q p)) s
union (EFA δ₁ q₀ f₁) (EFA δ₂ p₀ f₂) =
                        EFA { delta = δ
                            , q0    = Left False
                            , fs    = Set.singleton (Left True)
                            } where δ (Left      False, Nothing)          = Set.fromList [Right (Left q₀), Right (Right p₀)]
                                    δ (Left          _,       _)          = (∅)
                                    -- connect the "old" final states of m₁ to the new final state
                                    δ (Right (Left  q), Nothing) | q ∈ f₁ = Left True `Set.insert` Set.map (Right . Left)  (δ₁ (q, Nothing))
                                    δ (Right (Left  q),       σ)          =                        Set.map (Right . Left)  (δ₁ (q,       σ))
                                    δ (Right (Right p), Nothing) | p ∈ f₂ = Left True `Set.insert` Set.map (Right . Right) (δ₂ (p, Nothing))
                                    δ (Right (Right p),       σ)          =                        Set.map (Right . Right) (δ₂ (p,       σ))

-- Concatenation for Thompson's construction
concatenate ∷ (Ord q, Ord p) ⇒ EFA q s → EFA p s → EFA (Either q p) s
concatenate (EFA δ₁ q₀ f₁) (EFA δ₂ p₀ f₂) =
                                      EFA { delta = δ
                                          , q0    = Left q₀
                                          , fs    = map Right f₂
                                          -- if this state, q, is a final state, merge q's transitions with p₀'s transitions
                                          } where δ (Left  q, σ) | q ∈ f₁ =           δ₁ (q, σ) ⊎ δ₂ (p₀, σ)
                                                  δ (Left  q, σ)          = map Left (δ₁ (q, σ))
                                                  δ (Right p, σ)          =            map Right (δ₂ (p,  σ))

-- Kleene Star for Thompson's construction
star ∷ (Ord q) ⇒ EFA q s → EFA (Either Bool q) s
star (EFA δ q₀ f) = EFA { delta = δ₁
                        , q0    = Left False
                        , fs    = singleton (Left True)
                        } where δ₁ (Left False, Nothing)         =                              Set.fromList [Right q₀, Left True]
                                δ₁ (Left     _,       _)         = (∅)
                                δ₁ (Right    q, Nothing) | q ∈ f = map Right (δ (q, Nothing)) ∪ Set.fromList [Right q₀, Left True]
                                δ₁ (Right    q,       σ)         = map Right (δ (q,       σ))

-- FIXME test this
-- The product construction
-- Essentially this runs two NFAs (which both share the same alphabet) "in parallel" together in lock step
synchronous ∷ (Ord q, Ord p) ⇒ EFA q s → EFA p s → EFA (q, p) s
synchronous (EFA δ₁ q₀ f₁) (EFA δ₂ p₀ f₂) = EFA { delta = δ
                                                , q0    = (q₀, p₀)
                                                , fs    = f₁ × f₂
                                                } where δ ((q, p), σ) = δ₁ (q, σ) × δ₂ (p, σ)

-- FIXME test me, I wrote this when tired
-- The asynchronous product of two EFA
-- Essentially this runs two EFAs with different alphabets "in parallel" independently
asynchronous ∷ (Ord q, Ord p) ⇒ EFA q s → EFA p g → EFA (q, p) (Either s g)
asynchronous (EFA δ₁ q₀ f₁) (EFA δ₂ p₀ f₂) = EFA { delta = δ
                                                 , q0    = (q₀, p₀)
                                                 , fs    = f₁ × f₂
                                                 } where δ ((q, p), Nothing)        = δ₁ (q, Nothing) × δ₂ (p, Nothing)
                                                         δ ((q, p), Just (Left  σ)) = δ₁ (q, Just  σ) × singleton p
                                                         δ ((q, p), Just (Right γ)) = singleton q     × δ₂ (p, Just  γ)

-- TODO version which determinizes instead of adding an extra state
fromFA ∷ (Ord q) ⇒ FA.FA q s → EFA (Either () q) s
fromFA (FA.FA δ i f) = EFA { delta = Set.map Right . δ₁
                           , q0    = Left ()
                           , fs    = Set.map Right f
                           } where δ₁ (Left (), Nothing) = i
                                   δ₁ (Right q, Just  σ) = δ (q, σ)
                                   δ₁ _                  = (∅)