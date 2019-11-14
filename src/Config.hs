{-# LANGUAGE FunctionalDependencies #-}

module Config where

import           Common (fixedPoint, intersects, upToLength, size')
import           Finite (Q, Σ, asList, qs, sigmaStar)
import           Data.Set as Set (Set, filter, singleton, insert, disjoint)
import           Data.Set.Unicode ((∩), (∖), (∋), (⊆))
import           Data.Eq.Unicode ((≠))
import           Data.Bool.Unicode ((∧))
import           Numeric.Natural.Unicode (ℕ)
import qualified TransitionGraph as TG

-- When `occupy` is `q` the automaton is deterministic, and when `occupy` is `Set q` it enables nondeterminism
class (Q (automaton q s) q, Σ (automaton q s) s, Eq occupy) ⇒ Configuration automaton q s occupy | automaton q s → occupy where
    -- type ID = (occupy, [s])
    -- N.B. `ID` here is "instantaneous description" and not "identity"
    initialID ∷ automaton q s → [s] → (occupy, [s])
    initialID m w = (initial m, w)

    -- The automaton's Transition Graph.
    -- N.B. information is lost in this conversion
    toGraph ∷ automaton q s → TG.TG q s

    occupied ∷ automaton q s → occupy → Set q

    initial ∷ automaton q s → occupy
    
    -- final "accepting" states of the automaton
    final   ∷ automaton q s → Set q

    -- The set of states which can be reached from the inital state(s)
    accessible ∷ automaton q s → Set q

    complete      ∷ automaton q s → Bool

    -- "A traditional finite-state automaton is deterministic if, for each state, the
    -- next state is uniquely determined by the current state and the current input character" --  Y.-S. Han and D. Wood
    -- Given an automaton, decide if it is deterministic, regardless of its type
    deterministic ∷ automaton q s → Bool

    codeterministic ∷ automaton q s → Bool

    -- An automaton M is called bideterministic if both M and its reversal automaton, Mʳ, are deterministic
    bideterministic ∷ automaton q s → Bool
    bideterministic m = deterministic m ∧ codeterministic m

    -- δ★ : Q × Σ★ → Q
    -- "Extended delta" - The delta function extended from single symbols to strings (lists of symbols).
    -- Take a DFA and a starting state, q, for that DFA, then compute the state p such that δ★(q, w) = p
    delta' ∷ automaton q s → (q, [s]) → occupy

    -- δ′′ : P(Q) × Σ★ → P(Q)
    delta'' ∷ automaton q s → (Set q, [s]) → Set q

    -- "Becomes in one move"
    -- Given an automaton and a configuration, return what it yields in one step
    (⊢)     ∷ automaton q s → (occupy, [s]) → (occupy, [s])

    (⊢⋆)    ∷ automaton q s → (occupy, [s]) → (occupy, [s])
    (⊢⋆) = fixedPoint . (⊢)

    eval ∷ automaton q s → [s] → occupy
    eval m w = fst (m ⊢⋆ initialID m w)

    eval'' ∷ automaton q s → [s] → Set q
    eval'' m w = delta'' m (occupied m (initial m), w)

    -- Given an automaton and a state, q, determine the set of states reachable in exactly one move
    -- i.e. all the "outgoing arrows" of the state.
    -- In Digraph terms this is the the out-neighbors, or the given node's adjacencies
    adjacent   ∷ automaton q s → q → Set q
    adjacent m q = foldMap (\σ → delta'' m (singleton q, [σ])) asList

    -- Determine which states are reachable in the given automaton, starting in state q,
    -- Works but not most efficient implementation, perhaps this can be reworked using alga at some point
    -- N.B. A state is always reachable from itself because δ★(q, ε) = q
    -- TODO can run in parallel DFS on each letter of Sigma and unions on result -- TODO just implement in terms of alga?
    reachable ∷ automaton q s → q → Set q
    reachable m = reachable' m . singleton

    -- `reachable` lifted into sets
    reachable' ∷ automaton q s → Set q → Set q
    reachable' m = fixedPoint (foldMap (\q → q `insert` adjacent m q))

    -- Given two states, q₁ and q₂, determine if q₁ can reach q₂
    reaches ∷ automaton q s → q → q → Bool
    reaches m = (∋) . reachable m

    -- A state is transient if it cannot reach itself, i.e.
    -- A state q ∈ Q is transient if ∀w ∈ Σ⁺, δ(q, w) ≠ q
    transient ∷ automaton q s → q → Bool
    transient m q = all (≠ q) (foldMap (reachable m) (adjacent m q))

    -- not transient states are called recurrent
    recurrent ∷ automaton q s → q → Bool
    recurrent m = not . transient m

    -- Take all the states of the given automaton, subtract the accessible ones
    inaccessible ∷ automaton q s → Set q
    inaccessible m = qs m ∖ accessible m

    -- Given an automaton, m, find the states of m from which a final state cannot be reached
    -- In the literature, this is frequently specific to non-final state for which all output transitions
    -- are self loops.
    dead ∷ automaton q s → Set q
    dead m = Set.filter (disjoint (final m) . reachable m) (qs m) -- all states where reachable ∩ F = ∅

    -- TODO write test for this (reverse the automaton, check that each coaccessible m == accessible m' and coaccessible m' == accessible m)
    -- All the states of the automaton such there exists a path to the final state
    -- A state q ∈ Q is coaccessible when ∃w ∈ Σ★ such that δ★(q, w) ∈ F
    coaccessible ∷ automaton q s → Set q
    coaccessible m = Set.filter (intersects (final m) . reachable m) (qs m)

    -- The useful states of the automaton are the states that can be reached from q₀ and can alse reach a final state
    useful ∷ automaton q s → Set q
    useful m = accessible m ∩ coaccessible m

    -- An automaton is trim when states are all accessible and co-accessible.
    trim ∷ automaton q s → Bool
    trim m = qs m == useful m

    acyclic ∷ automaton q s → Bool
    acyclic m = all (transient m) (qs m)

    -- Given an automaton, m, decide if the number of strings m accepts is finite, i.e. decide if ℒ(m) contains a finite number of words
    finite ∷ automaton q s → Bool
    finite m = all (transient m) (useful m)

    -- Given an automaton, m, decide if any state is able to reach itself
    cyclic  ∷ automaton q s → Bool
    cyclic m = any (recurrent m) (qs m)

    -- Given an automaton, m, decide if there is an infinite number of strings in ℒ(m)
    infinite ∷ automaton q s → Bool
    infinite m = any (recurrent m) (useful m)

    -- The size of the automaton, m, |m| = |Q|
    -- N.B. definitions for "size" of an automaton greatly differs between papers
    size ∷ automaton q s → ℕ
    size = size' . qs

    -- Given an automaton, decide if it produces the empty language, i.e.
    -- ℒ ≟ ∅
    isZero ∷ automaton q s → Bool
    isZero m = accessible m `disjoint` final m

    -- Given an automaton, decide if it accepts all possible strings of the alphabet, i.e.
    -- A DFA M accepts Σ★ iff all the accessible states are final states.
    -- Also valid solution to decide iff the result of minimizing M is a DFA isomorphic to the minimal DFA for Σ★
    -- ℒ ≟ Σ★
    isSigmaStar ∷ automaton q s → Bool
    isSigmaStar m = accessible m ⊆ final m

    -- TODO
    -- toFA ∷ automaton q s → FA.FA q s
    -- toFA m = FA.FA { delta = undefined, FA.initial = initial, FA.final = final }

    -- Take an automaton, m, and a string, w, and decide if that string is accepted/recognized
    -- m accepts a string, w ∈ Σ★, iff δ★(I, w) ∩ F ≠ ∅
    accepts ∷ automaton q s → [s] → Bool
    accepts m w = eval'' m w `intersects` final m

    rejects ∷ automaton q s → [s] → Bool
    rejects m w = eval'' m w `disjoint` final m

    -- Lazily generate the entire language of the given automaton
    -- Mathematically, this is defined as a Set,
    -- however, Data.Set does not support lazy infinite sets.
    -- ℒ(m) ⊆ Σ★
    -- ℒ(m) = { w ∈ Σ★ | δ★(q₀, w) ∈ F } for DFA
    -- ℒ(m) = { w ∈ Σ★ | δ★(q₀, w) ∩ F ≠ ∅ } for NFA, EFA
    -- ℒ(m) = { w ∈ Σ★ | δ★(I, w) ∩ F ≠ ∅ } for FA
    language ∷ automaton q s → [[s]]
    language m
        -- if m produces the empty language then no need to waste computation
        | isZero      m = []
        -- if we know m accepts all strings, don't bother filtering with `accepts`, just return Σ★
        | isSigmaStar m = sigmaStar m
        | otherwise     = Prelude.filter (accepts m) strings'
                    where strings'
                            -- if the language is finite then we don't need to filter over all of Σ★ (and we may return a List which terminates!)
                            -- because the language produced by the automaton is finite, we know there are no cycles in useful states so
                            -- the language can't contain any string w such that |w| ≥ n where n is the number of useful states
                            | finite m  = upToLength (size' (useful m)) (sigmaStar m)
                            -- otherwise just filter `accepts` predicate over Σ★
                            | otherwise = sigmaStar m
