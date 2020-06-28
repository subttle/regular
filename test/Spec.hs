{-# OPTIONS_GHC -Wall                   #-}
-- Unfortunately, using Fin types breaks the warnings for incomplete patterns at this time
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE OverloadedStrings          #-}

import           DFA
import           NFA (NFA)
import qualified NFA
-- import qualified EFA
-- import qualified GFA
import           RegExp (RegExp (..))
import qualified RegExp as RE hiding (RegExp (..))
import           Language (ℒ)
import qualified Language
import           Common
import           Finite
import           Examples (by3, by5, by5', minimal, ab, cd)
import           Data.Set (Set, singleton)
import           Config
import           Numeric.Natural.Unicode (ℕ)
import           Data.Bool (bool)
import           Data.Eq.Unicode ((≠))
import           Data.Functor.Contravariant (contramap, Equivalence (..), Comparison (..), Predicate (..))
import qualified Data.Group as G
import           EasyTest (Test, tests, scope, expect, run)
import qualified Data.List as List
import qualified Data.List.NonEmpty as NE (NonEmpty (..), fromList)
import           Data.Either (isRight, isLeft, lefts)

main ∷ IO ()
main = run suite

suite ∷ Test ()
suite = tests [ testFizzBuzz
              , scope "DFA.empty"     . expect $ Config.language DFA.empty          == ([]   ∷ [[Bool]])
              , scope "DFA.epsilon"   . expect $ Config.language DFA.epsilon        == ([[]] ∷ [[Bool]])
              , scope "DFA.literal"   . expect $ Config.language (DFA.literal True) == [[True]]
              , scope "DFA.quotient"  . expect $ minimal `DFA.equal` quotient minimal && size' (useful (quotient minimal)) < size' (useful minimal)
              , scope "DFA.toRE"      . expect $ toRE by5 `RE.equivalent` by5'
              , testDFArquotient
              , testDFAinvhomimage
              , testRESubstitution
              , testREDropout
              , testDFAPerfectShuffle
              , testNFAshuffle
              , testBisimSubset (by5, DFA.toLanguage by5) (List.take 101 (freeMonoid asList))
              -- "For example, the restricted growth function 0,1,1,2,0,3,1 defines the set partition {{1,5}, {2,3,7}, {4}, {6}}"
              -- https://www8.cs.umu.se/kurser/TDBAfl/VT06/algorithms/BOOK/BOOK4/NODE153.HTM
              , scope "toRGS"         . expect $ toRGS (toEquivalence [0 NE.:| [4], 1 NE.:| [2, 6], 3 NE.:| [], 5 NE.:| []]) == (RGS [0, 1, 1, 2, 0, 3, 1] ∷ RGS Fin₇)
              , scope "RGS"           . expect $ bijection (toRGS @ Suit) (fromRGS @ Suit) -- bijection (toRGS ∷ Equivalence Suit → RGS Suit) (fromRGS ∷ RGS Suit → Equivalence Suit)
              , testComposeC
              , testGroupInvert
              , testCycles
              , testOpenersClosers
              ]

-- Test that ordinary FizzBuzz has the same output as the FizzBuzz which uses DFA
testFizzBuzz ∷ Test ()
testFizzBuzz = scope "main.FizzBuzz" . expect $ woDFA == wDFA
  where
    -- FizzBuzz (without DFA)
    woDFA ∷ [String]
    woDFA = fmap fizzbuzz [1 .. 100]
      where
        fizz ∷ ℕ → Bool
        fizz n = n `mod` 3 == 0
        buzz ∷ ℕ → Bool
        buzz n = n `mod` 5 == 0
        fbzz ∷ ℕ → Bool
        fbzz n = fizz n && buzz n
        fizzbuzz ∷ ℕ → String
        fizzbuzz n | fbzz n    = "FizzBuzz"
                   | fizz n    = "Fizz"
                   | buzz n    = "Buzz"
                   | otherwise = show n
    -- FizzBuzz (with DFA)
    wDFA ∷ [String]
    wDFA = fmap fizzbuzz [1 .. 100]
      where
        fizz ∷ ℕ → Bool
        fizz n = accepts  by3                         (toDigits n)
        buzz ∷ ℕ → Bool
        buzz n = accepts                         by5  (toDigits n)
        fbzz ∷ ℕ → Bool
        fbzz n = accepts (by3 `DFA.intersection` by5) (toDigits n)
        fizzbuzz ∷ ℕ → String
        fizzbuzz n | fbzz n    = "FizzBuzz"
                   | fizz n    = "Fizz"
                   | buzz n    = "Buzz"
                   | otherwise = show n

-- https://math.stackexchange.com/questions/871662/finding-right-quotient-of-languages
testDFArquotient ∷ Test ()
testDFArquotient = scope "DFA.rquotient" . expect $ and e₃Tests
  where
    -- L₁ = {"carrot"}
    e₃L₁ ∷ DFA Fin₈ Alpha
    e₃L₁   = DFA δ 0 (singleton 6)
      where
        δ ∷ (Fin₈, Alpha) → Fin₈
        δ (0, C) = 1
        δ (1, A) = 2
        δ (2, R) = 3
        δ (3, R) = 4
        δ (4, O) = 5
        δ (5, T) = 6
        δ _      = 7
    -- L₂ = {"t"} ∪ {"ot"} = {"t", "ot"}
    e₃L₂ ∷ DFA (Fin₈, Fin₈) Alpha
    e₃L₂   = DFA.union (right e₃L₁ 5) (right e₃L₁ 4)
    -- L₁/L₂ = {"carro", "carr"}
    e₃L₁L₂ ∷ DFA Fin₈ Alpha
    e₃L₁L₂ = DFA.rquotient e₃L₁ e₃L₂
    -- {"carrot"} / {"t", "ot"} = {"carro", "carr"}
    e₃Tests ∷ [Bool]
    e₃Tests = [ Config.accepts e₃L₁   [C, A, R, R, O, T]                  -- test that "carrot" ∈ L₁
              , Config.accepts e₃L₂   [O, T]                              -- test that     "ot" ∈    L₂
              , Config.accepts e₃L₂   [T]                                 -- test that      "t" ∈    L₂
              , Config.accepts e₃L₁L₂ [C, A, R, R, O]                     -- test that "carro"  ∈ L₁/L₂
              , Config.accepts e₃L₁L₂ [C, A, R, R]                        -- test that "carr"   ∈ L₁/L₂
              , Prelude.take 2 (Config.language e₃L₁L₂) == [[C, A, R, R], [C, A, R, R, O]]
              ]

testDFAinvhomimage ∷ Test ()
testDFAinvhomimage = scope "DFA.invhomimage" . expect $ same
  where
    same ∷ Bool
    same = DFA.invhomimage h slide22 `DFA.equal` expected
      where
        -- slide 22 http://infolab.stanford.edu/~ullman/ialc/spr10/slides/rs2.pdf
        slide22 ∷ DFA Fin₃ Fin₂
        slide22 = DFA δ 0 (singleton 2)
          where
            δ (0, 0) = 1
            δ (0, 1) = 2
            δ (1, 0) = 0
            δ (1, 1) = 2
            δ (2, 0) = 0
            δ (2, 1) = 1        
        h ∷ Bool → [Fin₂]
        h False = [0,1]
        h True  = []
        expected ∷ DFA Fin₃ Bool 
        expected = DFA δ 0 (singleton 2)
          where
            δ ∷ (Fin₃, Bool) → Fin₃
            δ (0, False) = 2
            δ (0, True ) = 0
            δ (1, False) = 2
            δ (1, True ) = 1
            δ (2, False) = 2
            δ (2, True ) = 2

testREDropout ∷ Test ()
testREDropout = scope "RE.dropout" . expect $ and [test₁, test₂]
  where
    -- ℒ (A·(B·C)) ≟ {"AB", "AC", "BC"}
    test₁ ∷ Bool
    test₁ = expected == RE.language (expression')
      where
        -- ℒ (ε·(B·C) ∣ A·(ε·C ∣ B·ε)) = {"AB", "AC", "BC"}
        expression' ∷ RegExp Alpha
        expression' = RE.dropout expression
          where
            -- A·(B·C) is the regular expression such that
            -- ℒ (A·(B·C))             = {"ABC"}
            expression  ∷ RegExp Alpha
            expression  = RE.fromList [A, B, C]
        -- {"AB", "AC", "BC"}
        expected ∷ [[Alpha]]
        expected = [ [A, B]
                   , [A, C]
                   , [B, C]
                   ]
    -- ℒ (D ∣ (A·(B·C) ∣ E·F)) ≟ {"", "AB", "AC", "BC", "E", "F"}
    test₂ ∷ Bool
    test₂ = expected == RE.language (expression')
      where
        -- ℒ (ε ∣ ((ε·(B·C) ∣ A·(ε·C ∣ B·ε)) ∣ (ε·F ∣ E·ε)))
        expression' ∷ RegExp Alpha
        expression' = RE.dropout expression
          where
            -- ℒ (D ∣ (A·(B·C) ∣ E·F)) = {"ABC", "D", "EF"}
            expression  ∷ RegExp Alpha
            expression  = RE.fromWords [[A, B, C], [D], [E, F]]
        -- {"", "AB", "AC", "BC", "E", "F"}
        expected ∷ [[Alpha]]
        expected = [ []
                   , [A, B]
                   , [A, C]
                   , [B, C]
                   , [E]
                   , [F]
                   ]

-- Substitution
-- A Second Course in Formal Languages and Automata Theory (Pg 55, Example 3.3.4)
-- s(101) = (cd)*(a+ab)*(cd)*
testRESubstitution ∷ Test ()
testRESubstitution = scope "RE.>>=" . expect $ result == expected -- N.B. the use of structural equality is intentional here
  where
    original ∷ RegExp Fin₂
    original = RE.fromList [1, 0, 1]
    -- h(0) = {a, ab}*
    -- h(1) = (cd)*
    h ∷ Fin₂ → RegExp Fin₄
    h 0 = Star (Lit 0 :| RE.fromList [0,1])
    h 1 = Star (RE.fromList [2, 3])
    result ∷ RegExp Fin₄
    result = original >>= h
    -- (cd)*(a+ab)*(cd)*
    expected ∷ RegExp Fin₄
    expected =  Star (         RE.fromList [2, 3])
            :. (Star (Lit 0 :| RE.fromList [0, 1])
            :.  Star (         RE.fromList [2, 3]))

-- Example from: https://courses.engr.illinois.edu/cs373/fa2010/Exams/midterm1sol.pdf
testDFAPerfectShuffle ∷ Test ()
testDFAPerfectShuffle = scope "DFA.perfectShuffle" . expect $ l == expected
  where    
    -- {"1010"}
    l ∷ [[Fin₂]]
    l = Config.language ab
      where
        ab ∷ DFA (Set (Either Bool Bool), Set (Either Bool Bool), Bool) Fin₂
        ab = DFA.perfectShuffle a b
          where
            -- A = {"11"}
            a ∷ DFA (Set (Either Bool Bool)) Fin₂
            a = DFA.fromNFA (NFA.concatenate a' a')
              where
                -- {"1"}
                a' ∷ NFA Bool Fin₂
                a' = NFA.literal 1
            -- B = {"00"}
            b ∷ DFA (Set (Either Bool Bool)) Fin₂
            b = DFA.fromNFA (NFA.concatenate b' b')
              where
                -- {"0"}
                b' ∷ NFA Bool Fin₂
                b' = NFA.literal 0
    -- {"1010"}
    expected ∷ [[Fin₂]]
    expected = [[1, 0, 1, 0]]

-- TODO
-- Shuffle
-- A Second Course in Formal Languages and Automata Theory (Pg 57, Example 3.3.8)
testNFAshuffle ∷ Test ()
testNFAshuffle = scope "NFA.shuffle" . expect $ and [test]
  where
    ab_cd ∷ [[Alpha]]
    ab_cd = fmap (fmap abcdh) (Config.language abcd')
      where
        abh ∷ Bool → Alpha
        abh = bool A B
        cdh ∷ Bool → Alpha
        cdh = bool C D
        abcdh ∷ Either Bool Bool → Alpha
        abcdh = either abh cdh
        abcd' ∷ NFA (Fin₃, Fin₃) (Either Bool Bool)
        abcd' = NFA.asynchronous ab' cd'
          where
            ab' ∷ NFA Fin₃ Bool
            ab' = contramap abh ab
            cd' ∷ NFA Fin₃ Bool
            cd' = contramap cdh cd
    shuffled ∷ [[Alpha]]
    shuffled = [ [A, B, C, D]
               , [A, C, B, D]
               , [A, C, D, B]
               , [C, A, B, D]
               , [C, A, D, B]
               , [C, D, A, B]
               ]
    test ∷ Bool
    test = ab_cd == shuffled

-- Coinductive bisimulation (partial)
-- Either the bisimulation will succeed (on the given subset) or
-- it will produce a counter-example to the bisimulation
-- (i.e. a witness to the proof of its negation)
-- basically we take some subset of Σ⋆ to be sampled for
-- "observational equality", here meaning both `m` and `ℓ`
-- are in agreeance of which words to accept and reject.
testBisimSubset ∷ forall q s automaton p
                . (Finite q, Finite s, Configuration automaton q s p)
                ⇒ (automaton q s, ℒ s)
                → [[s]]
                → Test ()
testBisimSubset (m, ℓ) subset = scope "bisim" . expect $ isBisim
  where
    -- try to partition, into two parts, (a subset/sample of) Σ⋆:
    -- words tagged with `Right` (ℒ₁ ≡ ℒ₂)
    -- words tagged with `Left`  (ℒ₁ ≢ ℒ₂)
    witnesses ∷ [Either [s] [s]]
    witnesses = List.unfoldr bisim subset
      where
        accepts₁ ∷ [s] → Bool
        accepts₁ = Config.accepts   m
        accepts₂ ∷ [s] → Bool
        accepts₂ = Language.accepts ℓ
        bisim ∷ [[s]] → Maybe (Either [s] [s], [[s]])
        bisim []                                    = Nothing
        bisim (w : todo) | accepts₁ w == accepts₂ w = Just (Right w, todo)
        bisim (w : todo) | accepts₁ w ≠  accepts₂ w = Just (Left  w, todo)
    isBisim ∷ Bool
    isBisim = all isRight witnesses
    _isNotBisim ∷ Bool
    _isNotBisim = any isLeft witnesses
    -- The list of words on which `m` and `ℓ` did not agree
    -- i.e. a list of counter examples
    _negationProof ∷ [[s]]
    _negationProof = lefts witnesses

-- Composition of permutations
testComposeC ∷ Test ()
testComposeC = scope "Comparison.Compose" . expect $ and [test₁, test₂, test₃]
  where
    -- https://en.wikipedia.org/wiki/Permutation_group#Composition_of_permutations%E2%80%93the_group_product
    (p, q) = (listToComparison [1, 3, 0, 2, 4], listToComparison [4, 3, 2, 1, 0]) ∷ (Comparison Fin₅, Comparison Fin₅)

    -- https://youtu.be/3aNeCWRjh8I?t=211
    c₁ ∷ Comparison Fin₄ -- 1 3 4 2
    c₁ = listToComparison [0, 2, 3, 1]
    c₂ ∷ Comparison Fin₄ -- 4 3 2 1
    c₂ = listToComparison [3, 2, 1, 0]
    c₃ ∷ Comparison Fin₄ -- 2 4 3 1
    c₃ = c₁ `composeC` c₂
    c₄ ∷ Comparison Fin₄ -- 4 2 1 3
    c₄ = c₂ `composeC` c₁

    test₁ ∷ Bool
    test₁ = q `composeC` p == listToComparison [3, 1, 4, 2, 0] -- 4 2 5 3 1

    test₂ ∷ Bool
    test₂ = comparisonToList c₃ == [1, 3, 2, 0]
    test₃ ∷ Bool
    test₃ = comparisonToList c₄ == [3, 1, 0, 2]

-- test laws of group invert function
testGroupInvert ∷ Test ()
testGroupInvert = scope "Comparison.Invert" . expect $ and [test₁, test₂]
  where
    comparisons ∷ [Comparison Fin₅]
    comparisons = asList
    test₁ ∷ Bool
    test₁ = all (\c → (         c) `composeC` (G.invert c) == mempty) comparisons
    test₂ ∷ Bool
    test₂ = all (\c → (G.invert c) `composeC` (         c) == mempty) comparisons

-- test to check that `cycles` function gives back a lawful equivalence relation
testCycles ∷ Test ()
testCycles = scope "Comparison.Cycles" . expect $ and [test₁, test₂, test₃]
  where
    -- https://www.youtube.com/watch?v=MpKG6FmcIHk
    c₁ ∷ Comparison Fin₅ -- 3 5 4 1 2
    c₁ = listToComparison [2, 4, 3, 0, 1]
    test₁ ∷ Bool
    test₁ = getPredicate lawfulComparison c₁
    test₂ ∷ Bool
    test₂ = getPredicate lawful (cycles c₁)
    test₃ ∷ Bool
    test₃ = cycles c₁ == toEquivalence [0 NE.:| [2, 3], 1 NE.:| [4]]


-- https://arxiv.org/abs/0904.1097
-- Pg 3. Crossings and nestings in set partitions of classical types (v2)
testOpenersClosers ∷ Test ()
testOpenersClosers = scope "Equivalence.OpenersClosers" . expect $ and [test₀, test₁, test₂, test₃, test₄, test₅, test₆, test₇, test₈]
  where
    -- "Figure 1. A non-crossing set partition of [9]."
    -- {{1, 7, 9}, {2, 5, 6}, {3, 4}, {8}}
    figure₁ ∷ Equivalence Fin₉
    figure₁ = toEquivalence [ NE.fromList [0, 6, 8] -- {1, 7, 9}
                            , NE.fromList [1, 4, 5] -- {2, 5, 6}
                            , NE.fromList [2, 3]    -- {3, 4}
                            , NE.fromList [7]       -- {8}
                            ]
    -- "Figure 2. A non-nesting set partition of [9]."
    -- {{1, 4}, {2, 5, 7, 9}, {3, 6}, {8}}
    figure₂ ∷ Equivalence Fin₉
    figure₂ = toEquivalence [ NE.fromList [0, 3]       -- {1, 4}
                            , NE.fromList [1, 4, 6, 8] -- {2, 5, 7, 9}
                            , NE.fromList [2, 5]       -- {3, 6}
                            , NE.fromList [7]          -- {8}
                            ]
    -- {1, 2, 3, 5, 7}
    expectedOpeners ∷ [Fin₉]
    expectedOpeners = [0, 1, 2, 4, 6]
    -- {4, 5, 6, 7, 9}
    expectedClosers ∷ [Fin₉]
    expectedClosers = [3, 4, 5, 6, 8]
    -- {5, 7}
    expectedTransients ∷ [Fin₉]
    expectedTransients = [4, 6]
    -- {8}
    expectedSingletons ∷ [Fin₉]
    expectedSingletons = [7]
    -- Some assumptions that it shouldn't hurt to test explicitly
    -- TODO also test noncrossing and nonnesting predicates here?
    test₀ ∷ Bool
    test₀ = and [ getPredicate lawful figure₁
                , getPredicate lawful figure₂
                ]
    -- (openers {{1, 7, 9}, {2, 5, 6}, {3, 4}, {8}}) ≟ {1, 2, 3, 5, 7}
    test₁ ∷ Bool
    test₁ = openers figure₁ == expectedOpeners
    -- (openers {{1, 4}, {2, 5, 7, 9}, {3, 6}, {8}}) ≟ {1, 2, 3, 5, 7}
    test₂ ∷ Bool
    test₂ = openers figure₂ == expectedOpeners
    -- (closers {{1, 7, 9}, {2, 5, 6}, {3, 4}, {8}}) ≟ {4, 5, 6, 7, 9}
    test₃ ∷ Bool
    test₃ = closers figure₁ == expectedClosers
    -- (closers {{1, 4}, {2, 5, 7, 9}, {3, 6}, {8}}) ≟ {4, 5, 6, 7, 9}
    test₄ ∷ Bool
    test₄ = closers figure₂ == expectedClosers
    -- (transients {{1, 7, 9}, {2, 5, 6}, {3, 4}, {8}}) ≟ {5, 7}
    test₅ ∷ Bool
    test₅ = transients figure₁ == expectedTransients
    -- (transients {{1, 4}, {2, 5, 7, 9}, {3, 6}, {8}}) ≟ {5, 7}
    test₆ ∷ Bool
    test₆ = transients figure₂ == expectedTransients
    -- (singletons {{1, 7, 9}, {2, 5, 6}, {3, 4}, {8}}) ≟ {8}
    test₇ ∷ Bool
    test₇ = singletons figure₁ == expectedSingletons
    -- (singletons {{1, 4}, {2, 5, 7, 9}, {3, 6}, {8}}) ≟ {8}
    test₈ ∷ Bool
    test₈ = singletons figure₂ == expectedSingletons

-- TODO finish moving test
{-

import           Control.Comonad
import           Data.Functor.Compose
import           Data.Tree

-- there is obvious reuse we could use here, but for now this is manually expanded to illustrate
level₀ ∷ Tree ℕ
level₀ = Node 2 []
level₁ ∷ Tree ℕ
level₁ = Node 2 [ Node 2 []
                , Node 3 []
                ]
level₂ ∷ Tree ℕ
level₂ = Node 2 [ Node 2 [ Node 2 []
                         , Node 3 []
                         ]
                , Node 3 [ Node 3 []
                         , Node 3 []
                         , Node 4 []
                         ]
                ]
level₃ ∷ Tree ℕ
level₃ = Node 2 [ Node 2 [ Node 2 [ Node 2 []
                                  , Node 3 []
                                  ]
                         , Node 3 [ Node 3 []
                                  , Node 3 []
                                  , Node 4 []
                                  ]
                         ]
                , Node 3 [ Node 3 [ Node 3 []
                                  , Node 3 []
                                  , Node 4 []
                                  ]
                         , Node 3 [ Node 3 []
                                  , Node 3 []
                                  , Node 4 []
                                  ]
                         , Node 4 [ Node 4 []
                                  , Node 4 []
                                  , Node 4 []
                                  , Node 5 []
                                  ]
                         ]
                ]
--       L₀       L₁       L₂       L₃       L₄ ...
level₄ ∷ Tree ℕ
level₄ = Node 2 [ Node 2 [ Node 2 [ Node 2 [ Node 2 []
                                           , Node 3 []
                                           ]
                                  , Node 3 [ Node 3 []
                                           , Node 3 []
                                           , Node 4 []
                                           ]
                                  ]
                         , Node 3 [ Node 3 [ Node 3 []
                                           , Node 3 []
                                           , Node 4 []
                                           ]
                                  , Node 3 [ Node 3 []
                                           , Node 3 []
                                           , Node 4 []
                                           ]
                                  , Node 4 [ Node 4 []
                                           , Node 4 []
                                           , Node 4 []
                                           , Node 5 []
                                           ]
                                  ]
                         ]
                , Node 3 [ Node 3 [ Node 3 [ Node 3 []
                                           , Node 3 []
                                           , Node 4 []
                                           ]
                                  , Node 3 [ Node 3 []
                                           , Node 3 []
                                           , Node 4 []
                                           ]
                                  , Node 4 [ Node 4 []
                                           , Node 4 []
                                           , Node 4 []
                                           , Node 5 []
                                           ]
                                  ]
                         , Node 3 [ Node 3 [ Node 3 []
                                           , Node 3 []
                                           , Node 4 []
                                           ]
                                  , Node 3 [ Node 3 []
                                           , Node 3 []
                                           , Node 4 []
                                           ]
                                  , Node 4 [ Node 4 []
                                           , Node 4 []
                                           , Node 4 []
                                           , Node 5 []
                                           ]
                                  ]
                         , Node 4 [ Node 4 [ Node 4 []
                                           , Node 4 []
                                           , Node 4 []
                                           , Node 5 []
                                           ]
                                  , Node 4 [ Node 4 []
                                           , Node 4 []
                                           , Node 4 []
                                           , Node 5 []
                                           ]
                                  , Node 4 [ Node 4 []
                                           , Node 4 []
                                           , Node 4 []
                                           , Node 5 []
                                           ]
                                  , Node 5 [ Node 5 []
                                           , Node 5 []
                                           , Node 5 []
                                           , Node 5 []
                                           , Node 6 []
                                           ]
                                      ]
                             ]
                    ]
-}
