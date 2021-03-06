{-# OPTIONS_GHC -Wall                   #-}
-- Unfortunately, using Fin types breaks the warnings for incomplete patterns at this time
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE OverloadedStrings          #-}

import           Control.Applicative (Applicative (..))
import           Data.Bool (bool)
import           Data.Bool.Unicode ((∧))
import           Data.Either (isRight, isLeft, lefts)
import           Data.Eq.Unicode ((≠))
import           Data.Fin (toNatural)
import           Data.Function (on)
import           Data.Functor.Contravariant (Contravariant (..), Equivalence (..), Comparison (..), Predicate (..), defaultComparison)
import qualified Data.Group as G
import qualified Data.List as List
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE (NonEmpty (..), fromList, take)
import qualified Data.Set as Set (fromList)
import           Data.Set (Set, singleton, fromAscList)
import           Data.Set.Ordered (OSet)
import qualified Data.Set.Ordered as OSet ()
import           Data.Tagged (Tagged (..))
import           Data.Tree (Tree (..))
import qualified Data.Universe as U (cardinality)
import           Data.Void (Void)
import           EasyTest (Test, expect, expectEqual, pick, run, scope, tests)
import           Numeric.Natural.Unicode (ℕ)
import           DFA
import           NFA (NFA)
import qualified NFA
-- import qualified EFA
-- import qualified GFA
import           RegExp (RegExp (..))
import qualified RegExp as RE hiding (RegExp (..))
import           Common
import           Config
import           Finite
import           Language (ℒ)
import qualified Language
import           Examples (by3, by5, by5', minimal, ab, cd)

main ∷ IO ()
main = run suite

suite ∷ Test ()
suite = tests [ scope "main.FizzBuzz"              testFizzBuzz
              , scope "DFA.empty"                  testDFAEmptyLanguage
              , scope "DFA.epsilon"                testDFAEpsilon
              , scope "DFA.literal"                testDFALiteral
              , scope "DFA.union"                  testDFAUnion
              , scope "DFA.quotient"               testDFAquotient
              , scope "DFA.toRE"                   testDFAtoRE
              , scope "DFA.rquotient"              testDFArquotient
              , scope "DFA.invhomimage"            testDFAinvhomimage
              , scope "DFA.perfectShuffle"         testDFAPerfectShuffle
              , scope "DFA.toNFAShuffle"           testDFAtoNFAshuffle
              , scope "NFA.shuffle"                testNFAshuffle
              , scope "NFA.permutations"           testNFAPermutations
              , scope "RE.>>="                     testRESubstitution
              , scope "RE.dropout"                 testREDropout
              , scope "RE.derivative"              testREDerivative
              , scope "Language.onlyLength"        testLanguageOnlyLength
              , scope "bisim"                      testBisimSubset
              , scope "Comparison.Compose"         testComposeC
              , scope "Comparison.Invert"          testGroupInvert
              , scope "Comparison.Cycles"          testCycles
              , scope "Comparison.derangement"     testDerangement
              , scope "Comparisons.lawful"         testLawfulComparisons
              , scope "RGS.restricted"             testRestrictedPredicate  -- FIXME better name?
              , scope "paths"                      testRestrictedPaths      -- FIXME better name
              , scope "generateₙ"                  testGenerateN
              , scope "Equivalence.OpenersClosers" testOpenersClosers
              , scope "Equivalence.toRGS"          testEquivalencetoRGS
              , scope "Equivalence.bijection"      testEquivalenceBijection
              , scope "Equivalences.lawful"        testLawfulEquivalences
              , scope "Sequences.Arrangements"     testArrangementsInit
              , scope "Sequences.Bells"            testBellsInit
              , scope "Sequences.Catalan"          testCatalanInit
              , scope "Sequences.Factorials"       testFactorialsInit
              , scope "Sequences.Fib"              testFibInit
              , scope "Sequences.Naturals"         testNaturalsInit
              ]

-- Test that ordinary FizzBuzz has the same output as the FizzBuzz which uses DFA
testFizzBuzz ∷ Test ()
testFizzBuzz = expectEqual woDFA wDFA
  where
    -- FizzBuzz (without DFA)
    woDFA ∷ [String]
    woDFA = fmap fizzbuzz [1 .. 100]
      where
        fizz ∷ ℕ → Bool
        fizz = (==) 0 . (`mod` 3)
        buzz ∷ ℕ → Bool
        buzz = (==) 0 . (`mod` 5)
        fbzz ∷ ℕ → Bool
        fbzz = liftA2 (∧) fizz buzz
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
        fizz = accepts  by3                         . toDigits
        buzz ∷ ℕ → Bool
        buzz = accepts                         by5  . toDigits
        fbzz ∷ ℕ → Bool
        fbzz = accepts (by3 `DFA.intersection` by5) . toDigits
        fizzbuzz ∷ ℕ → String
        fizzbuzz n | fbzz n    = "FizzBuzz"
                   | fizz n    = "Fizz"
                   | buzz n    = "Buzz"
                   | otherwise = show n

testDFAEmptyLanguage ∷ Test ()
testDFAEmptyLanguage = expectEqual (Config.language DFA.empty)          ([      ] ∷ [[Bool]])

testDFAEpsilon       ∷ Test ()
testDFAEpsilon       = expectEqual (Config.language DFA.epsilon)        ([[    ]] ∷ [[Bool]])

testDFALiteral       ∷ Test ()
testDFALiteral       = expectEqual (Config.language (DFA.literal True)) ([[True]] ∷ [[Bool]])

-- N.B. Due to the nature of the `Set` type in GHC (namely the `Ord` constraint),
-- both tests should explicitly have the result ordered the same (i.e. {"<", "="}).
testDFAUnion         ∷ Test ()
testDFAUnion         = tests [test₁, test₂]
  where
    -- Three example languages, L₁, L₂, L₃
    -- L₁ = ℒ (eL₁) = {"<"}
    eL₁ ∷ DFA Ordering Ordering
    eL₁ = DFA.literal LT
    -- L₂ = ℒ (eL₂) = {"="}
    eL₂ ∷ DFA Ordering Ordering
    eL₂ = DFA.literal EQ
    -- L₃           = {"<", "="}
    eL₃ ∷ [[Ordering]]
    eL₃ = [[LT], [EQ]]
    -- (L₁ ∪ L₂) ≟ L₃
    test₁ ∷ Test ()
    test₁ = expectEqual (Config.language ltEq) eL₃
      where
        --        L₁ ∪ L₂
        -- =   {"<"} ∪ {"="}
        -- =   {"<",    "="}
        ltEq ∷ DFA (Ordering, Ordering) Ordering
        ltEq = DFA.union eL₂ eL₁
    -- (L₂ ∪ L₁) ≟ L₃
    test₂ ∷ Test ()
    test₂ = expectEqual (Config.language eqLt) eL₃
      where
        --      L₂ ∪ L₁
        -- = {"="} ∪ {"<"}
        -- = {"<",    "="}
        eqLt ∷ DFA (Ordering, Ordering) Ordering
        eqLt = DFA.union eL₁ eL₂

testDFAquotient ∷ Test ()
testDFAquotient = tests [test₁, test₂]
  where
    test₁ ∷ Test ()
    test₁ = expect (DFA.equal                (quotient minimal)                  minimal  )
    test₂ ∷ Test ()
    test₂ = expect ((<)       (size' (useful (quotient minimal))) (size' (useful minimal)))

testDFArquotient ∷ Test ()
testDFArquotient = tests [example₃, example₄]
  where
    -- See "Example 3" of https://math.stackexchange.com/questions/871662/finding-right-quotient-of-languages
    example₃ ∷ Test ()
    example₃ = scope "Example 3" $ tests [test₁, test₂, test₃, test₄, test₅, test₆]
      where
        -- ℒ₁ = {"carrot"}
        ℓ₁ ∷ DFA Fin₈ Alpha
        ℓ₁ = DFA δ 0 (singleton 6)
          where
            δ ∷ (Fin₈, Alpha) → Fin₈
            δ (0, C) = 1
            δ (1, A) = 2
            δ (2, R) = 3
            δ (3, R) = 4
            δ (4, O) = 5
            δ (5, T) = 6
            δ _      = 7
        -- ℒ₂ = {"ot"} ∪ {"t"} = {"ot", "t"}
        ℓ₂ ∷ DFA (Fin₈, Fin₈) Alpha
        ℓ₂ = DFA.union (right ℓ₁ 5) (right ℓ₁ 4)
        -- ℒ = ℒ₁ / ℒ₂ = {"carrot"} / {"ot", "t"} = {"carr", "carro"}
        ℓ ∷ DFA Fin₈ Alpha
        ℓ = DFA.rquotient ℓ₁ ℓ₂
        -- ℒ ≟ {"carr", "carro"}
        test₁ ∷ Test ()
        test₁ = expectEqual (Prelude.take 2 (Config.language ℓ)) [[C, A, R, R], [C, A, R, R, O]]
        -- "carro"  ∈? ℒ₁ / ℒ₂
        test₂ ∷ Test ()
        test₂ = expect      (Config.accepts ℓ  [C, A, R, R, O   ])
        -- "carr"   ∈? ℒ₁ / ℒ₂
        test₃ ∷ Test ()
        test₃ = expect      (Config.accepts ℓ  [C, A, R, R      ])
        -- "carrot" ∈? ℒ₁
        test₄ ∷ Test ()
        test₄ = expect      (Config.accepts ℓ₁ [C, A, R, R, O, T])
        --     "ot" ∈?      ℒ₂
        test₅ ∷ Test ()
        test₅ = expect      (Config.accepts ℓ₂ [            O, T])
        --      "t" ∈?      ℒ₂
        test₆ ∷ Test ()
        test₆ = expect      (Config.accepts ℓ₂ [               T])
    -- See "Example 4" of https://math.stackexchange.com/questions/871662/finding-right-quotient-of-languages
    example₄ ∷ Test ()
    example₄ = scope "Example 4" $ tests [test₁, test₂, test₃]
      where
        -- ℒ₁ ≟ {"012", "312"}
        test₁ ∷ Test ()
        test₁ = expectEqual expected (Config.language ℓ₁)
          where
            expected ∷ [[Fin₄]]
            expected = [[0, 1, 2], [3, 1, 2]]
        -- ℒ₂ ≟ {"2", "12"}
        test₂ ∷ Test ()
        test₂ = expectEqual expected (Config.language ℓ₂)
          where
            expected ∷ [[Fin₄]]
            expected = [[2], [1, 2]]
        -- ℒ ≟ {"0", "3", "01", "31"}
        test₃ ∷ Test ()
        test₃ = expectEqual expected (Config.language ℓ)
          where
            expected ∷ [[Fin₄]]
            expected = [[0], [3], [0, 1], [3, 1]]
            -- ℒ = ℒ₁ / ℒ₂ = {"0", "3", "01", "31"}
            ℓ ∷ DFA Fin₅ Fin₄
            ℓ = DFA.rquotient ℓ₁ ℓ₂
        -- ℒ₁ = {"012", "312"}
        ℓ₁ ∷ DFA Fin₅ Fin₄
        ℓ₁ = DFA δ 0 (singleton 3)
          where
            δ ∷ (Fin₅, Fin₄) → Fin₅
            δ (0, 0) = 1
            δ (0, 3) = 1
            δ (1, 1) = 2
            δ (2, 2) = 3
            δ _      = 4
        -- ℒ₂ = {"2", "12"}
        ℓ₂ ∷ DFA Fin₄ Fin₄
        ℓ₂ = contramap (toEnum . fromEnum) (DFA δ 0 (singleton 2))
          where
            δ ∷ (Fin₄, Fin₃) → Fin₄
            δ (0, 0) = 3
            δ (0, 1) = 1
            δ (0, 2) = 2
            δ (1, 0) = 3
            δ (1, 1) = 3
            δ (1, 2) = 2
            δ (2, 0) = 3
            δ (2, 1) = 3
            δ (2, 2) = 3
            δ (3, 0) = 3
            δ (3, 1) = 3
            δ (3, 2) = 3
            δ _      = 3 -- impossible

testDFAinvhomimage ∷ Test ()
testDFAinvhomimage = tests [test₁, test₂]
  where
    -- slide 22 http://infolab.stanford.edu/~ullman/ialc/spr10/slides/rs2.pdf
    test₁ ∷ Test ()
    test₁ = expect (expected `DFA.equal` DFA.invhomimage h m)
      where
        m ∷ DFA Fin₃ Fin₂
        m = DFA δ 0 (singleton 2)
          where
            δ ∷ (Fin₃, Fin₂) → Fin₃
            δ (0, 0) = 1
            δ (0, 1) = 2
            δ (1, 0) = 0
            δ (1, 1) = 2
            δ (2, 0) = 0
            δ (2, 1) = 1
        -- h(0) ↦ ab
        -- h(1) ↦ ε
        h ∷ Bool → [Fin₂]
        h False = [0, 1]
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
    -- A Second Course in Formal Languages and Automata Theory, Example 3.3.7
    -- h⁻¹({aba}) ≟ c*ac*bc*ac*
    test₂ ∷ Test ()
    test₂ = expect (expected == r)
      where
        -- c★·a·c★·b·c★·a·c★
        expected ∷ RegExp Fin₃
        expected = Star c :. (a :. (Star c :. (b :. (Star c :. (a :. Star c)))))
          where
            a ∷ RegExp Fin₃
            a = Lit 0
            b ∷ RegExp Fin₃
            b = Lit 1
            c ∷ RegExp Fin₃
            c = Lit 2
        -- 2★·0·2★·1·2★·0·2★
        r ∷ RegExp Fin₃
        r = DFA.toRE m'
          where
            m' ∷ DFA Fin₅ Fin₃
            m' = DFA.invhomimage h m
              where
                -- h(a) ↦ a
                -- h(b) ↦ b
                -- h(c) ↦ ε
                h ∷ Fin₃ → [Fin₂]
                h 0 = [0]
                h 1 = [1]
                h 2 = []
                -- ℒ(m) = {"aba"}
                m ∷ DFA Fin₅ Fin₂
                m = DFA δ 0 (singleton 3)
                  where
                    δ ∷ (Fin₅, Fin₂) → Fin₅
                    δ (0, 0) = 1
                    δ (0, 1) = 4
                    δ (1, 0) = 4
                    δ (1, 1) = 2
                    δ (2, 0) = 3
                    δ (2, 1) = 4
                    δ (3, 0) = 4
                    δ (3, 1) = 4
                    δ (4, 0) = 4
                    δ (4, 1) = 4

testREDropout ∷ Test ()
testREDropout = tests [test₁, test₂]
  where
    -- ℒ (dropout (A·(B·C))) ≟ {"AB", "AC", "BC"}
    test₁ ∷ Test ()
    test₁ = expectEqual expected (RE.language expression')
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
    test₂ ∷ Test ()
    test₂ = expectEqual expected (RE.language expression')
      where
        -- ℒ (ε ∣ ((ε·(B·C) ∣ A·(ε·C ∣ B·ε)) ∣ (ε·F ∣ E·ε)))
        expression' ∷ RegExp Alpha
        expression' = RE.dropout expression
          where
            -- ℒ (D ∣ (A·(B·C) ∣ E·F)) = {"ABC", "D", "EF"}
            expression  ∷ RegExp Alpha
            expression  = RE.fromWords [[A, B, C], [D], [E, F]]
        -- {ε, "AB", "AC", "BC", "E", "F"}
        expected ∷ [[Alpha]]
        expected = [ []
                   , [A, B]
                   , [A, C]
                   , [B, C]
                   , [E]
                   , [F]
                   ]

-- Test a few regular expression derivatives
testREDerivative ∷ Test ()
testREDerivative = tests [test₁, test₂, test₃, test₄]
  where
    -- ∂₀(0·1★) ≟ 1★
    test₁ ∷ Test ()
    test₁ = expectEqual expected (RE.derivative r 0)
      where
        r ∷ RegExp Fin₂
        r = RE.literal 0 RE.* RE.star (RE.literal 1)
        expected ∷ RegExp Fin₂
        expected = RE.star (RE.literal 1)
    -- ∂₀(0) ≟ ε
    test₂ ∷ Test ()
    test₂ = expectEqual expected (RE.derivative r 0)
      where
        r ∷ RegExp Fin₂
        r = RE.literal 0
        expected ∷ RegExp Fin₂
        expected = RE.one
    -- ∂₀(4∣5∣6) ≟ ∅
    test₃ ∷ Test ()
    test₃ = expectEqual expected (RE.derivative r 0)
      where
        r ∷ RegExp Fin₉
        r = RE.fromSet (Set.fromList [4, 5, 6])
        expected ∷ RegExp Fin₉
        expected = RE.zero
    -- ∂₅(4∣5∣6) ≟ ε
    test₄ ∷ Test ()
    test₄ = expectEqual expected (RE.derivative r 5)
      where
        r ∷ RegExp Fin₉
        r = RE.fromSet (Set.fromList [4, 5, 6])
        expected ∷ RegExp Fin₉
        expected = RE.one

-- Substitution
-- A Second Course in Formal Languages and Automata Theory, Example 3.3.4
-- s(101) = (cd)*(a+ab)*(cd)*
testRESubstitution ∷ Test ()
testRESubstitution = expectEqual result expected -- N.B. the use of structural equality is intentional here
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
-- Test that:
-- perfectShuffle {"11"} {"00"} = {"1010"}
testDFAPerfectShuffle ∷ Test ()
testDFAPerfectShuffle = expectEqual (Config.language shuffled) expected
  where
    -- perfectShuffle {"11"} {"00"}
    shuffled ∷ DFA (Set (Either Bool Bool), Set (Either Bool Bool), Bool) Fin₂
    shuffled = DFA.perfectShuffle aa bb
      where
        -- {"11"}
        aa ∷ DFA (Set (Either Bool Bool)) Fin₂
        aa = DFA.fromNFA (NFA.concatenate a a)
          where
            -- {"1"}
            a ∷ NFA Bool Fin₂
            a = NFA.literal 1
        -- {"00"}
        bb ∷ DFA (Set (Either Bool Bool)) Fin₂
        bb = DFA.fromNFA (NFA.concatenate b b)
          where
            -- {"0"}
            b ∷ NFA Bool Fin₂
            b = NFA.literal 0
    -- {"1010"}
    expected ∷ [[Fin₂]]
    expected = [[1, 0, 1, 0]]

testDFAtoRE ∷ Test ()
testDFAtoRE = expect (RE.equivalent (toRE by5) by5')

testDFAtoNFAshuffle ∷ Test ()
testDFAtoNFAshuffle = expectEqual ℓ shuffled
  where
    ℓ ∷ [[Fin₄]]
    ℓ = Config.language (DFA.toNFAShuffle ab' cd')
      where
        ab' ∷ DFA (Set Fin₃) Fin₄
        ab' = contramap (toEnum . fromEnum) (DFA.fromNFA ab)
        cd' ∷ DFA (Set Fin₃) Fin₄
        cd' = contramap (toEnum . fromEnum) (DFA.fromNFA cd)
    shuffled ∷ [[Fin₄]]
    shuffled = [ [0, 1, 2, 3]
               , [0, 2, 1, 3]
               , [0, 2, 3, 1]
               , [2, 0, 1, 3]
               , [2, 0, 3, 1]
               , [2, 3, 0, 1]
               ]

-- TODO
-- Shuffle
-- A Second Course in Formal Languages and Automata Theory (Pg 57, Example 3.3.8)
testNFAshuffle ∷ Test ()
testNFAshuffle = expectEqual ab_cd shuffled
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

-- Test that the `NFA.permutations` function generates the same set of words
-- as the GHC `List.permutatations` function does (after the `List.permutations` result is sorted).
testNFAPermutations ∷ Test ()
testNFAPermutations = tests [test₁, test₂, test₃]
  where
    -- ℒ(permutations {0, 1, 2}) ≟ {"012", "021", "102", "120", "201", "210"}
    test₁ ∷ Test ()
    test₁ = expectEqual (Config.language m) (List.sort (List.permutations asList))
      where
        m ∷ NFA (Set Fin₃) Fin₃
        m = NFA.permutations (asSet ∷ Set Fin₃)
    -- ℒ(NFA.permutations {1}) ≟ {"1"}
    test₂ ∷ Test ()
    test₂ = expectEqual (Config.language m) (List.sort (List.permutations asList))
      where
        m ∷ NFA (Set ()) ()
        m = NFA.permutations (asSet ∷ Set ())
    -- ℒ(NFA.permutations {0, 3}) ≟ {"03", "30"}
    test₃ ∷ Test ()
    test₃ = expectEqual (Config.language m) (List.sort (List.permutations l))
      where
        l ∷ [Fin₄]
        l = [0, 3]
        m ∷ NFA (Set Fin₄) Fin₄
        m = NFA.permutations s
          where
            s ∷ Set Fin₄
            s = fromAscList l

-- Coinductive bisimulation (partial)
-- Either the bisimulation will succeed (on the given subset) or
-- it will produce a counter-example to the bisimulation
-- (i.e. a witness to the proof of its negation)
-- basically we take some subset of Σ⋆ to be sampled for
-- "observational equality", here meaning both `m` and `ℓ`
-- are in agreeance of which words to accept and reject.
-- FIXME should write version which better utilizes EasyTest, probably should move the bisim part to another file :)
testBisimSubset' ∷ ∀ q s automaton p
                 . (Finite q, Finite s, Configuration automaton q s p)
                 ⇒ (automaton q s, ℒ s)
                 → [[s]]
                 → Bool
testBisimSubset' (m, ℓ) subset = isBisim
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

testBisimSubset ∷ Test ()
testBisimSubset = expect (testBisimSubset' (by5, DFA.toLanguage by5) (List.take 101 (freeMonoid asList)))

-- Some tests for composition of permutations
-- Note, the examples are converted to zero-based indices, but I leave the original one-based indices in the comments
testComposeC ∷ Test ()
testComposeC = tests [test₁, test₂]
  where
    -- https://en.wikipedia.org/wiki/Permutation_group#Composition_of_permutations%E2%80%93the_group_product
    -- 4 2 5 3 1 ≟ 5 4 3 2 1 ∘ 2 4 1 3 5
    test₁ ∷ Test ()
    test₁ = expectEqual expected (q `composeC` p)
      where
        -- 4 2 5 3 1
        expected ∷ Comparison Fin₅
        expected = listToComparison [3, 1, 4, 2, 0]
        -- 5 4 3 2 1
        q ∷ Comparison Fin₅
        q = listToComparison [4, 3, 2, 1, 0]
        -- 2 4 1 3 5
        p ∷ Comparison Fin₅
        p = listToComparison [1, 3, 0, 2, 4]
    -- https://youtu.be/3aNeCWRjh8I?t=211
    test₂ ∷ Test ()
    test₂ = tests [test₃, test₄]
      where
        -- 1 3 4 2
        c₁ ∷ Comparison Fin₄
        c₁ = listToComparison [0, 2, 3, 1]
        -- 4 3 2 1
        c₂ ∷ Comparison Fin₄
        c₂ = listToComparison [3, 2, 1, 0]
        -- 2 4 3 1 ≟ 1 3 4 2 ∘ 4 3 2 1
        test₃ ∷ Test ()
        test₃ = expectEqual expected (c₁ `composeC` c₂)
          where
            -- 2 4 3 1
            expected ∷ Comparison Fin₄
            expected = listToComparison [1, 3, 2, 0]
        -- 4 2 1 3 ≟ 4 3 2 1 ∘ 1 3 4 2
        test₄ ∷ Test ()
        test₄ = expectEqual expected (c₂ `composeC` c₁)
          where
            -- 4 2 1 3
            expected ∷ Comparison Fin₄
            expected = listToComparison [3, 1, 0, 2]

-- test laws of group invert function
testGroupInvert ∷ Test ()
testGroupInvert = tests [test₁, test₂]
  where
    comparisons ∷ [Comparison Fin₅]
    comparisons = asList
    -- TODO perhaps `nologging` can help keep this from taking over console output?
    -- TODO or can consider e.g. `comparisons ∷ [Comparison Fin₄]`
    test₁ ∷ Test ()
    test₁ = tests (fmap (\c → expectEqual mempty ((         c) `composeC` (G.invert c))) comparisons)
    test₂ ∷ Test ()
    test₂ = tests (fmap (\c → expectEqual mempty ((G.invert c) `composeC` (         c))) comparisons)

-- test to check that `cycles` function gives back a lawful equivalence relation
testCycles ∷ Test ()
testCycles = tests [test₁, test₂, test₃]
  where
    -- https://www.youtube.com/watch?v=MpKG6FmcIHk
    c₁ ∷ Comparison Fin₅ -- 3 5 4 1 2
    c₁ = listToComparison [2, 4, 3, 0, 1]
    test₁ ∷ Test ()
    test₁ = expect (getPredicate lawfulComparison c₁)
    test₂ ∷ Test ()
    test₂ = expect (getPredicate lawful (cycles c₁))
    test₃ ∷ Test ()
    test₃ = expectEqual (cycles c₁) (toEquivalence [0 NE.:| [2, 3], 1 NE.:| [4]])

testDerangement ∷ Test ()
testDerangement = tests [test₁, test₂]
  where
    -- see example given https://mathworld.wolfram.com/Derangement.html
    test₁ ∷ Test ()
    test₁ = expectEqual expected (List.filter (derangement (defaultComparison @ Fin₄)) (asList @ (Comparison Fin₄)))
      where
        expected ∷ [Comparison Fin₄] -- cf. 0, 1, 2, 3
        expected = fmap listToComparison [ [1, 0, 3, 2]
                                         , [1, 2, 3, 0]
                                         , [1, 3, 0, 2]
                                         , [2, 0, 3, 1]
                                         , [2, 3, 0, 1]
                                         , [2, 3, 1, 0]
                                         , [3, 0, 1, 2]
                                         , [3, 2, 0, 1]
                                         , [3, 2, 1, 0]
                                         ]
    -- Test that the reverse of an any arbitrarly picked permutation is a derangement of the original permutation
    -- N.B. This test is meant only for permutations on finite sets with cardinality > 1.
    test₂ ∷ Test ()
    test₂ = do
      c ← pick (asList @ (Comparison D6))
      expect (derangement c (reverseC c))

-- TODO can improve but this works for now
testLanguageOnlyLength ∷ Test ()
testLanguageOnlyLength = tests [test₁, test₂, test₃]
  where
    -- {"abc"} ≟ {ε, "a", "ab", "abc", "abcd"} `onlyLength` 3
    test₁ ∷ Test ()
    test₁ = expectEqual expected (Prelude.take 1 (Language.language (ℓ `Language.onlyLength` 3)))
      where
        -- {"abc"}
        expected ∷ [[Alpha]]
        expected = [[A, B, C]]
        -- {ε, "a", "ab", "abc", "abcd"}
        ℓ ∷ ℒ Alpha
        ℓ = Language.fromLang [[], [A], [A, B], [A, B, C], [A, B, C, D]]
    -- {ε} ≟ {ε, "a", "ab", "abc", "abcd"} `onlyLength` 0
    test₂ ∷ Test ()
    test₂ = expectEqual expected (Prelude.take 1 (Language.language (ℓ `Language.onlyLength` 0)))
      where
        -- {ε}
        expected ∷ [[Alpha]]
        expected = [[]]
        -- {ε, "a", "ab", "abc", "abcd"}
        ℓ ∷ ℒ Alpha
        ℓ = Language.fromLang [[], [A], [A, B], [A, B, C], [A, B, C, D]]
    -- {"0", "1", "2", "3"} ≟ {"0", "1", "2", "3", "10", "11", "12", "13", "20", "21", "22", "23"} `onlyLength` 1
    test₃ ∷ Test ()
    test₃ = expectEqual expected (Prelude.take 4 (Language.language (ℓ `Language.onlyLength` 1)))
      where
        -- {"0", "1", "2", "3"}
        expected ∷ [[Fin₄]]
        expected = [[0], [1], [2], [3]]
        -- {"0", "1", "2", "3", "10", "11", "12", "13", "20", "21", "22", "23"}
        ℓ ∷ ℒ Fin₄
        ℓ = Language.fromLang [[0], [1], [2], [3], [1, 0], [1, 1], [1, 2], [1, 3], [2, 0], [2, 1], [2, 2], [2, 3]]

-- Some tests for the `restricted` predicate.
-- Recall:
-- Checks the following two conditions:
-- a₁ = 0
-- and
-- aᵢ₊₁ ≤ 1 + max (a₁, a₂, ..., aᵢ)
testRestrictedPredicate ∷ Test ()
testRestrictedPredicate = tests [test₁, test₂]
  where
    p ∷ RGS Fin₄ → Bool
    p = getPredicate restricted . NE.fromList . getRGS
    {-
    λ> mapM_ print (asList @ (RGS Fin₄))
    [0,0,0,0]
    [0,0,0,1]
    [0,0,1,0]
    [0,0,1,1]
    [0,0,1,2]
    [0,1,0,0]
    [0,1,0,1]
    [0,1,0,2]
    [0,1,1,0]
    [0,1,1,1]
    [0,1,1,2]
    [0,1,2,0]
    [0,1,2,1]
    [0,1,2,2]
    [0,1,2,3]
    -}
    -- test that all automatically generated RGS are valid
    test₁ ∷ Test ()
    test₁ = expect (all p (asList @ (RGS Fin₄)))
    -- partition the entire space into valid/invalid by use of `p`
    test₂ ∷ Test ()
    test₂ = expect (all p valid ∧ none p invalid)
      where
        (valid, invalid) = List.partition p (fmap (RGS . fmap toNatural) ws) ∷ ([RGS Fin₄], [RGS Fin₄])
          where
            -- any possible string, w, where Σ = {0, 1, 2 ,3} s.t. length w == 4
            -- i.e. [0,0,0,0], [0,0,0,1], ..., [3,3,3,3]
            -- TODO probably better way to do this with vec, but this works for now
            ws ∷ [[Fin₄]]
            ws = upToLength 5 (freeMonoidFrom 4 (asList @ Fin₄))

-- TODO update with actual RGS use instead
-- Test that all paths in the generated index tree are restricted
testRestrictedPaths ∷ Test ()
testRestrictedPaths = tests [test₁, test₂]
  where
    test₁ ∷ Test ()
    test₁ = expect (all (getPredicate restricted) (paths (generateᵢ 3)))
    test₂ ∷ Test ()
    test₂ = expect (all (getPredicate restricted) (paths (generateᵢ 4)))

-- "For example, the restricted growth function 0,1,1,2,0,3,1 defines the set partition {{1,5}, {2,3,7}, {4}, {6}}"
-- https://www8.cs.umu.se/kurser/TDBAfl/VT06/algorithms/BOOK/BOOK4/NODE153.HTM
testEquivalencetoRGS ∷ Test ()
testEquivalencetoRGS = expectEqual (toRGS (toEquivalence [0 NE.:| [4], 1 NE.:| [2, 6], 3 NE.:| [], 5 NE.:| []]))
                                   (RGS [0, 1, 1, 2, 0, 3, 1] ∷ RGS Fin₇)

testEquivalenceBijection ∷ Test ()
testEquivalenceBijection = tests [test₀, test₁, test₂, test₃, test₄, test₅]
  where
    -- bijection (toRGS ∷ Equivalence () → RGS ()) (fromRGS ∷ RGS () → Equivalence ())
    test₀ ∷ Test ()
    test₀ = expect (bijection (toRGS   @ ())   (fromRGS @ ()))
    test₁ ∷ Test ()
    test₁ = expect (bijection (toRGS   @ Suit) (fromRGS @ Suit))
    test₂ ∷ Test ()
    test₂ = expect (bijection (toRGS   @ Fin₅) (fromRGS @ Fin₅))
    test₃ ∷ Test ()
    test₃ = expect (bijection (fromRGS @ ())   (toRGS   @ ()))
    test₄ ∷ Test ()
    test₄ = expect (bijection (fromRGS @ Suit) (toRGS   @ Suit))
    test₅ ∷ Test ()
    test₅ = expect (bijection (fromRGS @ Fin₅) (toRGS   @ Fin₅))

-- https://arxiv.org/abs/0904.1097
-- Pg 3. Crossings and nestings in set partitions of classical types (v2)
testOpenersClosers ∷ Test ()
testOpenersClosers = tests [test₀, test₁, test₂, test₃, test₄, test₅, test₆, test₇, test₈]
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
    test₀ ∷ Test ()
    test₀ = tests [ expect (getPredicate lawful figure₁)
                  , expect (getPredicate lawful figure₂)
                  ]
    -- (openers {{1, 7, 9}, {2, 5, 6}, {3, 4}, {8}}) ≟ {1, 2, 3, 5, 7}
    test₁ ∷ Test ()
    test₁ = expectEqual expectedOpeners (openers figure₁)
    -- (openers {{1, 4}, {2, 5, 7, 9}, {3, 6}, {8}}) ≟ {1, 2, 3, 5, 7}
    test₂ ∷ Test ()
    test₂ = expectEqual expectedOpeners (openers figure₂)
    -- (closers {{1, 7, 9}, {2, 5, 6}, {3, 4}, {8}}) ≟ {4, 5, 6, 7, 9}
    test₃ ∷ Test ()
    test₃ = expectEqual expectedClosers (closers figure₁)
    -- (closers {{1, 4}, {2, 5, 7, 9}, {3, 6}, {8}}) ≟ {4, 5, 6, 7, 9}
    test₄ ∷ Test ()
    test₄ = expectEqual expectedClosers (closers figure₂)
    -- (transients {{1, 7, 9}, {2, 5, 6}, {3, 4}, {8}}) ≟ {5, 7}
    test₅ ∷ Test ()
    test₅ = expectEqual expectedTransients (transients figure₁)
    -- (transients {{1, 4}, {2, 5, 7, 9}, {3, 6}, {8}}) ≟ {5, 7}
    test₆ ∷ Test ()
    test₆ = expectEqual expectedTransients (transients figure₂)
    -- (singletons {{1, 7, 9}, {2, 5, 6}, {3, 4}, {8}}) ≟ {8}
    test₇ ∷ Test ()
    test₇ = expectEqual expectedSingletons (singletons figure₁)
    -- (singletons {{1, 4}, {2, 5, 7, 9}, {3, 6}, {8}}) ≟ {8}
    test₈ ∷ Test ()
    test₈ = expectEqual expectedSingletons (singletons figure₂)

-- Test the `generateₙ` function against some known (and easy to check visually) inputs
testGenerateN ∷ Test ()
testGenerateN = tests [test₀, test₁, test₂, test₃, test₄]
  where
    test₀ ∷ Test ()
    test₀ = scope "level₀" . expectEqual level₀ $ generateₙ 0
    test₁ ∷ Test ()
    test₁ = scope "level₁" . expectEqual level₁ $ generateₙ 1
    test₂ ∷ Test ()
    test₂ = scope "level₂" . expectEqual level₂ $ generateₙ 2
    test₃ ∷ Test ()
    test₃ = scope "level₃" . expectEqual level₃ $ generateₙ 3
    test₄ ∷ Test ()
    test₄ = scope "level₄" . expectEqual level₄ $ generateₙ 4
    -- λ> printTree level₀
    -- 2
    level₀ ∷ Tree ℕ
    level₀ = pure 2
    -- λ> printTree level₁
    -- 2┬─┐
    --  │ │
    --  2 3
    level₁ ∷ Tree ℕ
    level₁ = Node 2 [ level₀
                    , pure 3
                    ]
    -- λ> printTree level₂
    -- 2──┬─────┐
    --    │     │
    --  2┬┴┐ 3┬─┼─┐
    --   │ │  │ │ │
    --   2 3  3 3 4
    level₂ ∷ Tree ℕ
    level₂ = Node 2 [ level₁
                    , Node 3 [ pure 3
                             , pure 3
                             , pure 4
                             ]
                    ]
    -- λ> printTree level₃
    -- 2─────┬────────────────┐
    --       │                │
    --  2──┬─┴───┐  3───┬─────┴┬───────┐
    --     │     │      │      │       │
    --   2┬┴┐ 3┬─┼─┐ 3┬─┼─┐ 3┬─┼─┐ 4┬─┬┴┬─┐
    --    │ │  │ │ │  │ │ │  │ │ │  │ │ │ │
    --    2 3  3 3 4  3 3 4  3 3 4  4 4 4 5
    level₃ ∷ Tree ℕ
    level₃ = Node 2 [ level₂
                    , Node 3 [ Node 3 [ pure 3
                                      , pure 3
                                      , pure 4
                                      ]
                             , Node 3 [ pure 3
                                      , pure 3
                                      , pure 4
                                      ]
                             , Node 4 [ pure 4
                                      , pure 4
                                      , pure 4
                                      , pure 5
                                      ]
                             ]
                    ]
    -- λ> printTree level₄
    -- 2────────────┬───────────────────────────────────────────────────────┐
    --              │                                                       │
    --  2─────┬─────┴──────────┐            3──────────┬────────────────────┴─┬─────────────────────────────┐
    --        │                │                       │                      │                             │
    --   2──┬─┴───┐  3───┬─────┴┬───────┐    3───┬─────┴┬───────┐   3───┬─────┴┬───────┐   4────┬────────┬──┴─────┬─────────┐
    --      │     │      │      │       │        │      │       │       │      │       │        │        │        │         │
    --    2┬┴┐ 3┬─┼─┐ 3┬─┼─┐ 3┬─┼─┐ 4┬─┬┴┬─┐  3┬─┼─┐ 3┬─┼─┐ 4┬─┬┴┬─┐ 3┬─┼─┐ 3┬─┼─┐ 4┬─┬┴┬─┐ 4┬─┬┴┬─┐ 4┬─┬┴┬─┐ 4┬─┬┴┬─┐ 5┬─┬─┼─┬─┐
    --     │ │  │ │ │  │ │ │  │ │ │  │ │ │ │   │ │ │  │ │ │  │ │ │ │  │ │ │  │ │ │  │ │ │ │  │ │ │ │  │ │ │ │  │ │ │ │  │ │ │ │ │
    --     2 3  3 3 4  3 3 4  3 3 4  4 4 4 5   3 3 4  3 3 4  4 4 4 5  3 3 4  3 3 4  4 4 4 5  4 4 4 5  4 4 4 5  4 4 4 5  5 5 5 5 6
    level₄ ∷ Tree ℕ
    level₄ = Node 2 [ level₃
                    , Node 3 [ Node 3 [ Node 3 [ pure 3
                                               , pure 3
                                               , pure 4
                                               ]
                                      , Node 3 [ pure 3
                                               , pure 3
                                               , pure 4
                                               ]
                                      , Node 4 [ pure 4
                                               , pure 4
                                               , pure 4
                                               , pure 5
                                               ]
                                      ]
                             , Node 3 [ Node 3 [ pure 3
                                               , pure 3
                                               , pure 4
                                               ]
                                      , Node 3 [ pure 3
                                               , pure 3
                                               , pure 4
                                               ]
                                      , Node 4 [ pure 4
                                               , pure 4
                                               , pure 4
                                               , pure 5
                                               ]
                                      ]
                             , Node 4 [ Node 4 [ pure 4
                                               , pure 4
                                               , pure 4
                                               , pure 5
                                               ]
                                      , Node 4 [ pure 4
                                               , pure 4
                                               , pure 4
                                               , pure 5
                                               ]
                                      , Node 4 [ pure 4
                                               , pure 4
                                               , pure 4
                                               , pure 5
                                               ]
                                      , Node 5 [ pure 5
                                               , pure 5
                                               , pure 5
                                               , pure 5
                                               , pure 6
                                               ]
                                      ]
                                ]
                        ]

-- Test lawfulness of the generated equivalence relations (with some arbitrarily picked types).
testLawfulEquivalences ∷ Test ()
testLawfulEquivalences = tests [test₁, test₂, test₃, test₄, test₅, test₆]
  where
    test₁ ∷ Test ()
    test₁ = scope "eqMaybe"  . expect . getPredicate lawful $ eqMaybe  @ Fin₄
    test₂ ∷ Test ()
    test₂ = scope "eqEither" . expect . getPredicate lawful $ eqEither @ Fin₄ @ Ordering
    test₃ ∷ Test ()
    test₃ = scope "eqThese"  . expect . getPredicate lawful $ eqThese  @ Fin₄ @ Ordering
    test₄ ∷ Test ()
    test₄ = scope "eqSmash"  . expect . getPredicate lawful $ eqSmash  @ Fin₄ @ Ordering
    test₅ ∷ Test ()
    test₅ = scope "eqCan"    . expect . getPredicate lawful $ eqCan    @ Fin₄ @ Ordering
    test₆ ∷ Test ()
    test₆ = scope "eqWedge"  . expect . getPredicate lawful $ eqWedge  @ Fin₄ @ Ordering

-- Test lawfulness of the generated total orderings (with some arbitrarily picked types).
testLawfulComparisons ∷ Test ()
testLawfulComparisons = tests [test₁, test₂, test₃, test₄, test₅, test₆]
  where
    test₁ ∷ Test ()
    test₁ = scope "cmpMaybe"  . expect . getPredicate lawfulComparison $ cmpMaybe  @ Fin₄
    test₂ ∷ Test ()
    test₂ = scope "cmpEither" . expect . getPredicate lawfulComparison $ cmpEither @ Fin₄ @ Ordering
    test₃ ∷ Test ()
    test₃ = scope "cmpThese"  . expect . getPredicate lawfulComparison $ cmpThese  @ Fin₄ @ Ordering
    test₄ ∷ Test ()
    test₄ = scope "cmpSmash"  . expect . getPredicate lawfulComparison $ cmpSmash  @ Fin₄ @ Ordering
    test₅ ∷ Test ()
    test₅ = scope "cmpCan"    . expect . getPredicate lawfulComparison $ cmpCan    @ Fin₄ @ Ordering
    test₆ ∷ Test ()
    test₆ = scope "cmpWedge"  . expect . getPredicate lawfulComparison $ cmpWedge  @ Fin₄ @ Ordering

-- Test OSet's cardinalities matches the initial segment of the arrangements sequence as specified via the 3rd party reference
testArrangementsInit ∷ Test ()
testArrangementsInit = expect (((==) `on` NE.take 16) expected cardinalities)
  where
    -- https://oeis.org/A000522
    expected ∷ NonEmpty ℕ
    expected = 1
       NE.:| [ 2
             , 5
             , 16
             , 65
             , 326
             , 1957
             , 13700
             , 109601
             , 986410
             , 9864101
             , 108505112
             , 1302061345
             , 16926797486
             , 236975164805
             , 3554627472076
             , 56874039553217
             , 966858672404690
             , 17403456103284421
             , 330665665962404000
             , 6613313319248080001
             , 138879579704209680022
             , 3055350753492612960485
             , 70273067330330098091156
             ]
    cardinalities ∷ NonEmpty ℕ
    cardinalities = unTagged (U.cardinality ∷ Tagged (OSet Void)  ℕ)
            NE.:| [ unTagged (U.cardinality ∷ Tagged (OSet Fin₁)  ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₂)  ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₃)  ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₄)  ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₅)  ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₆)  ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₇)  ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₈)  ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₉)  ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₁₀) ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₁₁) ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₁₂) ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₁₃) ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₁₄) ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₁₅) ℕ)
                  , unTagged (U.cardinality ∷ Tagged (OSet Fin₁₆) ℕ)
                  ]

-- Test that the initial segment of the non-empty list generated by `bells` matches the 3rd party reference
testBellsInit ∷ Test ()
testBellsInit = expect (((==) `on` NE.take 27) expected bells)
  where
    -- https://oeis.org/A000142/
    expected ∷ NonEmpty ℕ
    expected = 1
       NE.:| [ 1
             , 2
             , 5
             , 15
             , 52
             , 203
             , 877
             , 4140
             , 21147
             , 115975
             , 678570
             , 4213597
             , 27644437
             , 190899322
             , 1382958545
             , 10480142147
             , 82864869804
             , 682076806159
             , 5832742205057
             , 51724158235372
             , 474869816156751
             , 4506715738447323
             , 44152005855084346
             , 445958869294805289
             , 4638590332229999353
             , 49631246523618756274
             ]

-- Test that the initial segment of the non-empty list generated by `catalan` matches the 3rd party reference
testCatalanInit ∷ Test ()
testCatalanInit = expect (((==) `on` NE.take 31) expected catalan)
  where
    -- https://oeis.org/A000108
    expected ∷ NonEmpty ℕ
    expected = 1
       NE.:| [ 1
             , 2
             , 5
             , 14
             , 42
             , 132
             , 429
             , 1430
             , 4862
             , 16796
             , 58786
             , 208012
             , 742900
             , 2674440
             , 9694845
             , 35357670
             , 129644790
             , 477638700
             , 1767263190
             , 6564120420
             , 24466267020
             , 91482563640
             , 343059613650
             , 1289904147324
             , 4861946401452
             , 18367353072152
             , 69533550916004
             , 263747951750360
             , 1002242216651368
             , 3814986502092304
             ]

-- Test that the initial segment generated by the (non-empty list) `factorials` matches the 3rd party reference
testFactorialsInit ∷ Test ()
testFactorialsInit = expect (((==) `on` NE.take 23) expected factorials)
  where
    -- https://oeis.org/A000142/
    expected ∷ NonEmpty ℕ
    expected = 1
       NE.:| [ 1
             , 2
             , 6
             , 24
             , 120
             , 720
             , 5040
             , 40320
             , 362880
             , 3628800
             , 39916800
             , 479001600
             , 6227020800
             , 87178291200
             , 1307674368000
             , 20922789888000
             , 355687428096000
             , 6402373705728000
             , 121645100408832000
             , 2432902008176640000
             , 51090942171709440000
             , 1124000727777607680000
             ]

-- Test that the initial segment of the non-empty list generated by `fibonacci` matches the 3rd party reference
testFibInit ∷ Test ()
testFibInit = expect (((==) `on` NE.take 40) expected fibonacci)
  where
    -- https://oeis.org/A000045
    expected ∷ NonEmpty ℕ
    expected = 0
       NE.:| [ 1
             , 1
             , 2
             , 3
             , 5
             , 8
             , 13
             , 21
             , 34
             , 55
             , 89
             , 144
             , 233
             , 377
             , 610
             , 987
             , 1597
             , 2584
             , 4181
             , 6765
             , 10946
             , 17711
             , 28657
             , 46368
             , 75025
             , 121393
             , 196418
             , 317811
             , 514229
             , 832040
             , 1346269
             , 2178309
             , 3524578
             , 5702887
             , 9227465
             , 14930352
             , 24157817
             , 39088169
             , 63245986
             , 102334155
             ]

-- Test that the initial segment of the non-empty list generated by `naturals` matches the 3rd party reference
testNaturalsInit ∷ Test ()
testNaturalsInit = expect (((==) `on` NE.take 78) expected naturals)
  where
    -- https://oeis.org/A001477
    expected ∷ NonEmpty ℕ
    expected = 0
       NE.:| [ 1
             , 2
             , 3
             , 4
             , 5
             , 6
             , 7
             , 8
             , 9
             , 10
             , 11
             , 12
             , 13
             , 14
             , 15
             , 16
             , 17
             , 18
             , 19
             , 20
             , 21
             , 22
             , 23
             , 24
             , 25
             , 26
             , 27
             , 28
             , 29
             , 30
             , 31
             , 32
             , 33
             , 34
             , 35
             , 36
             , 37
             , 38
             , 39
             , 40
             , 41
             , 42
             , 43
             , 44
             , 45
             , 46
             , 47
             , 48
             , 49
             , 50
             , 51
             , 52
             , 53
             , 54
             , 55
             , 56
             , 57
             , 58
             , 59
             , 60
             , 61
             , 62
             , 63
             , 64
             , 65
             , 66
             , 67
             , 68
             , 69
             , 70
             , 71
             , 72
             , 73
             , 74
             , 75
             , 76
             , 77
             ]
