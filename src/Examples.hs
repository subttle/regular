{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- Unfortunately, using Fin types breaks the warnings for incomplete patterns at this time
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module Examples where

import           DFA
import qualified NFA
import qualified EFA
-- import qualified GFA
import qualified RegExp as RE
import           Finite
import           Data.Set
import           Data.Set.Unicode
import           Data.Bool.Unicode
import           Data.Eq.Unicode
import           Data.Either

-- A DFA which accepts all binary strings ending in 1
endsWith1 ∷ DFA Bool Fin₂
endsWith1 = DFA { delta = δ
                , q0    = False
                , fs    = singleton True
                } where δ (False, 0) = False
                        δ (False, 1) = True
                        δ (True,  0) = False
                        δ (True,  1) = True

-- The set of strings which end in [0, 1]
endsWith01 ∷ NFA.NFA Fin₄ Fin₂
endsWith01 = NFA.NFA { NFA.delta = δ
                     , NFA.q0    = 0
                     , NFA.fs    = singleton 2
                     } where δ ∷ (Fin₄, Fin₂) → Set Fin₄
                             δ (0, 0) = fromList  [0, 1]
                             δ (0, 1) = singleton 0
                             δ (1, 1) = singleton 2
                             δ _      = (∅)

-- https://en.wikipedia.org/wiki/File:NFAexample.svg
-- Generates the language where w has an even number of 0s or an even number of 1s
even0or1 ∷ EFA.EFA Fin₅ Fin₂
even0or1 = EFA.EFA { EFA.delta = δ
                   , EFA.q0    = 0
                   , EFA.fs    = fromList [1, 3]
                   } where δ (0, Nothing) = fromList  [1, 3]
                           δ (1, Just  0) = singleton 2
                           δ (1, Just  1) = singleton 1
                           δ (2, Just  0) = singleton 1
                           δ (2, Just  1) = singleton 2
                           δ (3, Just  0) = singleton 3
                           δ (3, Just  1) = singleton 4
                           δ (4, Just  0) = singleton 4
                           δ (4, Just  1) = singleton 3
                           δ (_, _      ) = (∅)

-- A number is divisible by 5 iff its last digit is 0 or 5
by5 ∷ DFA Bool Fin₁₀
by5 = DFA { delta = δ
          , q0    = False
          , fs    = singleton True
          } where δ (_, 0) = True
                  δ (_, 5) = True
                  δ _      = False

-- A regular expression to match the language of the `by5` DFA
-- [0-9]★[0+5]
-- ((0+(1+(2+(3+(4+(5+(6+(7+(8+9))))))))))★·(0+5)
by5' ∷ RE.RegExp Fin₁₀
by5' = RE.star RE.dot RE.* RE.fromSet (fromList [0, 5])

-- A number is divisible by 3 iff the sum of its digits is divisible by 3
-- The state we are in is the (running total % 3)
-- (We add a single starting state `Left ()` to avoid accepting the empty string.)
by3 ∷ DFA (Either () Fin₃) Fin₁₀
by3 = DFA { delta = Right . toEnum . (`mod` 3) . \(q, digit) → fromEnum (fromRight 0 q) + fromEnum digit
          , q0    = Left ()
          , fs    = singleton (Right 0)
          }

{-          Ross Ashby's "ghost taming" automaton [1]
 (example from "Synchronizing automata and the Černý conjecture" [2])
 "In each minute, each noise is either sounding or silent—
they show no degrees. What each will do during the ensuing
minute depends, in the following exact way, on what
has been happening during the preceding minute:

The Singing, in the succeeding minute, will go on as it was
during the preceding minute (sounding or silent) unless there
was organ-playing with no Laughter, in which case it will
change to the opposite (sounding to silent, or vice versa).

As for the Laughter, if there was incense burning, then it
will sound or not according as the Singing was sounding or
not (so that the Laughter copies the Singing a minute later).
If however there was no incense burning, the Laughter will
do the opposite of what the Singing did.
At this minute of writing, the Laughter and Singing are
troth sounding. Please tell me what manipulations of
incense and organ I should make to get the house quiet, and
to keep it so"
[1] An Introduction to Cybernetics, W. Ross Ashby, 1956, pg 60-61
[2] http://csseminar.imkn.urfu.ru/tarragona_volkov2008.pdf             -}

-- The states, i.e. Q : (Bool × Bool) represent the status of the ghosts singing and laughing, respectively,
-- and the alphabet, i.e. Σ : (Bool × Bool) represents the actions of playing an organ and lighting incense, respectively.
-- Each word accepted by the automaton is a solution
haunted ∷ DFA (Bool, Bool) (Bool, Bool)
haunted = DFA { delta = δ
              -- Start with ghosts both singing and laughing
              , q0    =           (True,  True)
              -- End with ghosts neither singing nor laughing
              , fs    = singleton (False, False)
              } where δ ((singing, laughing), (organ, incense)) = (if not laughing ∧ organ then not singing else singing, if incense then singing else not singing)

-- Farmer's problem
-- The goal of the problem is to get all the items safely and efficiently to the opposite
-- side of the river. The farmer may carry at most one item across at a time.
-- ...
-- Each type wraps a Bool which when True stands for "is across the river" and
-- when False stands for "is not across the river".
-- The states are the locations of the person, the fox, the hen, and the bag. Each one may be either across or not across the river.
-- The symbols are transitions across the river, either the person by themself, or one of fox, hen, or bag (accompanied by the person).
data Objects = Per | Fox | Hen | Bag deriving (Eq, Ord, Enum, Bounded, Show)
instance Finite Objects where
  asList = [Per, Fox, Hen, Bag]

-- The states are the locations of the person, the fox, the hen, and the bag. Each one may be either left of the river or right of the river.
-- The symbols are transitions, either the person by themself, or one of animals, accompanied by the person
farmer ∷ DFA (Bool, Bool, Bool, Bool) Objects
farmer = DFA { delta = δ
             , q0    =           (False, False, False, False)  -- Everything starts not across the river
             , fs    = singleton (True,  True,  True,  True )  -- We are finished when everything is safely across the river
             } where -- foxEatsHen = p ≠ f ∧ f == h -- If the fox and the hen are on the same side and the person isn't watching the fox, then the hen gets eaten.
                     -- henEatsBag = p ≠ h ∧ h == b -- If the hen and the bag are on the same side and the person isn't watching the hen, then the bag gets eaten.
                     -- illegal x  = p ≠ x          -- only allow x to transition with the farmer
                     δ ((p, f, h, b), Per) = if         (p ≠ f ∧ f == h) ∨ (p ≠ h ∧ h == b) then (p, f, h, b) else (not p,     f,     h,     b)
                     δ ((p, f, h, b), Fox) = if p ≠ f ∨                    (p ≠ h ∧ h == b) then (p, f, h, b) else (not p, not f,     h,     b)
                     δ ((p, f, h, b), Hen) = if p ≠ h ∨ (p ≠ f ∧ f == h)                    then (p, f, h, b) else (not p,     f, not h,     b)
                     δ ((p, f, h, b), Bag) = if p ≠ b ∨ (p ≠ f ∧ f == h) ∨ (p ≠ h ∧ h == b) then (p, f, h, b) else (not p,     f,     h, not b)

-- Wikipedia version of the riddle
-- https://en.wikipedia.org/wiki/Fox,_goose_and_bag_of_beans_puzzle
-- https://en.wikipedia.org/wiki/File:Fox_goose_beans_puzzle_visualisation.svg
farmerw ∷ NFA.NFA (Bool, Bool, Bool) Objects
farmerw = NFA.NFA { NFA.delta = δ
                  , NFA.q0    =           (False, False, False)  -- Everything starts not across the river
                  , NFA.fs    = singleton (True,  True,  True )  -- We are finished when everything is safely across the river
                  } where
                          -- fgb
                          δ ((False, False, False), Hen) = singleton (False, True,  False)
                          -- fGb
                          δ ((False, True,  False), Fox) = singleton (True,  True,  False)
                          δ ((False, True,  False), Bag) = singleton (False, True,  True)
                          -- FGb
                          δ ((True,  True,  False), Hen) = singleton (True,  False, False)
                          -- Fgb
                          δ ((True,  False, False), Bag) = singleton (True,  False, True)
                          -- FgB
                          δ ((True,  False, True),  Bag) = singleton (True,  False, False)
                          δ ((True,  False, True),  Hen) = singleton (True,  True,  True)
                          δ ((True,  False, True),  Fox) = singleton (False, False, True)
                          -- fGB
                          δ ((False, True,  True),  Hen) = singleton (False, False, True)
                          -- fgB
                          δ ((False, False, True),  Fox) = singleton (True,  False, True)
                          δ _                            = (∅)

-- https://www.researchgate.net/publication/269628569_DNA_Pattern_Analysis_using_Finite_Automata
figure2 ∷ NFA.NFA Fin₈ DNA
figure2 = NFA.NFA { NFA.delta = δ
                  , NFA.q0    = 0
                  , NFA.fs    = singleton 7
                  } where δ (0, Adenine)  = singleton  6
                          δ (0, Cytosine) = singleton  3
                          δ (0, Thymine)  = singleton  3
                          δ (0, Guanine)  = fromList  [1, 3, 6]
                          δ (1, Adenine)  = fromList  [2, 5]
                          δ (1, Cytosine) = fromList  [1, 3]
                          δ (1, Thymine)  = singleton  5
                          δ (1, Guanine)  = fromList  [2, 5]
                          δ (2, Guanine)  = (∅)
                          δ (2, _)        = singleton  7
                          δ (3, Cytosine) = fromList  [3, 7]
                          δ (3, Thymine)  = fromList  [3, 4, 7, 1]
                          δ (3, _)        = fromList  [4, 7]
                          δ (4, Guanine)  = singleton  7
                          δ (4, _)        = fromList  [2, 7]
                          δ (5, _)        = singleton  7
                          δ (6, Thymine)  = fromList  [2, 7]
                          δ (6, Guanine)  = singleton  7
                          δ (6, _)        = fromList  [6, 7]
                          δ (7, _)        = (∅)

-- Generates the language [[1], [2], [3]]
oneTwoThree ∷ EFA.EFA Bool Fin₄
oneTwoThree = EFA.EFA { EFA.delta = δ
                      , EFA.q0    = False
                      , EFA.fs    = singleton True
                      } where δ (False, Just 1) = singleton True
                              δ (False, Just 2) = singleton True
                              δ (False, Just 3) = singleton True
                              δ _               = (∅)

-- An EFA which accepts only strings which start with 0 and end with 1
-- A similar example is given in this video lecture https://youtu.be/yzb4J7oSyLA
startsWith0endsWith1 ∷ EFA.EFA Fin₄ Fin₂
startsWith0endsWith1 = EFA.EFA { EFA.delta = δ
                               , EFA.q0    = 0
                               , EFA.fs    = singleton 2
                               } where δ (0, Just  0) = singleton 1
                                       δ (0, Just  1) = singleton 3

                                       δ (1, Just  0) = singleton 1
                                       δ (1, Just  1) = singleton 2

                                       δ (2, Just  0) = singleton 1
                                       δ (2, Just  1) = singleton 2

                                       δ (3, Just  0) = singleton 3
                                       δ (3, Just  1) = singleton 3
                                       δ (_, Nothing) = (∅)

-- A DFA which accepts all binary strings starting with 0
startsWith0 ∷ DFA Fin₃ Fin₂
startsWith0 = DFA { delta = δ
                  , q0    = 0
                  , fs    = singleton 1
                  } where δ (0, 0) = 1
                          δ (0, 1) = 2

                          δ (1, 0) = 1
                          δ (1, 1) = 1

                          δ (2, 0) = 2
                          δ (2, 1) = 2

-- Coursera Stanford Automata, NFA lecture
-- http://spark-public.s3.amazonaws.com/automata/slides/4_fa3.pdf
data RB = Red | Black deriving (Eq, Enum, Ord, Bounded, Show)
instance Finite RB
board ∷ NFA.NFA Fin₉ RB
board = NFA.NFA { NFA.delta = δ
                , NFA.q0    = 0
                , NFA.fs    = singleton 8
                } where δ (0,   Red) = fromList  [1, 3]
                        δ (0, Black) = singleton  4
                        δ (1,   Red) = fromList  [3, 5]
                        δ (1, Black) = fromList  [0, 2, 4]
                        δ (2,   Red) = fromList  [1, 5]
                        δ (2, Black) = singleton  4
                        δ (3,   Red) = fromList  [1, 7]
                        δ (3, Black) = fromList  [0, 4, 6]
                        δ (4,   Red) = fromList  [1, 3, 5, 7]
                        δ (4, Black) = fromList  [0, 2, 6, 8]
                        δ (5,   Red) = fromList  [1, 7]
                        δ (5, Black) = fromList  [2, 4, 8]
                        δ (6,   Red) = fromList  [3, 7]
                        δ (6, Black) = singleton  4
                        δ (7,   Red) = fromList  [3, 5]
                        δ (7, Black) = fromList  [4, 6, 8]
                        δ (8,   Red) = fromList  [5, 7]
                        δ (8, Black) = singleton  4

data Decimal = Plus | Minus | Period deriving (Eq, Ord, Enum, Bounded)
instance Finite Decimal
instance Show Decimal where
  show Plus   = "+"
  show Minus  = "-"
  show Period = "."

-- HMU Figure 2.18 Pg.73
hmu218 ∷ EFA.EFA Fin₆ (Either Decimal Fin₁₀)
hmu218 = EFA.EFA { EFA.delta = δ
                 , EFA.q0    = 0
                 , EFA.fs    = singleton 5
                 } where δ (0, Just (Left   Plus)) = singleton 1
                         δ (0, Just (Left  Minus)) = singleton 1
                         δ (0,            Nothing) = singleton 1
                         δ (1, Just (Left Period)) = singleton 2
                         δ (1, Just (Right     _)) = fromList  [1, 4]
                         δ (2, Just (Right     _)) = singleton 3
                         δ (3, Just (Right     _)) = singleton 3
                         δ (3,            Nothing) = singleton 5
                         δ (4, Just (Left Period)) = singleton 3
                         δ  _                      = (∅)

-- [[0],[1],[0,1],[0,0,0],[0,1,1],[1,1,1]
ex144 ∷ EFA.EFA Fin₆ Fin₂
ex144 = EFA.EFA { EFA.delta = δ
                , EFA.q0    = 0
                , EFA.fs    = singleton 3
                } where δ (0, Just  0) = singleton 4
                        δ (0, Just  1) = singleton 1
                        δ (1, Just  1) = singleton 2
                        δ (1, Nothing) = singleton 3
                        δ (2, Just  1) = singleton 3
                        δ (4, Just  0) = singleton 5
                        δ (4, Nothing) = fromList  [1, 2]
                        δ (5, Just  0) = singleton 3
                        δ _            = (∅)

closuresExample ∷ EFA.EFA Fin₇ Fin₂
closuresExample = EFA.EFA { EFA.delta = δ
                          , EFA.q0 = 0
                          , EFA.fs = singleton 3
                          } where δ (0, Nothing) = fromList  [1, 2]
                                  δ (1, Just  1) = singleton 4
                                  δ (1, Nothing) = singleton 3
                                  δ (2, Just  0) = singleton 6
                                  δ (2, Nothing) = singleton 5
                                  δ (5, Nothing) = singleton 0
                                  δ _            = (∅)

-- https://youtu.be/1GZOzTJOBuM
minimal ∷ DFA Fin₅ Fin₂
minimal = DFA { delta = δ
              , q0    = 0
              , fs    = singleton 4
              } where δ (0, 0) = 1
                      δ (0, 1) = 2
                      δ (1, 0) = 1
                      δ (1, 1) = 3
                      δ (2, 0) = 1
                      δ (2, 1) = 2
                      δ (3, 0) = 1
                      δ (3, 1) = 4
                      δ (4, 0) = 1
                      δ (4, 1) = 2

-- https://youtu.be/TvMEX2htBYw
minimal' ∷ DFA Fin₁₀ Fin₂
minimal' = DFA { delta = δ
               , q0    = 0
               , fs    = fromList [5, 6]
               } where δ (0, 0) = 7
                       δ (0, 1) = 1
                       δ (1, 0) = 7
                       δ (1, 1) = 0
                       δ (2, 0) = 4
                       δ (2, 1) = 5
                       δ (3, 0) = 4
                       δ (3, 1) = 5
                       δ (4, 0) = 6
                       δ (4, 1) = 6
                       δ (5, 0) = 5
                       δ (5, 1) = 5
                       δ (6, 0) = 6
                       δ (6, 1) = 5
                       δ (7, 0) = 2
                       δ (7, 1) = 2
                       δ _      = 9

-- http://i.stack.imgur.com/AD6WJ.png
exactly20s ∷ DFA Fin₄ Fin₂
exactly20s = DFA { delta = δ
                 , q0    = 0
                 , fs    = singleton 2
                 } where δ (0, 0) = 1
                         δ (0, 1) = 0

                         δ (1, 0) = 2
                         δ (1, 1) = 1

                         δ (2, 0) = 3
                         δ (2, 1) = 2

                         δ (3, 0) = 3
                         δ (3, 1) = 3

-- http://i.stack.imgur.com/AD6WJ.png
atleast21s ∷ DFA Fin₃ Fin₂
atleast21s = DFA { delta = δ
                 , q0    = 0
                 , fs    = singleton 2
                 } where δ (0, 0) = 0
                         δ (0, 1) = 1

                         δ (1, 0) = 1
                         δ (1, 1) = 2

                         δ (2, 0) = 2
                         δ (2, 1) = 2

exactly20sANDatleast21s ∷ DFA (Fin₄, Fin₃) Fin₂
exactly20sANDatleast21s  = exactly20s `DFA.intersection` atleast21s

-- The language ["123456789"]
digitsNFA ∷ NFA.NFA Fin₁₀ Fin₁₀
digitsNFA = NFA.NFA { NFA.delta = δ
                    , NFA.q0 = 0
                    , NFA.fs = singleton 9
                    } where δ (0, 1) = singleton 1
                            δ (1, 2) = singleton 2
                            δ (2, 3) = singleton 3
                            δ (3, 4) = singleton 4
                            δ (4, 5) = singleton 5
                            δ (5, 6) = singleton 6
                            δ (6, 7) = singleton 7
                            δ (7, 8) = singleton 8
                            δ (8, 9) = singleton 9
                            δ _      = (∅)

