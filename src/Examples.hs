{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs, ExplicitForAll, UnicodeSyntax, InstanceSigs, MultiParamTypeClasses #-}

module Examples where

import           DFA
import qualified NFA
import qualified EFA
import qualified GFA
import qualified RE
-- import qualified PDA
-- import qualified TM
import           Common
import           Finite
import           Data.Set
import           Data.Set.Unicode
import           Data.Bool.Unicode
import           Data.Eq.Unicode
import           Data.Void
import           Data.Maybe
import           Data.Functor.Contravariant

import           Data.Fin
import           Data.Type.Nat as N

data Binary = Zero' | One' deriving (Eq, Enum, Bounded, Ord)
instance Finite Binary
instance Show Binary where
  show Zero' = "0"
  show  One' = "1"

-- A DFA which accepts all binary strings ending in 1
endsWith1 ∷ DFA Bool Binary
endsWith1 = DFA { delta = delta
                , q0    = False
                , fs    = singleton True
                } where delta (False, Zero') = False
                        delta (False,  One') = True
                        delta (True,  Zero') = False
                        delta (True,   One') = True

-- The set of strings which end in [Zero', One']
endsWith01 ∷ NFA.NFA Fin₃ Binary
endsWith01 = NFA.NFA { NFA.delta = delta
                     , NFA.q0    = Fin₃ 0
                     , NFA.fs    = singleton (Fin₃ 2)
                     } where delta (Fin₃ 0, Zero') = fromList  [Fin₃ 0, Fin₃ 1]
                             delta (Fin₃ 0,  One') = singleton (Fin₃ 0)
                             delta (Fin₃ 1,  One') = singleton (Fin₃ 2)
                             delta _               = (∅)

-- The set of strings which end in [0, 1]
endsWith01' ∷ NFA.NFA (Fin N.Nat4) (Fin N.Nat2)
endsWith01' = NFA.NFA { NFA.delta = delta
                     , NFA.q0    = 0
                     , NFA.fs    = singleton 2
                     } where delta ∷ (Fin N.Nat4, Fin N.Nat2) → Set (Fin N.Nat4)
                             delta (0, 0) = fromList  [0, 1]
                             delta (0, 1) = singleton 0
                             delta (9, 1) = singleton 2
                             delta _      = (∅)

-- https://en.wikipedia.org/wiki/File:NFAexample.svg
-- Generates the language where w has an even number of 0s or an even number of 1s
even0or1 ∷ EFA.EFA Fin₅ Binary
even0or1 = EFA.EFA { EFA.delta = delta
                   , EFA.q0    = Fin₅ 0
                   , EFA.fs    = fromList [Fin₅ 1, Fin₅ 3]
                   } where delta (Fin₅ 0,    Nothing) = fromList  [Fin₅ 1, Fin₅ 3]
                           delta (Fin₅ 1, Just Zero') = singleton (Fin₅ 2)
                           delta (Fin₅ 1, Just  One') = singleton (Fin₅ 1)
                           delta (Fin₅ 2, Just Zero') = singleton (Fin₅ 1)
                           delta (Fin₅ 2, Just  One') = singleton (Fin₅ 2)
                           delta (Fin₅ 3, Just Zero') = singleton (Fin₅ 3)
                           delta (Fin₅ 3, Just  One') = singleton (Fin₅ 4)
                           delta (Fin₅ 4, Just Zero') = singleton (Fin₅ 4)
                           delta (Fin₅ 4, Just  One') = singleton (Fin₅ 3)
                           delta (Fin₅ _,          _) = (∅)

-- A number, n, either ends in 5 or 0 (when n % 5 = 0), or it doesn't (n % 5 ≠ 0).
by5 ∷ DFA (Fin N.Nat2) Digits
by5 = DFA { delta = delta
          , q0    = 0
          , fs    = singleton 1
          } where delta (_, Zero) = 1
                  delta (_, Five) = 1
                  delta _         = 0

-- A regular expression to match the language of the divisibleBy5 DFA
-- [0-9]★[0+5]
-- ((0+(1+(2+(3+(4+(5+(6+(7+(8+9))))))))))★·(0+5)
by5' ∷ RE.RegExp Digits
by5' = RE.star RE.dot RE.* RE.fromSet (fromList [Zero, Five])

-- A number is divisible by 3 if and only if the sum of its digits is divisible by 3
-- The state we are in is the (running total % 3)
-- (We add a single starting state `Left ()` to avoid accepting the empty string.)
by3 ∷ DFA (Either () (Fin N.Nat3)) Digits
by3 = DFA { delta = Right . toEnum . delta
          , q0    = Left ()
          , fs    = singleton (Right 0)
          } where delta (Left  (), digit) = (0          + fromEnum digit) `mod` 3
                  delta (Right  q, digit) = (fromEnum q + fromEnum digit) `mod` 3

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
[2] http://csseminar.kadm.usu.ru/tarragona_volkov2008.pdf                      -}

-- Ghosts:  Singing and Laughing
newtype Sing    = Sing    Bool deriving (Eq, Ord, Enum, Bounded)
newtype Laugh   = Laugh   Bool deriving (Eq, Ord, Enum, Bounded)
-- Actions: play organ, light incense
newtype Organ   = Organ   Bool deriving (Eq, Ord, Enum, Bounded)
newtype Incense = Incense Bool deriving (Eq, Ord, Enum, Bounded)
instance Finite Sing
instance Finite Laugh
instance Finite Organ
instance Finite Incense
instance Show Sing where
  show (Sing      True) = "Singing"
  show (Sing     False) = "Not Singing"
instance Show Laugh where
  show (Laugh     True) = "Laughing"
  show (Laugh    False) = "Not Laughing"
instance Show Organ where
  show (Organ     True) = "Playing organ"
  show (Organ    False) = "Not playing organ"
instance Show Incense where
  show (Incense   True) = "Burning incense"
  show (Incense  False) = "Not burning incense"

haunted ∷ DFA (Sing, Laugh) (Organ, Incense)
haunted = DFA { delta = delta
              , q0    =           (Sing  True, Laugh  True)
              , fs    = singleton (Sing False, Laugh False)
              } where delta ((Sing singing, Laugh laughing), (Organ organ, Incense incense)) = (left, right)
                                                         where left  = Sing  ((if not laughing ∧ organ then not else  id) singing)
                                                               right = Laugh ((if incense              then id  else not) singing)

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
                        δ _ = (∅)

-- https://www.researchgate.net/publication/269628569_DNA_Pattern_Analysis_using_Finite_Automata
figure2 :: NFA.NFA Fin₈ DNA
figure2 = NFA.NFA { NFA.delta = δ
                  , NFA.q0    = Fin₈ 0
                  , NFA.fs    = singleton (Fin₈ 7)
                  } where δ (Fin₈ 0, Adenine)  = singleton (Fin₈ 6)
                          δ (Fin₈ 0, Cytosine) = singleton (Fin₈ 3)
                          δ (Fin₈ 0, Thymine)  = singleton (Fin₈ 3)
                          δ (Fin₈ 0, Guanine)  = fromList  [Fin₈ 1, Fin₈ 3, Fin₈ 6]
                          δ (Fin₈ 1, Adenine)  = fromList  [Fin₈ 2, Fin₈ 5]
                          δ (Fin₈ 1, Cytosine) = fromList  [Fin₈ 1, Fin₈ 3]
                          δ (Fin₈ 1, Thymine)  = singleton (Fin₈ 5)
                          δ (Fin₈ 1, Guanine)  = fromList  [Fin₈ 2, Fin₈ 5]
                          δ (Fin₈ 2, Guanine)  = (∅)
                          δ (Fin₈ 2, _)        = singleton (Fin₈ 7)
                          δ (Fin₈ 3, Cytosine) = fromList  [Fin₈ 3, Fin₈ 7]
                          δ (Fin₈ 3, Thymine)  = fromList  [Fin₈ 3, Fin₈ 4, Fin₈ 7, Fin₈ 1]
                          δ (Fin₈ 3, _)        = fromList  [Fin₈ 4, Fin₈ 7]
                          δ (Fin₈ 4, Guanine)  = singleton (Fin₈ 7)
                          δ (Fin₈ 4, _)        = fromList  [Fin₈ 2, Fin₈ 7]
                          δ (Fin₈ 5, _)        = singleton (Fin₈ 7)
                          δ (Fin₈ 6, Thymine)  = fromList  [Fin₈ 2, Fin₈ 7]
                          δ (Fin₈ 6, Guanine)  = singleton (Fin₈ 7)
                          δ (Fin₈ 6, _)        = fromList  [Fin₈ 6, Fin₈ 7]
                          δ (Fin₈ 7, _)        = (∅)

-- Generates the language [[1], [2], [3]]
oneTwoThree ∷ EFA.EFA Bool Digits
oneTwoThree = EFA.EFA { EFA.delta = delta
                      , EFA.q0    = False
                      , EFA.fs    = singleton True
                      } where delta (False, Just   One) = singleton True
                              delta (False, Just   Two) = singleton True
                              delta (False, Just Three) = singleton True
                              delta _                   = (∅)

-- An EFA which accepts only strings which start with 0 and end with 1
-- A similar example is given in this video lecture https://youtu.be/yzb4J7oSyLA
startsWith0endsWith1 ∷ EFA.EFA Fin₄ Binary
startsWith0endsWith1 = EFA.EFA { EFA.delta = delta
                               , EFA.q0    = Fin₄ 0
                               , EFA.fs    = singleton (Fin₄ 2)
                               } where delta (Fin₄ 0, Just Zero') = singleton (Fin₄ 1)
                                       delta (Fin₄ 0, Just  One') = singleton (Fin₄ 3)

                                       delta (Fin₄ 1, Just Zero') = singleton (Fin₄ 1)
                                       delta (Fin₄ 1, Just  One') = singleton (Fin₄ 2)

                                       delta (Fin₄ 2, Just Zero') = singleton (Fin₄ 1)
                                       delta (Fin₄ 2, Just  One') = singleton (Fin₄ 2)

                                       delta (Fin₄ 3, Just Zero') = singleton (Fin₄ 3)
                                       delta (Fin₄ 3, Just  One') = singleton (Fin₄ 3)
                                       delta (Fin₄ _,    Nothing) = (∅)

-- A DFA which accepts all binary strings starting with 0
startsWith0 ∷ DFA Fin₃ Binary
startsWith0 = DFA { delta = delta
                  , q0    = Fin₃ 0
                  , fs    = singleton (Fin₃ 1)
                  } where delta (Fin₃ 0, Zero') = Fin₃ 1
                          delta (Fin₃ 0,  One') = Fin₃ 2

                          delta (Fin₃ 1, Zero') = Fin₃ 1
                          delta (Fin₃ 1,  One') = Fin₃ 1

                          delta (Fin₃ 2, Zero') = Fin₃ 2
                          delta (Fin₃ 2,  One') = Fin₃ 2

-- Coursera Stanford Automata, NFA lecture
-- http://spark-public.s3.amazonaws.com/automata/slides/4_fa3.pdf
data RB = Red | Black deriving (Eq, Enum, Ord, Bounded, Show)
instance Finite RB
board ∷ NFA.NFA Fin₉ RB
board = NFA.NFA { NFA.delta = delta
                , NFA.q0    = Fin₉ 0
                , NFA.fs    = singleton (Fin₉ 8)
                } where delta (Fin₉ 0,   Red) = fromList  [Fin₉ 1, Fin₉ 3]
                        delta (Fin₉ 0, Black) = singleton (Fin₉ 4)
                        delta (Fin₉ 1,   Red) = fromList  [Fin₉ 3, Fin₉ 5]
                        delta (Fin₉ 1, Black) = fromList  [Fin₉ 0, Fin₉ 2, Fin₉ 4]
                        delta (Fin₉ 2,   Red) = fromList  [Fin₉ 1, Fin₉ 5]
                        delta (Fin₉ 2, Black) = singleton (Fin₉ 4)
                        delta (Fin₉ 3,   Red) = fromList  [Fin₉ 1, Fin₉ 7]
                        delta (Fin₉ 3, Black) = fromList  [Fin₉ 0, Fin₉ 4, Fin₉ 6]
                        delta (Fin₉ 4,   Red) = fromList  [Fin₉ 1, Fin₉ 3, Fin₉ 5, Fin₉ 7]
                        delta (Fin₉ 4, Black) = fromList  [Fin₉ 0, Fin₉ 2, Fin₉ 6, Fin₉ 8]
                        delta (Fin₉ 5,   Red) = fromList  [Fin₉ 1, Fin₉ 7]
                        delta (Fin₉ 5, Black) = fromList  [Fin₉ 2, Fin₉ 4, Fin₉ 8]
                        delta (Fin₉ 6,   Red) = fromList  [Fin₉ 3, Fin₉ 7]
                        delta (Fin₉ 6, Black) = singleton (Fin₉ 4)
                        delta (Fin₉ 7,   Red) = fromList  [Fin₉ 3, Fin₉ 5]
                        delta (Fin₉ 7, Black) = fromList  [Fin₉ 4, Fin₉ 6, Fin₉ 8]
                        delta (Fin₉ 8,   Red) = fromList  [Fin₉ 5, Fin₉ 7]
                        delta (Fin₉ 8, Black) = singleton (Fin₉ 4)

data Decimal = Plus | Minus | Period deriving (Eq, Ord, Enum, Bounded)
instance Finite Decimal
instance Show Decimal where
  show Plus = "+"
  show Minus = "-"
  show Period = "."

-- HMU Figure 2.18 Pg.73
hmu218 ∷ EFA.EFA Fin₆ (Either Decimal Digits)
hmu218 = EFA.EFA { EFA.delta = delta
                 , EFA.q0    = Fin₆ 0
                 , EFA.fs    = singleton (Fin₆ 5)
                 } where delta (Fin₆ 0, Just (Left   Plus)) = singleton (Fin₆ 1)
                         delta (Fin₆ 0, Just (Left  Minus)) = singleton (Fin₆ 1)
                         delta (Fin₆ 0,            Nothing) = singleton (Fin₆ 1)
                         delta (Fin₆ 1, Just (Left Period)) = singleton (Fin₆ 2)
                         delta (Fin₆ 1, Just (Right     _)) = fromList  [Fin₆ 1, Fin₆ 4]
                         delta (Fin₆ 2, Just (Right     _)) = singleton (Fin₆ 3)
                         delta (Fin₆ 3, Just (Right     _)) = singleton (Fin₆ 3)
                         delta (Fin₆ 3,            Nothing) = singleton (Fin₆ 5)
                         delta (Fin₆ 4, Just (Left Period)) = singleton (Fin₆ 3)
                         delta  _                           = (∅)

-- An EFA to recognize my version of the "Real" numbers
reals ∷ EFA.EFA Fin₅ (Either Decimal Digits)
reals = EFA.EFA { EFA.delta = delta
                , EFA.q0    = Fin₅ 0
                , EFA.fs    = singleton (Fin₅ 4)
                } where delta (Fin₅ 0, Just (Left   Plus)) = singleton (Fin₅ 1)
                        delta (Fin₅ 0, Just (Left  Minus)) = singleton (Fin₅ 1)
                        delta (Fin₅ 1, Just (Right     _)) = fromList  [Fin₅ 1, Fin₅ 2]
                        delta (Fin₅ 2, Just (Left Period)) = singleton (Fin₅ 3)
                        delta (Fin₅ 3, Just (Right     _)) = fromList  [Fin₅ 3, Fin₅ 4]
                        delta  _                           = (∅)

-- [[0],[1],[0,1],[0,0,0],[0,1,1],[1,1,1]
ex144 ∷ EFA.EFA Fin₆ Binary
ex144 = EFA.EFA { EFA.delta = delta
                , EFA.q0    = Fin₆ 0
                , EFA.fs    = singleton (Fin₆ 3)
                } where delta (Fin₆ 0, Just Zero') = singleton (Fin₆ 4)
                        delta (Fin₆ 0, Just  One') = singleton (Fin₆ 1)
                        delta (Fin₆ 1, Just  One') = singleton (Fin₆ 2)
                        delta (Fin₆ 1,    Nothing) = singleton (Fin₆ 3)
                        delta (Fin₆ 2, Just  One') = singleton (Fin₆ 3)
                        delta (Fin₆ 4, Just Zero') = singleton (Fin₆ 5)
                        delta (Fin₆ 4,    Nothing) = fromList  [Fin₆ 1, Fin₆ 2]
                        delta (Fin₆ 5, Just Zero') = singleton (Fin₆ 3)
                        delta _                    = (∅)

closuresExample ∷ EFA.EFA Fin₇ Binary
closuresExample = EFA.EFA { EFA.delta = delta
                          , EFA.q0 = Fin₇ 0
                          , EFA.fs = singleton (Fin₇ 3)
                          } where delta (Fin₇ 0,    Nothing) = fromList  [Fin₇ 1, Fin₇ 2]
                                  delta (Fin₇ 1, Just  One') = singleton (Fin₇ 4)
                                  delta (Fin₇ 1,    Nothing) = singleton (Fin₇ 3)
                                  delta (Fin₇ 2, Just Zero') = singleton (Fin₇ 6)
                                  delta (Fin₇ 2,    Nothing) = singleton (Fin₇ 5)
                                  delta (Fin₇ 5,    Nothing) = singleton (Fin₇ 0)
                                  delta _                    = (∅)

-- https://youtu.be/1GZOzTJOBuM
minimal ∷ DFA Fin₆ Binary
minimal = DFA { delta = delta
              , q0    = Fin₆ 0
              , fs    = singleton (Fin₆ 4)
              } where delta (Fin₆ 0, Zero') = Fin₆ 1
                      delta (Fin₆ 0,  One') = Fin₆ 2
                      delta (Fin₆ 1, Zero') = Fin₆ 1
                      delta (Fin₆ 1,  One') = Fin₆ 3
                      delta (Fin₆ 2, Zero') = Fin₆ 1
                      delta (Fin₆ 2,  One') = Fin₆ 2
                      delta (Fin₆ 3, Zero') = Fin₆ 1
                      delta (Fin₆ 3,  One') = Fin₆ 4
                      delta (Fin₆ 4, Zero') = Fin₆ 1
                      delta (Fin₆ 4,  One') = Fin₆ 2

-- https://youtu.be/TvMEX2htBYw
minimal' ∷ DFA Digits Binary
minimal' = DFA { delta = delta
               , q0    = Zero
               , fs    = fromList [Five, Six]
               } where delta ( Zero, Zero') = Seven
                       delta ( Zero,  One') = One
                       delta (  One, Zero') = Seven
                       delta (  One,  One') = Zero
                       delta (  Two, Zero') = Four
                       delta (  Two,  One') = Five
                       delta (Three, Zero') = Four
                       delta (Three,  One') = Five
                       delta ( Four, Zero') = Six
                       delta ( Four,  One') = Six
                       delta ( Five, Zero') = Five
                       delta ( Five,  One') = Five
                       delta (  Six, Zero') = Six
                       delta (  Six,  One') = Five
                       delta (Seven, Zero') = Two
                       delta (Seven,  One') = Two
                       delta              _ = Nine

-- http://i.stack.imgur.com/AD6WJ.png
exactly20s ∷ DFA Fin₄ Binary
exactly20s = DFA { delta = delta
                 , q0    = Fin₄ 0
                 , fs    = singleton (Fin₄ 2)
                 } where delta (Fin₄ 0, Zero') = Fin₄ 1
                         delta (Fin₄ 0,  One') = Fin₄ 0

                         delta (Fin₄ 1, Zero') = Fin₄ 2
                         delta (Fin₄ 1,  One') = Fin₄ 1

                         delta (Fin₄ 2, Zero') = Fin₄ 3
                         delta (Fin₄ 2,  One') = Fin₄ 2

                         delta (Fin₄ 3, Zero') = Fin₄ 3
                         delta (Fin₄ 3,  One') = Fin₄ 3

-- http://i.stack.imgur.com/AD6WJ.png
atleast21s ∷ DFA Fin₃ Binary
atleast21s = DFA { delta = delta
                 , q0    = Fin₃ 0
                 , fs    = singleton (Fin₃ 2)
                 } where delta (Fin₃ 0, Zero') = Fin₃ 0
                         delta (Fin₃ 0,  One') = Fin₃ 1

                         delta (Fin₃ 1, Zero') = Fin₃ 1
                         delta (Fin₃ 1,  One') = Fin₃ 2

                         delta (Fin₃ 2, Zero') = Fin₃ 2
                         delta (Fin₃ 2,  One') = Fin₃ 2

exactly20sANDatleast21s ∷ DFA (Fin₄, Fin₃) Binary
exactly20sANDatleast21s  = exactly20s `DFA.intersection` atleast21s

-- The language ["123456789"]
digitsNFA ∷ NFA.NFA Digits Digits
digitsNFA = NFA.NFA { NFA.delta = delta
                    , NFA.q0 = Zero
                    , NFA.fs = singleton Nine
                    } where delta (Zero,  One)   = singleton One
                            delta (One,   Two)   = singleton Two
                            delta (Two,   Three) = singleton Three
                            delta (Three, Four)  = singleton Four
                            delta (Four,  Five)  = singleton Five
                            delta (Five,  Six)   = singleton Six
                            delta (Six,   Seven) = singleton Seven
                            delta (Seven, Eight) = singleton Eight
                            delta (Eight, Nine)  = singleton Nine
                            delta _              = (∅)

{-
data StackSym = X0 | Y0 deriving (Eq, Ord, Enum, Bounded, Show)

-- The standard PDA example language {L : 0ⁿ1ⁿ for n > 0 }
-- {"01","0011","000111","00001111","0000011111","000000111111","00000001111111","0000000011111111", ...}
example ∷ PDA.PDA Fin₃ (Either () StackSym) Binary
example = PDA.PDA { PDA.delta = delta
                  , PDA.q0    = Fin₃ 0
                  , PDA.z0    = Left ()
                  , PDA.fs    = singleton (Fin₃ 2)
                  } where delta (Fin₃ 0, Just Zero', Left  ()) = singleton (Fin₃ 0, [Right X0, Left  ()])
                          delta (Fin₃ 0, Just Zero', Right X0) = singleton (Fin₃ 0, [Right X0, Right X0])
                          delta (Fin₃ 0, Just  One', Right X0) = singleton (Fin₃ 1, [                  ])
                          delta (Fin₃ 1, Just  One', Right X0) = singleton (Fin₃ 1, [                  ])
                          delta (Fin₃ 1,    Nothing, Left  ()) = singleton (Fin₃ 2, [           Left ()])
                          delta _                              = (∅)

-- https://en.wikipedia.org/wiki/Pushdown_automaton#Example
-- https://en.wikipedia.org/wiki/Pushdown_automaton#/media/File:Pda-example.svg
-- The standard PDA example language {L : 0ⁿ1ⁿ | n ≥ 0 }
-- "", "01","0011","000111","00001111","0000011111","000000111111","00000001111111","0000000011111111", ...
wiki ∷ PDA.PDA Fin₃ Fin₂ Binary
wiki = PDA.PDA { PDA.delta = delta
               , PDA.q0 = Fin₃ 0
               , PDA.z0 = Fin₂ 1
               , PDA.fs = singleton (Fin₃ 2)
               } where delta (Fin₃ 0, Just Zero', Fin₂ 1) = singleton (Fin₃ 0, [Fin₂ 0, Fin₂ 1])
                       delta (Fin₃ 0, Just Zero', Fin₂ 0) = singleton (Fin₃ 0, [Fin₂ 0, Fin₂ 0])
                       delta (Fin₃ 0,    Nothing, Fin₂ 1) = singleton (Fin₃ 1, [        Fin₂ 1])
                       delta (Fin₃ 0,    Nothing, Fin₂ 0) = singleton (Fin₃ 1, [        Fin₂ 0])
                       delta (Fin₃ 1, Just  One', Fin₂ 0) = singleton (Fin₃ 1, [              ])
                       delta (Fin₃ 1,    Nothing, Fin₂ 1) = singleton (Fin₃ 2, [        Fin₂ 1])
                       delta _                            = (∅)

-- wwʳ (or "w then w-reversed"), even length palindromes
-- 62, Page 230, HMU 3rd Edition
wwʳ ∷ PDA.PDA Fin₃ (Either () Bool) Binary
wwʳ = PDA.PDA { PDA.delta = δ
              , PDA.q0    = Fin₃ 0
              , PDA.z0    = Left ()
              , PDA.fs    = singleton (Fin₃ 2)
              } where δ (Fin₃ 0, Just Zero',  Left    ()) = singleton (Fin₃ 0, [Right False, Left     ()])
                      δ (Fin₃ 0, Just Zero', Right False) = singleton (Fin₃ 0, [Right False, Right False])
                      δ (Fin₃ 0, Just Zero', Right  True) = singleton (Fin₃ 0, [Right False, Right  True])
                      δ (Fin₃ 0, Just  One',  Left    ()) = singleton (Fin₃ 0, [Right  True, Left     ()])
                      δ (Fin₃ 0, Just  One', Right False) = singleton (Fin₃ 0, [Right  True, Right False])
                      δ (Fin₃ 0, Just  One', Right  True) = singleton (Fin₃ 0, [Right  True, Right  True])
                      δ (Fin₃ 0,    Nothing,  Left    ()) = singleton (Fin₃ 1, [             Left     ()])
                      δ (Fin₃ 0,    Nothing, Right False) = singleton (Fin₃ 1, [             Right False])
                      δ (Fin₃ 0,    Nothing, Right  True) = singleton (Fin₃ 1, [             Right  True])
                      δ (Fin₃ 1, Just Zero', Right False) = singleton (Fin₃ 1, [                        ])
                      δ (Fin₃ 1, Just  One', Right  True) = singleton (Fin₃ 1, [                        ])
                      δ (Fin₃ 1,    Nothing,  Left    ()) = singleton (Fin₃ 2, [             Left     ()])
                      δ _                                 = (∅) -- otherwise kill the computation

data LP = LParen deriving (Enum, Eq, Ord, Bounded)
instance Show LP where
  show _ = "("
data RP = RParen deriving (Enum, Eq, Ord, Bounded)
instance Show RP where
  show _ = ")"
instance Finite LP
instance Finite RP
-- http://www.eecs.wsu.edu/~ananth/CptS317/Lectures/PDA.pdf
-- Accepts by empty stack, still works accepting by final state, but includes epsilon
-- fmap (>>= (either show show)) (take 10 $ PDA.language balanced)
-- ["","()","(())","()()","((()))","(()())","(())()","()(())","()()()","(((())))"]
balanced ∷ PDA.PDA Bool (Either () LP) (Either LP RP)
balanced = PDA.PDA { PDA.delta = delta
                   , PDA.q0    = False
                   , PDA.z0    = Left ()
                   , PDA.fs    = singleton True
                   } where delta (False, Just (Left  LParen), Left      ()) = singleton (False, [Right LParen, Left      ()])
                           delta (False, Just (Left  LParen), Right LParen) = singleton (False, [Right LParen, Right LParen])
                           delta (False, Just (Right RParen), Right LParen) = singleton (False, [                          ])
                           delta (False,             Nothing, Left      ()) = singleton (True,  [              Left      ()])
                           delta _                                          = (∅)
-}
{-
-- Example from Stanford Automata course, the "Turing Machines" lecture
-- Stanford Automata lecture 4 - 4 - 16, "Turing Machines"
exampleTM ∷ TM.TM Bool Binary Void
exampleTM = TM.TM { TM.delta = delta
                  , TM.q0    = False
                  , TM.fs    = singleton True
                  } where delta (False, Left    Zero') = Just (False, Left Zero', TM.R')
                          delta (False, Left     One') = Just ( True, Left Zero', TM.R')
                          delta (False, Right Nothing) = Just (False, Left  One', TM.L')
                          delta _                      = Nothing  -- Halt

-- HMU pg 329, Figure 8.9
-- { 0ⁿ1ⁿ | n ≥ 1 }
hmu89 ∷ TM.TM Fin₆ Binary StackSym
hmu89 = TM.TM { TM.delta = delta
              , TM.q0    = Fin₆ 0
              , TM.fs    = singleton (Fin₆ 4)
              } where delta (Fin₆ 0, Left      Zero') = Just (Fin₆ 1, Right (Just X0), TM.R')
                      delta (Fin₆ 0, Right (Just Y0)) = Just (Fin₆ 3, Right (Just Y0), TM.R')
                      delta (Fin₆ 1, Left      Zero') = Just (Fin₆ 1, Left      Zero', TM.R')
                      delta (Fin₆ 1, Left       One') = Just (Fin₆ 2, Right (Just Y0), TM.L')
                      delta (Fin₆ 1, Right (Just Y0)) = Just (Fin₆ 1, Right (Just Y0), TM.R')
                      delta (Fin₆ 2, Left      Zero') = Just (Fin₆ 2, Left      Zero', TM.L')
                      delta (Fin₆ 2, Right (Just X0)) = Just (Fin₆ 0, Right (Just X0), TM.R')
                      delta (Fin₆ 2, Right (Just Y0)) = Just (Fin₆ 2, Right (Just Y0), TM.L')
                      delta (Fin₆ 3, Right (Just Y0)) = Just (Fin₆ 3, Right (Just Y0), TM.R')
                      delta (Fin₆ 3, Right   Nothing) = Just (Fin₆ 4, Right   Nothing, TM.R')
                      delta _                         = Nothing


-- TODO accepts by halting, create a new data type without fs?
{-
So the successor’s output on 111101 was 000011 which is the reverse binary representation of 48.
www.cs.columbia.edu/~zeph/3261/L14/TuringMachine.pdf   L14
-}
successor ∷ TM.TM Bool Binary Void
successor = TM.TM { TM.delta = delta
                  , TM.q0    = False
                  , TM.fs    = singleton True
                  } where delta (False, Left    Zero') = Just ( True, Left  One', TM.R')
                          delta (False, Left     One') = Just (False, Left Zero', TM.R')
                          delta (False, Right Nothing) = Just ( True, Left  One', TM.R')
                          delta _                      = Nothing
-}
