{-# LANGUAGE UnicodeSyntax              #-}
-- {-# LANGUAGE FlexibleInstances          #-}
-- {-# OPTIONS_GHC -Wall #-}

import           DFA
import qualified NFA
import qualified EFA
import qualified GFA
import           Common
import           Finite
import qualified RegExp as RE
import           Examples
import           Data.Set
import           Data.List as List
import           Data.Bool.Unicode
import           Config
import           Data.Functor.Contravariant
import           EasyTest

suite :: Test ()
suite = ok

main ∷ IO ()
main = run suite