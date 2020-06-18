module Impossible where

import           Control.Applicative                  (liftA2)
import           Control.Monad                        (ap)
import           Control.Comonad
import           Data.Bool                            (bool)
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Divisible (conquer)
import           Data.Functor                         ((<&>))
import           Data.Function                        (on)
import           Data.Eq.Unicode                      ((≠))
import           Data.Pointed                         (Pointed, point)
import           Common                               (implies, (‥), DisplayColor, toColor)
import           Finite
import           NatBase  -- import           Numeric.Natural.Unicode        (ℕ)

-- experiments with heavy inspiration from group theory and:
-- http://math.andrej.com/2007/09/28/seemingly-impossible-functional-programs/
-- http://math.andrej.com/2008/11/21/a-haskell-monad-for-infinite-search-in-finite-time/

newtype Search a = Search { find ∷ Predicate a → a }

-- TODO a lot of this can probably be moved to src/Common.hs

