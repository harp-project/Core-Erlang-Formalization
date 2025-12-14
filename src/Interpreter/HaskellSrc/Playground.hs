module Playground where

import Data.Tree
import qualified Data.HashSet as HS
import Control.Monad.Trans.State

type HashSetState = StateT (Set ) IO