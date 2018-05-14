{-# LANGUAGE TypeApplications, AllowAmbiguousTypes #-}

module Main where

import Algebra (Group (..))
import Data.Fin (Fin, enum)
import Data.Foldable (toList)
import Data.Functor.Const
import Data.List (nub)
import Data.Natural.Class
import Data.Peano (Peano (..))
import Data.Universe.Class
import qualified Numeric.Natural as N
import Text.Printf

import Test.SmallCheck.Series
import Test.Tasty
import Test.Tasty.SmallCheck

import Data.Fin.Permutation

main :: IO ()
main = defaultMain . askOption $ \ (SmallCheckDepth d) -> 
    let go :: ∀ n . Natural n => [TestTree]
        go = tests @n : go @(Succ n)
    in testGroup "" (take (d+1) $ go @Zero)

tests :: ∀ n . Natural n => TestTree
tests =
    localOption (SmallCheckDepth (product [1..n])) $
    testGroup (printf "n = %d" (n :: N.Natural))
    [testGroup "universe"
     [testProperty "size" $ length theUniverse == product [1..n],
      testProperty "uniquity" $ nub theUniverse == theUniverse],
     testProperty "mempty-preserves-apply" $ apply (mempty :: Permutation n) enum == enum,
     testProperty "<>-mempty" $ \ (p :: Permutation n) -> p == p <> mempty && p == mempty <> p,
     testProperty "<>-assoc" $ \ (p :: Permutation n) q r -> p <> (q <> r) == (p <> q) <> r,
     testProperty "<>-preserves-apply" $ \ (p :: Permutation n) q -> (apply p . apply q) enum == apply (p <> q) enum,
     testProperty "inverse" $ \ (p :: Permutation n) -> mempty == p <> invert p,
     testProperty "invert . invert = id" $ \ (p :: Permutation n) -> p == (invert . invert) p,
     testProperty "swap-self-inverse" $ \ m n -> let p = swap m n :: Permutation n in p == invert p]
  where n :: Integral a => a
        n = (fromIntegral . getConst) (reify :: Const Peano n)
        theUniverse = universe @(Permutation n)

instance (Monad m, Natural n) => Serial m (Fin n) where
    series = generate $ \ d -> take (d+1) (toList enum)

instance (Monad m, Natural n) => Serial m (Permutation n) where
    series = generate $ \ d -> take (d+1) universe
