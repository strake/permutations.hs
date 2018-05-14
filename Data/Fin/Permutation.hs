{-# LANGUAGE TypeApplications #-}

module Data.Fin.Permutation (Permutation, apply, unapply, swap, orbit, cycles) where

import Prelude (Functor (..), Applicative (..), Eq (..), Show (..), Bool (..), ($), (<$>), otherwise, flip, curry, uncurry)
import Algebra
import Control.Category (Category (..))
import Data.Fin
import Data.Fin.List hiding (swap)
import Data.Foldable (elem, minimum, toList)
import Data.Functor.Compose
import Data.List.NonEmpty (NonEmpty (..))
import Data.Monoid (Endo (..))
import Data.Natural.Class (Natural (..))
import qualified Data.Peano as P
import Data.Universe.Class

data Permutation n where
    PZ :: Permutation P.Zero
    PS :: Fin (P.Succ n) -> Permutation n -> Permutation (P.Succ n)

deriving instance Eq (Permutation n)
deriving instance Show (Permutation n)

instance Natural n => Universe (Permutation n) where
    universe = getCompose $ natural (Compose [PZ]) (Compose $ PS <$> toList enum <*> universe)

instance Natural n => Finite (Permutation n)

apply :: Permutation n -> List n a -> List n a
apply PZ Nil = Nil
apply (PS Zero p) (a:.as) = a:.apply p as
apply (PS (Succ n) p) (a:.as) = uncurry (:.) $ at n (flip (,) a) (apply p as)

unapply :: Permutation n -> List n a -> List n a
unapply PZ Nil = Nil
unapply (PS Zero p) (a:.as) = a:.unapply p as
unapply (PS (Succ n) p) (a:.as) = unapply (PS Zero p) . uncurry (:.) $ at n (flip (,) a) as

instance Natural n => Semigroup (Permutation n) where
    (<>) = unOp₂ $ natural (Op₂ . curry $ \ (PZ, PZ) -> PZ) $ Op₂ . curry $ \ case
        (PS m p, PS Zero q) -> PS m (p <> q)
        (PS m p, PS (Succ n) q) -> let n' = unapply p enum !! n in case m of
            Zero -> PS (Succ n') (p <> q)
            Succ m' | m' == n'  -> PS Zero (p <> q)
                    | otherwise -> PS (Succ n') (swap m' n' <> p <> q)

instance Natural n => Monoid (Permutation n) where
    mempty = natural PZ $ PS Zero mempty

instance Natural n => Group (Permutation n) where
    invert = appEndo . getCompose $ natural (Compose mempty) $ Compose . Endo $ \ case
        PS Zero p -> PS Zero (invert p)
        PS (Succ n) p -> let n' = apply p enum !! n in PS (Succ n') (invert p)

swap :: Natural n => Fin n -> Fin n -> Permutation n
swap = unOp₂ $ natural (Op₂ $ \ case) $ Op₂ . curry $ \ case
    (Zero, Zero) -> mempty
    (Succ m, Succ n) -> PS Zero (swap m n)
    (Zero, Succ n) -> PS (Succ n) mempty
    (Succ m, Zero) -> PS (Succ m) mempty

newtype Op₂ a b n = Op₂ { unOp₂ :: a n -> a n -> b n }

orbit :: Natural n => Permutation n -> Fin n -> NonEmpty (Fin n)
orbit p n = case (!! n) <$> iterate (apply p) enum of
    a:<as -> a:|takeWhile (/= a) as

cycles :: ∀ n . Natural n => Permutation (P.Succ n) -> NonEmpty (NonEmpty (Fin (P.Succ n)))
cycles p = nubOn minimum $ orbit p <$> case enum @(P.Succ n) of n:.ns -> n:|toList ns

infixr 5 :<
data Stream a = a :< Stream a
  deriving (Functor)

iterate :: (a -> a) -> a -> Stream a
iterate f a = a :< (f <$> iterate f a)

takeWhile :: (a -> Bool) -> Stream a -> [a]
takeWhile f (a:<as) | f a = a:takeWhile f as
                    | otherwise = []

nubOn :: Eq b => (a -> b) -> NonEmpty a -> NonEmpty a
nubOn f (a:|as) = a:|go [f a] as
  where go _ [] = []
        go bs (a:as) | b `elem` bs = go bs as
                     | otherwise   = a:go (b:bs) as
          where b = f a
