 {-# LANGUAGE TemplateHaskell #-} 

module QC where

import qualified Prelude
import qualified Data.Bits
import qualified Data.Char
import qualified Data.HashMap.Strict
import qualified Data.Hashable
import qualified Data.HashSet
import Data.List
import GHC.Base
import Control.DeepSeq

import qualified CoqExtractionRaw
import qualified CoqExtractionReplaced

import Test.QuickCheck

constructUnoptimisedGmap :: CoqExtractionRaw.RelDecision a a -> CoqExtractionRaw.Countable a -> [(a,b)] -> CoqExtractionRaw.Gmap a b
constructUnoptimisedGmap eqdec count ((x,y):xs) = CoqExtractionRaw.insert (CoqExtractionRaw.map_insert0 (CoqExtractionRaw.gmap_partial_alter eqdec count)) x y (constructUnoptimisedGmap eqdec count xs)
constructUnoptimisedGmap _ _ _ = CoqExtractionRaw.GEmpty

constructOptimisedGmap :: (Data.Hashable.Hashable a) => [(a,b)] -> CoqExtractionReplaced.Gmap a b
constructOptimisedGmap ((x,y):xs) = Data.HashMap.Strict.insert x y (constructOptimisedGmap xs)
constructOptimisedGmap _ = Data.HashMap.Strict.empty

constructUnoptimisedGset :: CoqExtractionRaw.RelDecision a a -> CoqExtractionRaw.Countable a -> CoqExtractionRaw.Singleton a (CoqExtractionRaw.Gset a) -> [a] -> CoqExtractionRaw.Gset a
constructUnoptimisedGset eqdec count sing (x:xs) = CoqExtractionRaw.union (CoqExtractionRaw.gset_union eqdec count) (constructUnoptimisedGset eqdec count sing xs) (CoqExtractionRaw.singleton sing x) 
constructUnoptimisedGset eqdec count _ _ = CoqExtractionRaw.gset_empty eqdec count

constructOptimisedGset :: (Data.Hashable.Hashable a) => [a] -> CoqExtractionReplaced.Gset a
constructOptimisedGset (x:xs) = Data.HashSet.insert x (constructOptimisedGset xs)
constructOptimisedGset _ = Data.HashSet.empty


mapEquiv :: (Data.Hashable.Hashable a) =>
            CoqExtractionRaw.Countable a ->
            CoqExtractionRaw.RelDecision a a ->
            (b1 -> b2 -> Bool) ->
            CoqExtractionRaw.Gmap a b1 -> CoqExtractionReplaced.Gmap a b2 -> Bool
mapEquiv c1a d1a eqb m1 m2 = all (\(k, v) -> case Data.HashMap.Strict.lookup k m2 of Nothing -> False; Just v2 -> eqb v v2) items1 &&
                         all (\(k, v) -> case CoqExtractionRaw.gmap_lookup d1a c1a k m1 of Nothing -> False; Just v2 -> eqb v2 v) items2
  where
    items1 = CoqExtractionRaw.map_to_list (\_ -> CoqExtractionRaw.gmap_fold d1a c1a) m1
    items2 = Data.HashMap.Strict.toList m2

intMapEquiv = mapEquiv CoqExtractionRaw.nat_countable CoqExtractionRaw.eq_dec1 (==)

listEquiv xs ys = all (\y -> y `elem` xs) ys && all (\x -> x `elem` ys) xs

setEquiv :: (Data.Hashable.Hashable a) =>
            CoqExtractionRaw.Countable a ->
            CoqExtractionRaw.RelDecision a a ->
            CoqExtractionRaw.Gset a -> CoqExtractionReplaced.Gset a -> Bool
setEquiv ac ad xs ys = all (\k -> Data.HashSet.member k ys) items1 &&
                       all (\k -> CoqExtractionRaw.gset_elem_of_dec ad ac k xs) items2
  where
    items1 = CoqExtractionRaw.elements (CoqExtractionRaw.gset_elements ad ac) xs
    items2 = Data.HashSet.toList ys

intSetEquiv= setEquiv CoqExtractionRaw.nat_countable CoqExtractionRaw.eq_dec1
{-
  For maps:
  insert - all tests are based on it - DONE
  lookup DONE
  delete DONE
  domain DONE
  size DONE
  
  For sets:
  insert - all tests are based on it - DONE
  delete - DONE
  member - DONE
  union - DONE
  fresh
-}
--- MAPS ---
prop_lookup_map :: [(NonNegative Prelude.Integer,  NonNegative Prelude.Integer)] -> NonNegative Prelude.Integer -> Bool
prop_lookup_map dn kn = CoqExtractionRaw.lookup (CoqExtractionRaw.gmap_lookup CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable) k umap == Data.HashMap.Strict.lookup k omap
  where
    k = getNonNegative kn
    d = map (\(x, y) -> (getNonNegative x, getNonNegative y)) dn
    umap = constructUnoptimisedGmap CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable d
    omap = constructOptimisedGmap d

prop_delete_map :: [(NonNegative Prelude.Integer,  NonNegative Prelude.Integer)] -> NonNegative Prelude.Integer -> Bool
prop_delete_map dn kn = intMapEquiv
                             (CoqExtractionRaw.delete (CoqExtractionRaw.map_delete (CoqExtractionRaw.gmap_partial_alter CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable)) k umap)
                             (Data.HashMap.Strict.delete k omap)
  where
    k = getNonNegative kn
    d = map (\(x, y) -> (getNonNegative x, getNonNegative y)) dn
    umap = constructUnoptimisedGmap CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable d
    omap = constructOptimisedGmap d

prop_domain_map :: [(NonNegative Prelude.Integer,  NonNegative Prelude.Integer)] -> Bool
prop_domain_map dn = intSetEquiv (CoqExtractionRaw.dom (CoqExtractionRaw.gset_dom CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable) umap)
                           (Data.HashMap.Strict.keysSet omap)
  where
    d = map (\(x, y) -> (getNonNegative x, getNonNegative y)) dn
    umap = constructUnoptimisedGmap CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable d
    omap = constructOptimisedGmap d

prop_size_map :: [(NonNegative Prelude.Integer,  NonNegative Prelude.Integer)] -> Bool
prop_size_map dn = CoqExtractionRaw.map_size (\_ -> CoqExtractionRaw.gmap_fold CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable) umap ==
                                         (Prelude.fromIntegral (Data.HashMap.Strict.size omap))
  where
    d = map (\(x, y) -> (getNonNegative x, getNonNegative y)) dn
    umap = constructUnoptimisedGmap CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable d
    omap = constructOptimisedGmap d


--- SETS ---

prop_delete_set :: [(NonNegative Prelude.Integer)] -> NonNegative Prelude.Integer -> Bool
prop_delete_set dn kn = intSetEquiv
                             (CoqExtractionRaw.difference (CoqExtractionRaw.gset_difference CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable) uset (CoqExtractionRaw.singleton CoqExtractionRaw.singleton_PID k))
                             (Data.HashSet.delete k oset)
  where
    k = getNonNegative kn
    d = map (\x -> getNonNegative x) dn
    uset = constructUnoptimisedGset CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable CoqExtractionRaw.singleton_PID d
    oset = constructOptimisedGset d

prop_member_set :: [(NonNegative Prelude.Integer)] -> NonNegative Prelude.Integer -> Bool
prop_member_set dn kn = CoqExtractionRaw.gset_elem_of_dec CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable k uset == Data.HashSet.member k oset
  where
    k = getNonNegative kn
    d = map (\x -> getNonNegative x) dn
    uset = constructUnoptimisedGset CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable CoqExtractionRaw.singleton_PID d
    oset = constructOptimisedGset d

prop_union_set :: [(NonNegative Prelude.Integer)] -> [(NonNegative Prelude.Integer)] -> Bool
prop_union_set dn1 dn2 = intSetEquiv (CoqExtractionRaw.union (CoqExtractionRaw.gset_union CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable) uset1 uset2)
                                     (Data.HashSet.union oset1 oset2)
  where
    d1 = map (\x -> getNonNegative x) dn1
    d2 = map (\x -> getNonNegative x) dn2
    uset1 = constructUnoptimisedGset CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable CoqExtractionRaw.singleton_PID d1
    uset2 = constructUnoptimisedGset CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable CoqExtractionRaw.singleton_PID d2
    oset1 = constructOptimisedGset d1
    oset2 = constructOptimisedGset d2

prop_fresh :: [(NonNegative Prelude.Integer)] -> Bool
prop_fresh dn = CoqExtractionRaw.fresh (CoqExtractionRaw.set_fresh (CoqExtractionRaw.gset_elements CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable) (CoqExtractionRaw.infinite_fresh CoqExtractionRaw.nat_infinite)) uset ==
                (\pids -> if Data.HashSet.null pids then 0 else (Prelude.maximum (Data.HashSet.toList pids) Prelude.+ 1)) oset
  where
    d = map (\x -> getNonNegative x) dn
    uset = constructUnoptimisedGset CoqExtractionRaw.eq_dec1 CoqExtractionRaw.nat_countable CoqExtractionRaw.singleton_PID d
    oset = constructOptimisedGset d


return []
runTests = $forAllProperties (quickCheckWithResult (Args Nothing 10000 10 100 True 2))





