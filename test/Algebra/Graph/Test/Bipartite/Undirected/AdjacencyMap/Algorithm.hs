{-# LANGUAGE OverloadedLists #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Algebra.Graph.Test.Bipartite.Undirected.AdjacencyMap.Algorithm
-- Copyright  : (c) Andrey Mokhov 2016-2020
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- Testsuite for "Algebra.Graph.Bipartite.Undirected.AdjacencyMap.Algorithm".
-----------------------------------------------------------------------------
module Algebra.Graph.Test.Bipartite.Undirected.AdjacencyMap.Algorithm (
    -- * Testsuite
    testBipartiteUndirectedAdjacencyMapAlgorithm
    ) where

import Algebra.Graph.Bipartite.Undirected.AdjacencyMap
import Algebra.Graph.Bipartite.Undirected.AdjacencyMap.Algorithm
import Algebra.Graph.Test

import Data.Either (isLeft, isRight)
import Data.Either.Extra (fromEither)
import Data.List (nub)

import qualified Algebra.Graph.AdjacencyMap                      as AM
import qualified Algebra.Graph.Bipartite.Undirected.AdjacencyMap as B
import qualified Data.Map.Strict                                 as Map
import qualified Data.Set                                        as Set
import qualified Data.Tuple


type AI   = AM.AdjacencyMap Int
type BAII = AdjacencyMap Int Int
type MII  = Matching Int Int
type MIS  = Matching Int String
type LII  = List Int Int


testBipartiteUndirectedAdjacencyMapAlgorithm :: IO ()
testBipartiteUndirectedAdjacencyMapAlgorithm = do
    putStrLn "\n============ Bipartite.Undirected.AdjacencyMap.detectParts ============"
    test "detectParts empty                                       == Right empty" $
          detectParts (AM.empty :: AI)                            == Right empty
    test "detectParts (vertex x)                                  == Right (leftVertex x)" $ \x ->
          detectParts (AM.vertex x :: AI)                         == Right (leftVertex x)
    test "detectParts (edge x x)                                  == Left [x]" $ \x ->
          detectParts (AM.edge x x :: AI)                         == Left [x]
    test "detectParts (edge 1 2)                                  == Right (edge 1 2)" $
          detectParts (AM.edge 1 2 :: AI)                         == Right (edge 1 2)
    test "detectParts (1 * (2 + 3))                               == Right (edges [(1,2), (1,3)])" $
          detectParts (1 * (2 + 3) :: AI)                         == Right (edges [(1,2), (1,3)])
    test "detectParts (1 * 2 * 3)                                 == Left [1, 2, 3]" $
          detectParts (1 * 2 * 3 :: AI)                           == Left [1, 2, 3]
    test "detectParts ((1 + 3) * (2 + 4) + 6 * 5)                 == Right (swap (1 + 3) * (2 + 4) + swap 5 * 6)" $
          detectParts ((1 + 3) * (2 + 4) + 6 * 5 :: AI)           == Right (swap (1 + 3) * (2 + 4) + swap 5 * 6)
    test "detectParts ((1 * 3 * 4) + 2 * (1 + 2))                 == Left [2]" $
          detectParts ((1 * 3 * 4) + 2 * (1 + 2) :: AI)           == Left [2]
    test "detectParts (clique [1..10])                            == Left [1, 2, 3]" $
          detectParts (AM.clique [1..10] :: AI)                   == Left [1, 2, 3]
    test "detectParts (circuit [1..11])                           == Left [1..11]" $
          detectParts (AM.circuit [1..11] :: AI)                  == Left [1..11]
    test "detectParts (circuit [1..10])                           == Right (circuit [(x, x + 1) | x <- [1,3,5,7,9]])" $
          detectParts (AM.circuit [1..10] :: AI)                  == Right (circuit [(x, x + 1) | x <- [1,3,5,7,9]])
    test "detectParts (biclique [] xs)                            == Right (vertices xs [])" $ \xs ->
          detectParts (AM.biclique [] xs :: AI)                   == Right (vertices xs [])
    test "detectParts (biclique (map Left (x:xs)) (map Right ys)) == Right (biclique (map Left (x:xs)) (map Right ys))" $ \(x :: Int) xs (ys :: [Int]) ->
          detectParts (AM.biclique (map Left (x:xs)) (map Right ys)) == Right (B.biclique (map Left (x:xs)) (map Right ys))
    test "isRight (detectParts (star x ys))                       == notElem x ys" $ \(x :: Int) ys ->
          isRight (detectParts (AM.star x ys))                    == notElem x ys
    test "isRight (detectParts (fromBipartite x))                 == True" $ \(x :: BAII) ->
          isRight (detectParts (fromBipartite x))                 == True

    putStrLn ""
    test "Correctness of detectParts" $ \(input :: AI) ->
        let undirected = AM.symmetricClosure input in
        case detectParts input of
            Left cycle -> mod (length cycle) 2 == 1 && AM.isSubgraphOf (AM.circuit cycle) undirected
            Right bipartite -> AM.gmap fromEither (fromBipartite bipartite) == undirected

    putStrLn "\n============ Bipartite.Undirected.AdjacencyMap.pairOfLeft ============"
    test "pairOfLeft (matching [])                == Map.empty" $
        pairOfLeft (matching [] :: MII)                == Map.empty
    test "pairOfLeft (matching [(3,\"a\"),(1,\"b\")]) == Map.fromList [(3,\"a\"),(1,\"b\")]" $
        pairOfLeft (matching [(3,"a"),(1,"b")] :: MIS) == Map.fromList [(3,"a"),(1,"b")]

    putStrLn "\n============ Bipartite.Undirected.AdjacencyMap.pairOfRight ============"
    test "pairOfRight (matching [])                == Map.empty" $
        pairOfRight (matching [] :: MII)                == Map.empty
    test "pairOfRight (matching [(3,\"a\"),(1,\"b\")]) == Map.fromList [(\"a\",3),(\"b\",1)]" $
        pairOfRight (matching [(3,"a"),(1,"b")] :: MIS) == Map.fromList [("a",3),("b",1)]

    putStrLn "\n============ Bipartite.Undirected.AdjacencyMap.matching ============"
    test "matching [(1,\"a\"),(1,\"b\")]                 == matching [(1,\"b\")]" $
        matching [(1,"a"),(1,"b")]                 == (matching [(1,"b")] :: MIS)
    test "matching [(1,\"a\"),(1,\"b\"),(2,\"b\"),(2,\"a\")] == matching [(2,\"a\")]" $
        matching [(1,"a"),(1,"b"),(2,"b"),(2,"a")] == (matching [(2,"a")] :: MIS)

    putStrLn "\n============ Bipartite.Undirected.AdjacencyMap.swapMatching ============"
    test "swapMatching (matching [])                == matching []" $
        swapMatching (matching [] :: MII)                == matching []
    test "swapMatching (matching [(3,\"a\"),(1,\"b\")]) == matching [(\"a\",3),(\"b\",1)]" $
        swapMatching (matching [(3,"a"),(1,"b")] :: MIS) == matching [("a",3),("b",1)]
    test "swapMatching (matching xs)                == matching (map swap xs)" $ \(xs :: [(Int, Int)]) ->
        swapMatching (matching xs)                       == matching (map Data.Tuple.swap xs)

    putStrLn "\n============ Bipartite.Undirected.AdjacencyMap.matchingSize ============"
    test "matchingSize (matching [])                    == 0" $
        matchingSize (matching [] :: MII)                == 0
    test "matchingSize (matching [(3,\"a\"),(1,\"b\")]) == 2" $
        matchingSize (matching [(3,"a"),(1,"b")] :: MIS) == 2
    test "matchingSize (matching [(1,\"a\"),(1,\"b\")]) == 1" $
        matchingSize (matching [(1,"a"),(1,"b")] :: MIS) == 1
    test "matchingSize (matching xs)                    <= length xs" $ \(xs :: [(Int, Int)]) ->
        matchingSize (matching xs)                       <= length xs
    test "matchingSize x                                == Map.size (pairOfLeft x)" $ \(x :: MII) ->
        matchingSize x                                   == Map.size (pairOfLeft x)

    putStrLn "\n============ Bipartite.Undirected.AdjacencyMap.consistentMatching ============"
    test "consistentMatching (matching xs) == True" $ \(xs :: [(Int,Int)]) ->
        consistentMatching (matching xs)

    putStrLn "\n============ Show (Bipartite.Undirected.AdjacencyMap.Matching) ============"
    test "show (matching [])                == \"matching []\"" $
        Prelude.show (matching [] :: MII)                == "matching []"
    test "show (matching [(3,\"a\"),(1,\"b\")]) == \"matching [(1,\\\"b\\\",(3,\\\"a\\\")]\"" $
        Prelude.show (matching [(3,"a"),(1,"b")] :: MIS) == "matching [(1,\"b\"),(3,\"a\")]"

    putStrLn "\n============ Eq (Bipartite.Undirected.AdjacencyMap.Matching) ============"
    test "(x == y) == ((pairOfLeft x == pairOfLeft y) && (pairOfRight x == pairOfRight y))" $ \(x :: Matching Int Int) (y :: Matching Int Int) ->
        (x == y) == ((pairOfLeft x == pairOfLeft y) && (pairOfRight x == pairOfRight y))

    putStrLn "\n============ Bipartite.Undirected.AdjacencyMap.maxMatching ============"
    test "maxMatching empty                                        == matching []" $
        maxMatching (empty :: BAII)                                      == matching []
    test "maxMatching (vertices xs ys)                             == matching []" $ \(xs :: [Int]) (ys :: [Int]) ->
        maxMatching (vertices xs ys)                                     == matching []
    test "maxMatching (path [1,2,3,4])                             == matching [(1,2),(3,4)]" $
        maxMatching (path ([1,2,3,4] :: LII))                            == matching [(1,2),(3,4)]
    test "matchingSize (maxMatching (circuit [(1,2),(3,4),(5,6)])) == 3" $
        matchingSize (maxMatching (circuit [(1,2),(3,4),(5,6)] :: BAII)) == 3
    test "matchingSize (maxMatching (star x (y:ys)))               == 1" $ \(x :: Int) (y :: Int) (ys :: [Int]) ->
        matchingSize (maxMatching (star x (y:ys)))                       == 1
    test "matchingSize (maxMatching (biclique xs ys))              == min (length (nub xs)) (length (nub ys))" $ \(xs :: [Int]) (ys :: [Int]) ->
        matchingSize (maxMatching (biclique xs ys))                      == min (length (nub xs)) (length (nub ys))
    test "consistentMatching (maxMatching x)                       == True" $ \(x :: BAII) ->
        consistentMatching (maxMatching x)                               == True
    test "Set.fromAscList (Map.toAscList (pairOfLeft (maxMatching x))) `Set.isSubsetOf` edgeSet x == True" $ \(x :: BAII) ->
        Set.fromAscList (Map.toAscList (pairOfLeft (maxMatching x))) `Set.isSubsetOf` edgeSet x == True

    putStrLn "\n============ Bipartite.Undirected.AdjacencyMap.minVertexCover ============"
    test "minVertexCover empty                                  == []" $
        minVertexCover (empty :: BAII)                                == []
    test "minVertexCover (vertices xs ys)                       == []" $ \(xs :: [Int]) (ys :: [Int]) ->
        minVertexCover (vertices xs ys)                               == []
    test "minVertexCover (path [1,2,3])                         == [Right 2]" $
        minVertexCover (path ([1,2,3] :: LII))                        == [Right 2]
    test "minVertexCover (star x (y:(y+1):ys))                  == [Left x]" $ \(x :: Int) (y :: Int) (ys :: [Int]) ->
        minVertexCover (star x (y:(y+1):ys))                          == [Left x]
    test "length (minVertexCover (circuit [(1,2),(3,4),(5,6)])) == 3" $
        length (minVertexCover (circuit [(1,2),(3,4),(5,6)] :: BAII)) == 3
    test "length (minVertexCover (biclique xs ys))              == min (length (nub xs)) (length (nub ys))" $ size10 $ \(xs :: [Int]) (ys :: [Int]) ->
        length (minVertexCover (biclique xs ys))                      == min (length (nub xs)) (length (nub ys))
    test "length (minVertexCover x)                             == matchingSize (maxMatching x)" $ \(x :: BAII) ->
        length (minVertexCover x)                                     == matchingSize (maxMatching x)
    test "isStrictlySorted (minVertexCover x)                   == True" $ \(x :: BAII) ->
        isStrictlySorted (minVertexCover x)
    test "Set.fromAscList (minVertexCover x) `Set.isSubsetOf` vertexSet x == True" $ \(x :: BAII) ->
        Set.fromAscList (minVertexCover x) `Set.isSubsetOf` vertexSet x
    test "isVertexCover (minVertexCover x) x                    == True" $ \(x :: BAII) ->
        isVertexCover (minVertexCover x) x

    putStrLn "\n============ Bipartite.Undirected.AdjacencyMap.maxIndependentSet ============"
    test "maxIndependentSet empty                                  == []" $
        maxIndependentSet (empty :: BAII)                                == []
    test "maxIndependentSet (vertices xs ys)                       == [ Left  x | x <- nub (sort xs) ] ++ [ Right y | y <- nub (sort ys) ]" $ \(xs :: [Int]) (ys :: [Int]) ->
        maxIndependentSet (vertices xs ys)                               == [ Left  x | x <- nub (sort xs) ] ++ [ Right y | y <- nub (sort ys) ]
    test "maxIndependentSet (path [1,2,3])                         == [Left 1,Left 3]" $
        maxIndependentSet (path ([1,2,3] :: LII))                        == [Left 1, Left 3]
    test "maxIndependentSet (star x (y:(y+1):ys))                  == [ Right w | w <- nub (sort (y:(y+1):ys)) ]" $ \(x :: Int) (y :: Int) (ys :: [Int]) ->
        maxIndependentSet (star x (y:(y+1):ys))                          == [ Right w | w <- nub (sort (y:(y+1):ys)) ]
    test "length (maxIndependentSet (circuit [(1,2),(3,4),(5,6)])) == 3" $
        length (maxIndependentSet (circuit [(1,2),(3,4),(5,6)] :: BAII)) == 3
    test "length (maxIndependentSet (biclique xs ys))              == max (length (nub xs)) (length (nub ys))" $ \(xs :: [Int]) (ys :: [Int]) ->
        length (maxIndependentSet (biclique xs ys))                      == max (length (nub xs)) (length (nub ys))
    test "length (maxIndependentSet x)                             == vertexCount x - length (minVertexCover x)" $ \(x :: BAII) ->
        length (maxIndependentSet x)                                     == vertexCount x - length (minVertexCover x)
    test "isStrictlySorted (maxIndependentSet x)                   == True" $ \(x :: BAII) ->
        isStrictlySorted (maxIndependentSet x)
    test "Set.fromAscList (maxIndependentSet x) `Set.isSubsetOf` vertexSet x == True" $ \(x :: BAII) ->
        Set.fromAscList (maxIndependentSet x) `Set.isSubsetOf` vertexSet x
    test "isIndependentSet (maxIndependentSet x) x                 == True" $ \(x :: BAII) ->
        isIndependentSet (maxIndependentSet x) x

    putStrLn "\n============ Bipartite.Undirected.AdjacencyMap.augmentingPath ============"
    test "augmentingPath (matching [])      empty            == Left []" $
        augmentingPath (matching [])      (empty :: BAII)           == Left []
    test "augmentingPath (matching [])      (edge 1 2)       == Right [1,2]" $
        augmentingPath (matching [])      (edge 1 2)                == Right ([1,2] :: LII)
    test "augmentingPath (matching [(1,2)]) (path [1,2,3])   == Left [Right 2]" $
        augmentingPath (matching [(1,2)]) (path ([1,2,3] :: LII))   == Left [Right 2]
    test "augmentingPath (matching [(3,2)]) (path [1,2,3,4]) == Right [1,2,3,4]" $
        augmentingPath (matching [(3,2)]) (path ([1,2,3,4] :: LII)) == Right [1,2,3,4]
    test "isLeft (augmentingPath (maxMatching x) x)          == True" $ \(x :: BAII) ->
        isLeft (augmentingPath (maxMatching x) x)                   == True

isStrictlySorted :: Ord a => [a] -> Bool
isStrictlySorted xs = and $ zipWith (<) xs $ tail xs

isVertexCover :: (Ord a, Ord b) => VertexCover a b -> AdjacencyMap a b -> Bool
isVertexCover xs g = let vc = Set.fromList xs
                      in and $ do (v, u) <- edgeList g
                                  let leftIn  = Left  v `Set.member` vc
                                  let rightIn = Right u `Set.member` vc
                                  return (leftIn || rightIn)

isIndependentSet :: (Ord a, Ord b) => VertexCover a b -> AdjacencyMap a b -> Bool
isIndependentSet xs g = let is = Set.fromList xs
                         in and $ do (v, u) <- edgeList g
                                     let leftIn  = Left  v `Set.member` is
                                     let rightIn = Right u `Set.member` is
                                     return (not (leftIn && rightIn))
