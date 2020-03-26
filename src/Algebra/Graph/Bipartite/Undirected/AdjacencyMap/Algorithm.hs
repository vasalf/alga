----------------------------------------------------------------------------
-- |
-- Module     : Algebra.Graph.Bipartite.Undirected.AdjacencyMap.Algorithm
-- Copyright  : (c) Andrey Mokhov 2016-2020
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- __Alga__ is a library for algebraic construction and manipulation of graphs
-- in Haskell. See <https://github.com/snowleopard/alga-paper this paper> for
-- the motivation behind the library, the underlying theory, and
-- implementation details.
--
-- This module defines the 'AdjacencyMap' data type for undirected bipartite
-- graphs and associated functions. To avoid name clashes with
-- "Algebra.Graph.AdjacencyMap", this module can be imported qualified:
--
-- @
-- import qualified Algebra.Graph.Bipartite.Undirected.AdjacencyMap.Algorithm as BipartiteAlgorithm
-- @
----------------------------------------------------------------------------
module Algebra.Graph.Bipartite.Undirected.AdjacencyMap.Algorithm (
    -- * Testing bipartiteness
    OddCycle, detectParts,

    -- * Maximum matchings
    Matching, pairOfLeft, pairOfRight, matching, swapMatching, matchingSize,
    consistentMatching, VertexCover, IndependentSet, maxMatching,
    minVertexCover, maxIndependentSet, augmentingPath
    ) where

import Algebra.Graph.Bipartite.Undirected.AdjacencyMap

import qualified Algebra.Graph.AdjacencyMap as AM

import Control.Monad.Trans.Maybe
import Control.Monad.State
import Data.Foldable (asum)
import Data.List
import Data.Maybe
import GHC.Generics (Generic)

import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set

data Part = LeftPart | RightPart deriving (Show, Eq)

otherPart :: Part -> Part
otherPart LeftPart  = RightPart
otherPart RightPart = LeftPart

-- | An cycle of odd length. For example, @[1, 2, 3]@ represents the cycle
-- @1 -> 2 -> 3 -> 1@.
type OddCycle a = [a] -- TODO: Make this representation type-safe

-- | Test the bipartiteness of given graph. In case of success, return an
-- 'AdjacencyMap' with the same set of edges and each vertex marked with the
-- part it belongs to. In case of failure, return any cycle of odd length in the
-- graph.
--
-- The returned partition is lexicographically minimal. That is, consider the
-- string of part identifiers for each vertex in ascending order. Then,
-- considering that the identifier of the left part is less then the identifier
-- of the right part, this string is lexicographically minimal of all such
-- strings for all partitions.
--
-- The returned cycle is optimal in the following way: there exists a path that
-- is either empty or ends in a vertex adjacent to the first vertex in the
-- cycle, such that all vertices in @path ++ cycle@ are distinct and
-- @path ++ cycle@ is lexicographically minimal among all such pairs of paths
-- and cycles.
--
-- /Note/: since 'AdjacencyMap' represents __undirected__ bipartite graphs, all
-- edges in the input graph are treated as undirected. See the examples and the
-- correctness property for a clarification.
--
-- It is advised to use 'leftVertexList' and 'rightVertexList' to obtain the
-- partition of the vertices and 'hasLeftVertex' and 'hasRightVertex' to check
-- whether a vertex belongs to a part.
--
-- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
--
-- @
-- detectParts 'Algebra.Graph.AdjacencyMap.empty'                                       == Right 'empty'
-- detectParts ('Algebra.Graph.AdjacencyMap.vertex' x)                                  == Right ('leftVertex' x)
-- detectParts ('Algebra.Graph.AdjacencyMap.edge' x x)                                  == Left [x]
-- detectParts ('Algebra.Graph.AdjacencyMap.edge' 1 2)                                  == Right ('edge' 1 2)
-- detectParts (1 * (2 + 3))                               == Right ('edges' [(1,2), (1,3)])
-- detectParts (1 * 2 * 3)                                 == Left [1, 2, 3]
-- detectParts ((1 + 3) * (2 + 4) + 6 * 5)                 == Right ('swap' (1 + 3) * (2 + 4) + 'swap' 5 * 6)
-- detectParts ((1 * 3 * 4) + 2 * (1 + 2))                 == Left [2]
-- detectParts ('Algebra.Graph.AdjacencyMap.clique' [1..10])                            == Left [1, 2, 3]
-- detectParts ('Algebra.Graph.AdjacencyMap.circuit' [1..10])                           == Right ('circuit' [(x, x + 1) | x <- [1,3,5,7,9]])
-- detectParts ('Algebra.Graph.AdjacencyMap.circuit' [1..11])                           == Left [1..11]
-- detectParts ('Algebra.Graph.AdjacencyMap.biclique' [] xs)                            == Right ('vertices' xs [])
-- detectParts ('Algebra.Graph.AdjacencyMap.biclique' ('map' Left (x:xs)) ('map' Right ys)) == Right ('biclique' ('map' Left (x:xs)) ('map' Right ys))
-- 'isRight' (detectParts ('Algebra.Graph.AdjacencyMap.star' x ys))                       == 'notElem' x ys
-- 'isRight' (detectParts ('fromBipartite' ('toBipartite' x)))   == True
-- @
--
-- The correctness of 'detectParts' can be expressed by the following property:
--
-- @
-- let undirected = 'Algebra.Graph.AdjacencyMap.symmetricClosure' input in
-- case detectParts input of
--     Left cycle -> 'mod' (length cycle) 2 == 1 && 'Algebra.Graph.AdjacencyMap.isSubgraphOf' ('Algebra.Graph.AdjacencyMap.circuit' cycle) undirected
--     Right result -> 'Algebra.Graph.AdjacencyMap.gmap' 'Data.Either.Extra.fromEither' ('fromBipartite' result) == undirected
-- @
detectParts :: Ord a => AM.AdjacencyMap a -> Either (OddCycle a) (AdjacencyMap a a)
detectParts x = case runState (runMaybeT dfs) Map.empty of
    (Nothing, m) -> Right $ toBipartiteWith (toEither m) g
    (Just c,  _) -> Left  $ oddCycle c
  where
    -- g :: AM.AdjacencyMap a
    g = AM.symmetricClosure x

    -- type PartMap a = Map a Part
    -- type PartMonad a = MaybeT (State (PartMap a)) [a]
    -- dfs :: PartMonad a
    dfs = asum [ processVertex v | v <- AM.vertexList g ]

    -- processVertex :: a -> PartMonad a
    processVertex v = do m <- get
                         guard (Map.notMember v m)
                         inVertex LeftPart v

    -- inVertex :: Part -> a -> PartMonad a
    inVertex p v = ((:) v) <$> do
        modify (Map.insert v p)
        let q = otherPart p
        asum [ onEdge q u | u <- Set.toAscList (AM.postSet v g) ]

    {-# INLINE onEdge #-}
    -- onEdge :: Part -> a -> PartMonad a
    onEdge p v = do m <- get
                    case Map.lookup v m of
                        Nothing -> inVertex p v
                        Just q  -> do guard (p /= q)
                                      return [v]

    -- toEither :: PartMap a -> a -> Either a a
    toEither m v = case fromJust (Map.lookup v m) of
                       LeftPart  -> Left  v
                       RightPart -> Right v

    -- oddCycle :: [a] -> [a]
    oddCycle c = init $ dropWhile (/= last c) c

-- | A /matching/ of vertices of two parts.
--
-- The 'Show' instance is defined using the 'matching' function. The edges in
-- the argument are shown in ascending order of left vertices.
--
-- @
-- show ('matching' [])                   == "matching []"
-- show ('matching' [(3, "a"), (1, "b")]) == "matching [(1,\\"b\\"),(3,\\"a\\")]"
-- @
data Matching a b = Matching {
    -- | Map of covered vertices of the left part into their neighbours.
    -- Complexity: /O(1)/.
    --
    -- @
    -- pairOfLeft ('matching' [])                   == Map.'Data.Map.Strict.empty'
    -- pairOfLeft ('matching' [(3, "a"), (1, "b")]) == Map.'Data.Map.Strict.fromList' [(3, "a"), (1, "b")]
    -- @
    pairOfLeft  :: Map.Map a b,

    -- | Map of covered vertices of the right part into their neighbours.
    -- Complexity: /O(1)/.
    --
    -- @
    -- pairOfRight ('matching' [])                  == Map.'Data.Map.Strict.empty'
    -- pairOfRight ('matching' [(3, "a"), (1, "b")] == Map.'Data.Map.Strict.fromList' [("a", 3), ("b", 1)]
    -- @
    pairOfRight :: Map.Map b a
} deriving Generic

instance (Show a, Show b) => Show (Matching a b) where
    showsPrec _ m = showString "matching " . (showList $ Map.toAscList $ pairOfLeft m)

instance (Eq a, Eq b) => Eq (Matching a b) where
    m == n = pairOfLeft m == pairOfLeft n

addEdgeUnsafe :: (Ord a, Ord b) => a -> b -> Matching a b -> Matching a b
addEdgeUnsafe u v (Matching lr rl) = Matching (Map.insert u v lr) (Map.insert v u rl)

addEdge :: (Ord a, Ord b) => a -> b -> Matching a b -> Matching a b
addEdge u v (Matching lr rl) = addEdgeUnsafe u v (Matching lr' rl')
    where
        lr' = case v `Map.lookup` rl of
                   Nothing -> Map.delete u lr
                   Just w  -> Map.delete u (Map.delete w lr)
        rl' = case u `Map.lookup` lr of
                   Nothing -> Map.delete v rl
                   Just w  -> Map.delete v (Map.delete w rl)

-- | Construct a matching from given list of edges.
-- Complexity: /O(L log(L))/, where /L/ is the length of the given list.
--
-- Edges that appear on the list closer to the end of the list overwrite
-- previous edges. That is, if two edges from the list share a vertex, one
-- that appears closer to the beginning is ignored.
--
-- @
-- 'pairOfLeft'  (matching [])                  == Map.'Data.Map.Strict.empty'
-- 'pairOfRight' (matching [])                  == Map.'Data.Map.Strict.empty'
-- 'pairOfLeft'  (matching [(3,"a"),(1,"b")])   == Map.'Data.Map.Strict.fromList' [(3,"a"),(1,"b")]
-- 'pairOfLeft'  (matching [(1,"a"),(1,"b")])   == Map.'Data.Map.Strict.singleton' 1 "b"
-- matching [(1,"a"),(1,"b"),(2,"b"),(2,"a")] == matching [(2,"a")]
-- @
matching :: (Ord a, Ord b) => [(a, b)] -> Matching a b
matching = foldl (flip (uncurry addEdge)) (Matching Map.empty Map.empty)

-- | Swap parts of the vertices in the matching.
-- Complexity: /O(1)/.
--
-- @
-- swapMatching ('matching' [])                == 'matching' []
-- swapMatching ('matching' [(3,"a"),(1,"b")]) == 'matching' [("a",3),("b",1)]
-- swapMatching . 'matching'                   == 'matching' . map 'Data.Tuple.swap'
-- @
swapMatching :: Matching a b -> Matching b a
swapMatching (Matching lr rl) = Matching rl lr

-- | Compute the number of edges in matching.
-- Complexity: /O(1)/.
--
-- @
-- matchingSize ('matching' [])                == 0
-- matchingSize ('matching' [(3,"a"),(1,"b")]) == 2
-- matchingSize ('matching' [(1,"a"),(1,"b")]) == 1
-- matchingSize ('matching' xs)                <= 'length' xs
-- matchingSize                              == Map.'Data.Map.Strict.size' . 'pairOfLeft'
-- @
matchingSize :: Matching a b -> Int
matchingSize = Map.size . pairOfLeft

-- | Check if the internal matching representation of matching is consistent,
-- i.e. that every edge that is present in 'pairOfLeft' is present in
-- 'pairOfRight'.
-- Complexity: /O(S log(S))/, where /S/ is the size of the matching.
--
-- @
-- consistent (matching xs) == True
-- @
consistentMatching :: (Ord a, Ord b) => Matching a b -> Bool
consistentMatching (Matching lr rl) = lrl == sort rll
    where
        lrl = Map.toAscList lr
        rll = [ (v, u) | (u, v) <- Map.toAscList rl ]

-- | A /vertex cover/ in a bipartite graph, represented by list of vertices.
--
-- Vertex cover is such subset of vertices that every edge is incident to some
-- vertex from it.
type VertexCover a b = [Either a b] -- TODO: Maybe set?

-- | An /independent set/ in a bipartite graph, represented by list of vertices.
--
-- A subset of vertices is independent if it contains no pair of adjacent
-- vertices.
type IndependentSet a b = [Either a b] -- TODO: Maybe set?

-- | Find a /maximum mathcing/ in bipartite graph. A matching is maximum if it
-- has maximum possible size.
-- Complexity: /O(m sqrt(n) log(n))/
--
-- @
-- maxMatching 'empty'                                          == 'matching' []
-- maxMatching ('vertices' xs ys)                               == 'matching' []
-- maxMatching ('path' [1,2,3,4])                               == 'matching' [(1,2),(3,4)]
-- 'matchingSize' (maxMatching ('circuit' [(1,2),(3,4),(5,6)])) == 3
-- 'matchingSize' (maxMatching ('star' x (y:ys)))               == 1
-- 'matchingSize' (maxMatching ('biclique' xs ys))              == 'min' ('length' ('nub' xs)) ('length' ('nub' ys))
-- @
maxMatching :: (Ord a, Ord b) => AdjacencyMap a b -> Matching a b
maxMatching = undefined

-- | Find a /vertex cover/ of minimum possible size in bipartite graph.
-- Vertices in the returned list are sorted and unique.
-- Complexity: /O(m sqrt(n) log(n))/
--
-- @
-- minVertexCover 'empty'                     == []
-- minVertexCover ('vertices' xs ys)          == []
-- minVertexCover ('path' [1,2,3])            == [Right 2]
-- minVertexCover ('star' x (y:ys))           == [Left x]
-- 'length' (minVertexCover ('biclique' xs ys)) == 'min' ('length' ('nub' xs)) ('length' ('nub' ys))
-- 'length' . minVertexCover                  == 'matchingSize' . 'maxMatching'
-- @
minVertexCover :: (Ord a, Ord b) => AdjacencyMap a b -> VertexCover a b
minVertexCover = undefined

-- | Find an /independent set/ of maximum possible size in bipartite graph.
-- Vertices in the returned list are sorted and unique.
-- Complexity: /O(m sqrt(n) log(n))/
--
-- @
-- maxIndependentSet 'empty'                     == []
-- maxIndependentSet ('vertices' xs ys)          == [ Left  x | x <- 'Data.List.nub' ('Data.List.sort' xs) ]
--                                             ++ [ Right y | y <- 'Data.List.nub' ('Data.List.sort' ys) ]
-- maxIndependentSet ('path' [1,2,3])            == [Left 1,Left 3]
-- maxIndependentSet ('star' x (y:z:ys))         == [ Right w | w <- y:z:ys ]
-- 'length' (maxIndependentSet ('biclique' xs ys)) == 'max' ('length' ('nub' xs)) ('length' ('nub' ys))
-- 'length' (maxIndependentSet x)                == vertexCount x - length (minVertexCover x)
-- @
maxIndependentSet :: (Ord a, Ord b) => AdjacencyMap a b -> IndependentSet a b
maxIndependentSet = undefined

-- | Given a matching in a graph, find either a /vertex cover/ of the same size
-- or an /augmeting path/ with respect to the given matching.
-- Complexity: /O((m + n) log(n))/
--
-- A path is /alternating/ with respect to a matching if its edges from the
-- matching are alternating with edges not from the matching. An alternating
-- path is augmenting if it starts and ends in vertices that are uncovered by
-- the matching.
--
-- @
-- augmentingPath ('matching' [])      'empty'            == Left []
-- augmentingPath ('matching' [])      ('edge' 1 2)       == Right [1,2]
-- augmentingPath ('matching' [(1,2)]) ('path' [1,2,3])   == Left [Right 2]
-- augmentingPath ('matching' [(3,2)]) ('path' [1,2,3,4]) == Right [1,2,3,4]
-- isLeft (augmentingPath ('maxMatching' x) x)          == True
-- @
augmentingPath :: forall a b. (Ord a, Ord b) =>
                  Matching a b -> AdjacencyMap a b -> Either (VertexCover a b) (List a b)
augmentingPath = undefined
