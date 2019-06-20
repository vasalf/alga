{-# LANGUAGE DeriveGeneric #-}

----------------------------------------------------------------------------
-- |
-- Module     : Algebra.Graph.Bipartite.AdjacencyMap
-- Copyright  : (c) Andrey Mokhov 2016-2019
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- __Alga__ is a library for algebraic construction and manipulation of graphs
-- in Haskell. See <https://github.com/snowleopard/alga-paper this paper> for
-- the motivation behind the library, the underlying theory, and
-- implementation details.
--
-- This module defines the 'Bipartite.AdjacencyMap' for bipartite graphs data
-- type and basic associated functions.
----------------------------------------------------------------------------
module Algebra.Graph.Bipartite.AdjacencyMap (
    -- * Data structure
    AdjacencyMap, leftAdjacencyMap, rightAdjacencyMap,

    -- * Basic graph construction primitives
    empty, leftVertex, rightVertex, vertex, edge, overlay, connect, vertices,
    edges, overlays, connects,

    -- * Conversion functions
    toBipartite, fromBipartite, fromGraph,

    -- * Testing bipartiteness
    detectParts,

    -- * Graph properties
    isEmpty, hasEdge, hasLeftVertex, hasRightVertex, hasVertex, leftVertexCount,
    rightVertexCount, vertexCount, edgeCount, leftVertexList, rightVertexList,
    vertexList, edgeList, leftVertexSet, rightVertexSet, vertexSet, edgeSet,

    -- * Miscellaneous
    consistent,
    ) where

import Data.Either (lefts, rights)
import Data.List   (sort)
import Data.Tuple  (swap)
import GHC.Generics

import qualified Algebra.Graph              as G
import qualified Algebra.Graph.AdjacencyMap as AM

import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set

{-| The 'Bipartite.AdjacencyMap' data type represents an __undirected__
bipartite graph by two maps of vertices into their adjacency sets. The two type
parameteters define the types of identifiers of the vertices of each part.

__Note:__ even if the identifiers and their types for two vertices of
different parts are equal, these vertices are considered to be different.
See examples for more details.
-}
data AdjacencyMap a b = BAM {
    -- | The /adjacency map/ of the left part of the graph: each vertex is
    -- associated with a set of its neighbours. Complexity: /O(1)/ time and
    -- memory.
    --
    -- @
    -- leftAdjacencyMap 'empty'                    == Map.'Map.empty'
    -- leftAdjacencyMap ('leftVertex' 1)           == Map.'Map.singleton' 1 Set.'Set.empty'
    -- leftAdjacencyMap ('rightVertex' 1)          == Map.'Map.empty'
    -- leftAdjacencyMap ('edge' 1 2)               == Map.'Map.singleton' 1 (Set.'Set.singleton' 2)
    -- leftAdjacencyMap ('edge' 1 1)               == Map.'Map.singleton' 1 (Set.'Set.singleton' 1)
    -- leftAdjacencyMap ('edges' [(1, 1), (1, 2)]) == Map.'Map.singleton' 1 (Set.'Set.fromAscList' [1, 2])
    -- @
    leftAdjacencyMap :: Map.Map a (Set.Set b),

    -- | The inverse map for 'leftAdjacencyMap'. Complexity: /O(1)/ time and memory.
    --
    -- @
    -- rightAdjacencyMap 'empty'                    == Map.'Map.empty'
    -- rightAdjacencyMap ('leftVertex' 1)           == Map.'Map.empty'
    -- rightAdjacencyMap ('rightVertex' 1)          == Map.'Map.singleton' 2 Set.'Set.empty'
    -- rightAdjacencyMap ('edge' 1 2)               == Map.'Map.singleton' 2 (Set.'Set.singleton' 1)
    -- rightAdjacencyMap ('edge' 1 1)               == Map.'Map.singleton' 1 (Set.'Set.singleton' 1)
    -- rightAdjacencyMap ('edges' [(1, 1), (1, 2)]) == Map.'Map.fromAscList' [(1, Set.'Set.singleton' 1), (2, Set.'Set.singleton' 1)]
    -- @
    rightAdjacencyMap :: Map.Map b (Set.Set a)
} deriving (Eq, Show, Generic)

-- | Check that the internal graph representation is consistent, i.e. that all
-- edges that are present in the 'leftAdjacencyMap' are present in the
-- 'rightAdjacencyMap' map.
--
-- @
-- consistent 'empty'            == True
-- consistent ('vertex' x)       == True
-- consistent ('edge' x y)       == True
-- consistent ('edges' xs)       == True
-- consistent ('fromGraph' g)    == True
-- consistent ('toBipartite' am) == True
-- @
consistent :: (Ord a, Ord b) => AdjacencyMap a b -> Bool
consistent (BAM lr rl) = internalEdgeList lr == sort (map swap $ internalEdgeList rl)

-- The list of edges of a bipartite adjacency map.
--
-- /Note: this function is for internal use only./
internalEdgeList :: Map.Map a (Set.Set b) -> [(a, b)]
internalEdgeList lr = [ (u, v) | (u, vs) <- Map.toAscList lr, v <- Set.toAscList vs ]

-- | Check if a graph contains a given edge.
-- Complexity: /O(log(n))/ time.
--
-- @
-- hasEdge x y 'empty'                                == False
-- hasEdge x y ('edge' x y)                           == True
-- hasEdge 2 3 ('edge' 1 2)                           == False
-- hasEdge x y ('overlay' g ('edge' x y))               == True
-- hasEdge 1 2 ('fromGraph' ('Algebra.Graph.edge' (Left 1) (Left 2))) == False
-- @
hasEdge :: (Ord a, Ord b) => a -> b -> AdjacencyMap a b -> Bool
hasEdge u v (BAM m _) = ((Set.member v) <$> (u `Map.lookup` m)) == Just True

-- | Check if a graph contains a given vertex in the left part.
-- Complexity: /O(log(n))/ time.
--
-- @
-- hasLeftVertex x 'empty'           == False
-- hasLeftVertex x ('leftVertex' x)  == True
-- hasLeftVertex x ('rightVertex' x) == False
-- hasLeftVertex 1 ('leftVertex' 2)  == False
-- @
hasLeftVertex :: Ord a => a -> AdjacencyMap a b -> Bool
hasLeftVertex x (BAM lr _) = x `Map.member` lr

-- | Check if a graph contains a given vertex in the right part.
-- Complexity: /O(log(n))/ time.
--
-- @
-- hasRightVertex x 'empty'           == False
-- hasRightVertex x ('rightVertex' x) == True
-- hasRightVertex x ('leftVertex' x)  == False
-- hasRightVertex 1 ('rightVertex' 2) == False
-- @
hasRightVertex :: Ord b => b -> AdjacencyMap a b -> Bool
hasRightVertex y (BAM _ rl) = y `Map.member` rl

-- | Check if a graph contains a given vertex in the given part.
-- Complexity: /O(log(n))/ time.
--
-- @
-- hasVertex x 'empty'                   == False
-- hasVertex (Right x) ('rightVertex' x) == True
-- hasVertex (Right x) ('leftVertex' x)  == False
-- hasVertex (Left 1) ('leftVertex' 2)   == False
-- hasVertex . Left                    == 'hasLeftVertex'
-- hasVertex . Right                   == 'hasRightVertex'
-- @
hasVertex :: (Ord a, Ord b) => Either a b -> AdjacencyMap a b -> Bool
hasVertex (Left x)  = hasLeftVertex x
hasVertex (Right y) = hasRightVertex y

-- | Check if a graph is empty.
-- Complecity: /O(1)/ time.
--
-- @
-- isEmpty 'empty'                 == True
-- isEmpty ('overlay' 'empty' 'empty') == True
-- isEmpty ('vertex' x)            == False
-- isEmpty                       == (==) 'empty'
-- @
isEmpty :: AdjacencyMap a b -> Bool
isEmpty (BAM lr rl) = Map.null lr && Map.null rl

-- | The number of vertices in the left part in a graph.
-- Complexity: /O(1)/ time.
--
-- @
-- leftVertexCount 'empty'         == 0
-- leftVertexCount 'leftVertex' x  == 1
-- leftVertexCount 'rightVertex' x == 0
-- leftVertexCount . 'edges'       == 'length' . 'Data.List.nub' . 'map' 'fst'
-- @
leftVertexCount :: AdjacencyMap a b -> Int
leftVertexCount = Map.size . leftAdjacencyMap

-- | The number of vertices in the right part in a graph.
-- Complexity: /O(1)/ time.
--
-- @
-- rightVertexCount 'empty'         == 0
-- rightVertexCount 'rightVertex' x == 1
-- rightVertexCount 'leftVertex' x  == 0
-- rightVertexCount . 'edges'       == 'length' . 'Data.List.nub' . 'map' 'snd'
-- @
rightVertexCount :: AdjacencyMap a b -> Int
rightVertexCount = Map.size . rightAdjacencyMap

-- | The number of vertices in a graph.
-- Complexity: /O(1)/ time.
--
-- @
-- vertexCount 'empty'         == 0
-- vertexCount 'leftVertex' x  == 1
-- vertexCount 'rightVertex' x == 1
-- vertexCount g             == 'leftVertexCount' g + 'rightVertexCount' g
-- @
vertexCount :: AdjacencyMap a b -> Int
vertexCount g = leftVertexCount g + rightVertexCount g

-- | The number of edges in a graph.
-- Complexity: /O(n)/ time.
--
-- @
-- edgeCount 'empty'      == 0
-- edgeCount ('vertex' x) == 0
-- edgeCount ('edge' x y) == 1
-- edgeCount . 'edges'    == 'length' . 'Data.List.nub'
-- @
edgeCount :: AdjacencyMap a b -> Int
edgeCount = Map.foldr (+) 0 . fmap Set.size . leftAdjacencyMap

-- Adds all edges needed to make the graph undirected.
-- Complexity: /O(m log n)/.
--
-- /Note: this function is for internal use only./
addReverseEdges :: (Ord a, Ord b) => AM.AdjacencyMap (Either a b) -> AM.AdjacencyMap (Either a b)
addReverseEdges m = AM.overlay m $ AM.edges [ (v, u) | (u, v) <- AM.edgeList m ]

-- | Constructs a bipartite 'AdjacencyMap' from "Algebra.Graph.AdjacencyMap"
-- with given part identifiers, adding all needed edges to make the graph
-- undirected and removing all edges inside one part.
-- Complexity: /O(m log n)/.
--
-- @
-- 'toBipartite ('Algebra.Graph.AdjacencyMap.empty')                                                           == 'empty'
-- 'leftAdjacencyMap' (toBipartite ('Algebra.Graph.AdjacencyMap.edge' (Left 1) (Right 2)))                       == Map.'Map.singleton' 1 (Set.'Set.singleton' 2)
-- toBipartite ('Algebra.Graph.AdjacencyMap.edge' (Left 1) (Left 2))                                           == 'empty'
-- 'rightAdjacencyMap' (toBipartite ('Algebra.Graph.AdjacencyMap.edges' [(Left 1, Right 1), (Left 1, Right 2)])) == Map.'Map.fromAscList' [(1, Set.'Set.singleton' 1), (2, Set.'Set.singleton' 1)]
-- @
toBipartite :: (Ord a, Ord b) => AM.AdjacencyMap (Either a b) -> AdjacencyMap a b
toBipartite m = BAM (Map.fromAscList [ (u, setRights vs) | (Left  u, vs) <- Map.toAscList (AM.adjacencyMap $ addReverseEdges m)])
                         (Map.fromAscList [ (u, setLefts  vs) | (Right u, vs) <- Map.toAscList (AM.adjacencyMap $ addReverseEdges m)])
    where
        setRights = Set.fromAscList . rights . Set.toAscList
        setLefts  = Set.fromAscList . lefts  . Set.toAscList

-- | Constructs an 'Algrebra.Graph.AdjacencyMap' from a bipartite
-- 'AdjacencyMap'.
-- Complexity: /O(m log n)/.
--
-- @
-- fromBipartite 'empty'          == 'Algebra.Graph.AdjacencyMap.empty'
-- fromBipartite ('leftVertex' 1) == 'Algebra.Graph.AdjacencyMap.vertex' (Left 1)
-- fromBipartite ('edge' 1 2)     == 'Algebra.Graph.AdjacencyMap.edges' [(Left 1, Right 2), (Right 2, Left 1)]
-- @
fromBipartite :: (Ord a, Ord b) => AdjacencyMap a b -> AM.AdjacencyMap (Either a b)
fromBipartite (BAM lr rl) = AM.overlays $
       [ AM.edges [ (Left u, Right v) | (u, vs) <- Map.toAscList lr, v <- Set.toAscList vs ]
       , AM.edges [ (Right u, Left v) | (u, vs) <- Map.toAscList rl, v <- Set.toAscList vs ]
       , AM.vertices $ Left  <$> Map.keys lr
       , AM.vertices $ Right <$> Map.keys rl ]

-- | Constructs a bipartite 'AdjacencyMap' from a 'Algebra.Graph.Graph' with
-- given part identifiers, adding all needed edges to make the graph undirected
-- and removing all edges inside one part.
-- Complexity: /O(m log n)/.
--
-- @
-- 'leftAdjacencyMap' (fromGraph ('Algebra.Graph.empty'))                                         == Map.'Map.empty'
-- 'leftAdjacencyMap' (fromGraph ('Algebra.Graph.edge' (Left 1) (Right 2)))                       == Map.'Map.singleton' 1 (Set.'Set.singleton' 2)
-- 'leftAdjacencyMap' (fromGraph ('Algebra.Graph.edge' (Left 1) (Left 2)))                        == Map.'Map.empty'
-- 'rightAdjacencyMap' (fromGraph ('Algebra.Graph.edges' [(Left 1, Right 1), (Left 1, Right 2)])) == Map.'Map.fromAscList' [(1, Set.'Set.singleton' 1), (2, Set.'Set.singleton' 1)]
-- @
fromGraph :: (Ord a, Ord b) => G.Graph (Either a b) -> AdjacencyMap a b
fromGraph = toBipartite . (G.foldg AM.empty AM.vertex AM.overlay AM.connect)

-- | Constructs the /empty graph/.
-- Complexity: /O(1)/ time and memory.
--
-- @
-- 'leftAdjacencyMap' empty  == Map.'Map.empty'
-- 'rightAdjacencyMap' empty == Map.'Map.empty'
-- 'hasVertex' x empty       == False
-- @
empty :: AdjacencyMap a b
empty = BAM Map.empty Map.empty

-- | Constructs the bipartite graph comprising /a single isolated vertex/ in
-- the left part.
-- Complexity: /O(1)/ time and memory.
--
-- @
-- 'leftAdjacencyMap' (leftVertex x)  == Map.'Map.singleton' x Set.'Set.empty'
-- 'rightAdjacencyMap' (leftVertex x) == Map.'Map.empty'
-- 'hasEdge' x y (leftVertex x)       == False
-- 'hasLeftVertex' x (leftVertex x)   == True
-- 'hasRightVertex' x (leftVertex x)  == False
-- @
leftVertex :: a -> AdjacencyMap a b
leftVertex x = BAM (Map.singleton x Set.empty) Map.empty

-- | Constructs the bipartite graph comprising /a single isolated vertex/ in
-- the right part.
-- Complexity: /O(1)/ time and memory.
--
-- @
-- 'leftAdjacencyMap' (rightVertex x)  == Map.'Map.empty'
-- 'rightAdjacencyMap' (rightVertex x) == Map.'Map.singleton' x Set.'Set.empty'
-- 'hasEdge' x y (rightVertex y)       == False
-- 'hasLeftVertex' x (rightVertex x)   == False
-- 'hasRightVertex' x (rightVertex x)  == True
-- @
rightVertex :: b -> AdjacencyMap a b
rightVertex y = BAM Map.empty (Map.singleton y Set.empty)

-- | Constructs the bipartite graph comprising /a single isolated vertex/.
-- Complexity: /O(1)/ time and memory.
--
-- @
-- vertex (Left x)                == 'leftVertex' x
-- vertex (Right x)               == 'rightVertex' x
-- 'hasEdge' x y (vertex (Left x))  == False
-- 'hasEdge' x y (vertex (Right y)) == False
-- @
vertex :: Either a b -> AdjacencyMap a b
vertex (Left x)  = leftVertex x
vertex (Right y) = rightVertex y

-- | Constructs the bipartite graph comprising /a single edge/.
-- Complexity: /O(1)/ time and memory.
--
-- @
-- 'leftAdjacencyMap' (edge x y)  == Map.'Map.singleton' x (Set.'Set.singleton' y)
-- 'rightAdjacencyMap' (edge x y) == Map.'Map.singleton' y (Set.'Set.singleton' x)
-- 'hasEdge' x y (edge x y)       == True
-- 'hasEdge' y x (edge x y)       == (x == y)
-- @
edge :: a -> b -> AdjacencyMap a b
edge x y = BAM (Map.singleton x (Set.singleton y)) (Map.singleton y (Set.singleton x))

-- | /Overlay/ two bipartite graphs. This is a commutative, associative and
-- idempotent operation with the identity 'empty'.
-- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
--
-- @
-- 'isEmpty'     (overlay x y) == 'isEmpty'   x   && 'isEmpty'   y
-- 'hasVertex' z (overlay x y) == 'hasVertex' z x || 'hasVertex' z y
-- 'vertexCount' (overlay x y) >= 'vertexCount' x
-- 'vertexCount' (overlay x y) <= 'vertexCount' x + 'vertexCount' y
-- 'edgeCount'   (overlay x y) >= 'edgeCount' x
-- 'edgeCount'   (overlay x y) <= 'edgeCount' x   + 'edgeCount' y
-- @
overlay :: (Ord a, Ord b) => AdjacencyMap a b -> AdjacencyMap a b -> AdjacencyMap a b
overlay (BAM lr1 rl1) (BAM lr2 rl2) = BAM (Map.unionWith Set.union lr1 lr2) (Map.unionWith Set.union rl1 rl2)

-- | /Connect/ two bipartite graphs, not adding the inappropriate edges. This
-- is an associative operation with the identity 'empty', which distributes
-- over 'overlay' and obeys the decomposition axion.
-- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory. Note that the
-- number of edges in the resulting graph is quadratic with respect to the
-- number of vertices in the arguments: /m = O(m1 + m2 + l1 * r2 + l2 * r1)/.
--
-- @
-- 'isEmpty'     (connect x y) == 'isEmpty'   x   && 'isEmpty'   y
-- 'hasVertex' z (connect x y) == 'hasVertex' z x || 'hasVertex' z y
-- 'vertexCount' (connect x y) >= 'vertexCount' x
-- 'vertexCount' (connect x y) <= 'vertexCount' x + 'vertexCount' y
-- 'edgeCount'   (connect x y) >= 'edgeCount' x
-- 'edgeCount'   (connect x y) >= 'edgeCount' y
-- 'edgeCount'   (connect x y) >= 'leftVertexCount' x * 'rightVertexCount' y
-- 'edgeCount'   (connect x y) <= 'leftVertexCount' x * 'rightVertexCount' y + 'rightVertexCount' x * 'leftVertexCount' y + 'edgeCount' x + 'edgeCount' y
-- @
connect :: (Ord a, Ord b) => AdjacencyMap a b -> AdjacencyMap a b -> AdjacencyMap a b
connect (BAM lr1 rl1) (BAM lr2 rl2) = BAM (Map.unionsWith Set.union [ lr1, lr2,
                                                                      Map.fromSet (const $ Map.keysSet rl2) (Map.keysSet lr1),
                                                                      Map.fromSet (const $ Map.keysSet rl1) (Map.keysSet lr2)]) $
                                           Map.unionsWith Set.union [ rl1, rl2,
                                                                      Map.fromSet (const $ Map.keysSet lr2) (Map.keysSet rl1),
                                                                      Map.fromSet (const $ Map.keysSet lr1) (Map.keysSet rl2)]

-- | Constructs the graph comprising two given lists of isolated vertices for
-- each part.
-- Complexity: /O(L * log(L))/ time and /O(L)/ memory, where /L/ is the total
-- length of two lists.
--
-- @
-- vertices [] []                               == 'empty'
-- vertices [x] []                              == 'leftVertex' x
-- vertices [] [x]                              == 'rightVertex' x
-- 'hasLeftVertex' x . ('flip' ('const' [])) vertices == 'elem' x
-- 'hasRightVertex' x . 'const' [] vertices         == 'elem' x
-- @
vertices :: (Ord a, Ord b) => [a] -> [b] -> AdjacencyMap a b
vertices ls rs = BAM (Map.fromList $ map ((flip (,)) Set.empty) ls) (Map.fromList $ map ((flip (,)) Set.empty) rs)

-- | Constructs the graph from a list of edges.
-- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
--
-- @
-- edges []          == 'empty'
-- edges [(x, y)]    == 'edge' x y
-- 'edgeCount' . edges == 'length' . 'Data.List.nub'
-- @
edges :: (Ord a, Ord b) => [(a, b)] -> AdjacencyMap a b
edges es = BAM (Map.fromListWith Set.union (map (onRight Set.singleton) es)) $
                Map.fromListWith Set.union (map (onRight Set.singleton) (map swap es))
    where
        onRight f (x, y) = (x, f y)

-- | Overlay a given list of graphs.
-- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
--
-- @
-- overlays []        == 'empty'
-- overlays [x]       == x
-- overlays [x,y]     == 'overlay' x y
-- overlays           == 'foldr' 'overlay' 'empty'
-- 'isEmpty' . overlays == 'all' 'isEmpty'
-- @
overlays :: (Ord a, Ord b) => [AdjacencyMap a b] -> AdjacencyMap a b
overlays ams = BAM (Map.unionsWith Set.union (map leftAdjacencyMap ams)) $
                    Map.unionsWith Set.union (map rightAdjacencyMap ams)

-- | Connects a given list of graphs.
-- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
--
-- @
-- connects []        == 'empty'
-- connects [x]       == x
-- connects [x,y]     == connect x y
-- connects           == 'foldr' 'connect' 'empty'
-- 'isEmpty' . connects == 'all' 'isEmpty'
-- @
connects :: (Ord a, Ord b) => [AdjacencyMap a b] -> AdjacencyMap a b
connects = foldr connect empty


-- | The sorted list of vertices of the left part of a given graph.
-- Complexity: /O(l)/ time and memory.
--
-- @
-- leftVertexList 'empty'                == []
-- leftVertexList ('leftVertex' x)       == [x]
-- leftVertexList ('rightVertex' x)      == []
-- leftVertexList . ('flip' 'vertices') [] == 'Data.List.nub' . 'Data.List.sort'
-- @
leftVertexList :: AdjacencyMap a b -> [a]
leftVertexList = Map.keys . leftAdjacencyMap


-- | The sorted list of vertices of the right part of a given graph.
-- Complexity: /O(r)/ time and memory.
--
-- @
-- rightVertexList 'empty'           == []
-- rightVertexList ('leftVertex' x)  == []
-- rightVertexList ('rightVertex' x) == [x]
-- rightVertexList . 'vertices' []   == 'Data.List.nub' . 'Data.List.sort'
-- @
rightVertexList :: AdjacencyMap a b -> [b]
rightVertexList = Map.keys . rightAdjacencyMap


-- | The sorted list of vertices of a given graph.
-- Complexity: /O(n)/ time and memory
--
-- @
-- vertexList 'empty'                             == []
-- vertexList ('vertex' x)                        == [x]
-- vertexList (vertices ('Data.Either.lefts' vs) ('Data.Either.rights' vs)) == 'Data.List.nub' ('Data.List.sort' vs)
-- @
vertexList :: AdjacencyMap a b -> [Either a b]
vertexList g = (map Left $ leftVertexList g) ++ (map Right $ rightVertexList g)


-- | The sorted list of edges of a graph.
-- Complexity: /O(n + m)/ time and /O(m)/ memory.
--
-- @
-- edgeList 'empty'      == []
-- edgeList ('vertex' x) == []
-- edgeList ('edge' x y) == [(x, y)]
-- edgeList . 'edges'    == 'Data.List.nub' . 'Data.List.sort'
-- @
edgeList :: AdjacencyMap a b -> [(a, b)]
edgeList (BAM lr _) = [ (u, v) | (u, vs) <- Map.toAscList lr, v <- Set.toAscList vs ]


-- | The set of vertices of the left part of a given graph.
-- Complexity: /O(l)/ time and memory.
--
-- @
-- leftVertexSet 'empty'                == Set.'Data.Set.empty'
-- leftVertexSet . 'leftVertex'         == Set.'Data.Set.singleton'
-- leftVertexSet . 'rightVertex'        == 'const' Set.'Data.Set.empty'
-- leftVertexSet . ('flip' 'vertices') [] == Set.'Data.Set.fromList'
-- @
leftVertexSet :: AdjacencyMap a b -> Set.Set a
leftVertexSet = Map.keysSet . leftAdjacencyMap


-- | The set of vertices of the right part of a given graph.
-- Complexity: /O(r)/ time and memory.
--
-- @
-- rightVertexSet 'empty'         == Set.'Data.Set.empty'
-- rightVertexSet . 'leftVertex'  == 'const' Set.'Data.Set.empty'
-- rightVertexSet . 'rightVertex' == Set.'Data.Set.singleton'
-- rightVertexSet . 'vertices' [] == Set.'Data.Set.fromList'
-- @
rightVertexSet :: AdjacencyMap a b -> Set.Set b
rightVertexSet = Map.keysSet . rightAdjacencyMap


-- | The set of vertices of a given graph.
-- Complexity: /O(n)/ time and memory.
--
-- @
-- vertexSet 'empty'                             == Set.'Data.Set.empty'
-- vertexSet . 'vertex'                          == Set.'Data.Set.singleton'
-- vertexSet ('vertices' ('Data.Either.lefts' vs) ('Data.Either.rights' vs)) == Set.'Data.Set.fromList' vs
-- @
vertexSet :: (Ord a, Ord b) => AdjacencyMap a b -> Set.Set (Either a b)
vertexSet = Set.fromAscList . vertexList


-- | The set of edges of a given graph.
-- Complexity: /O(n + m)/ time and /O(m)/ memory.
--
-- @
-- edgeSet 'empty'      == Set.'Data.Set.empty'
-- edgeSet ('vertex' x) == Set.'Data.Set.empty'
-- edgeSet ('edge' x y) == Set.'Data.Set.singleton' (x, y)
-- edgeSet . 'edges'    == Set.'Data.Set.fromList'
-- @
edgeSet :: (Ord a, Ord b) => AdjacencyMap a b -> Set.Set (a, b)
edgeSet = Set.fromAscList . edgeList


-- | Test the given adjacency map on bipartiteness. In case of success,
-- return an `AdjacencyMap` with the same set of edges and the vertices marked
-- with the part they belong to.
--
-- /Note/: as `AdjacencyMap` only represents __undirected__ bipartite graphs,
-- all edges in the input graph are assumed to be bidirected and all edges in
-- the output `AdjacencyMap` are bidirected.
--
-- It is advised to use 'leftVertexList' and 'rightVertexList' to obtain the
-- partition of the vertices and 'hasLeftVertex' and 'hasRightVertex' to check
-- whether a vertex belong to a part.
--
-- @
-- detectParts 'Algebra.Graph.AdjacencyMap.empty'                             == Just 'empty'
-- 'Data.Maybe.isJust' (detectParts ('Algebra.Graph.AdjacencyMap.vertex' x))               == True
-- 'Data.Maybe.isJust' (detectParts ('Algebra.Graph.AdjacencyMap.edge' x y))               == True
-- 'Data.Maybe.isJust' (detectParts ('Algebra.Graph.AdjacencyMap.edges' [(1, 2), (1, 3)])) == True
-- 'Data.Maybe.isJust' (detectParts ('Algebra.Graph.AdjacencyMap.clique' k))               == k < 3
-- 'Data.Maybe.isJust' (detectParts ('Algebra.Graph.AdjacencyMap.star' x ys))              == True
-- 'Data.Maybe.isJust' (detectParts ('Algebra.Graph.AdjacencyMap.tree' t))                 == True
-- 'Data.Maybe.isJust' (detectParts ('Algebra.Graph.AdjacencyMap.biclique' xs ys))         == True
-- 'Data.Maybe.isJust' ('fromBipartite' ('toBipartite' am))       == True
-- @
detectParts :: Ord a => AM.AdjacencyMap a -> Maybe (AdjacencyMap a a)
detectParts = undefined
