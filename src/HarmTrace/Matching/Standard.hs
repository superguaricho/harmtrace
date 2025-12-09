
module HarmTrace.Matching.Standard (diffChords, diffChordsLen) where

import Data.Algorithm.Diff (Diff, PolyDiff(..), getDiff)



diff :: (Eq a) => [a] -> [a] -> [Diff a]
diff = getDiff

diffLen :: (Eq a) => [a] -> [a] -> Float
diffLen x y = fromIntegral (len (diff x y)) / fromIntegral (length x)

len :: [Diff a] -> Int
len []             = 0
len ((Both _ _):t) = len t
len ((_):t)        = 1 + len t

--------------------------------------------------------------------------------
-- Matching
--------------------------------------------------------------------------------

diffChordsLen :: (Eq a) => [a] -> [a] -> Float
diffChordsLen = diffLen

diffChords :: (Show a, Eq a) => [a] -> [a] -> String
diffChords x y = show (diff x y)
