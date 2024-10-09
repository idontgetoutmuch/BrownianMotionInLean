import           Data.Bits
import qualified Data.Map as M
import           Data.Map ( Map )
import           Data.Ratio
import qualified Data.Set as S
import           Data.Set ( Set )
import qualified Data.Vector as V
import           Data.Vector ( Vector )

bigD :: Enum a => Ord a => Fractional a => Int -> Set a
bigD n = S.fromList [ k / 2^n | k <- [0 .. 2^n] ]

natIndToRatInd :: Enum a => Ord a => Fractional a => Int -> Map Int a
natIndToRatInd n = M.fromList [ (k, fromIntegral k / 2^n) | k <- [0 .. 2^n] ]

invert :: Ord v => Map k [v] -> Map v [k]
invert m = M.fromListWith (++) pairs
    where pairs = [(v, [k]) | (k, vs) <- M.toList m, v <- vs]

ratIndToNatInd :: (Ord v, Enum [v], Fractional [v]) => Int -> Map v [Int]
ratIndToNatInd n = invert (natIndToRatInd n)

bigF' :: (Num t1, Ord a, Enum a, Fractional a) =>
         (t1 -> t3 -> a) -> (Int -> t3) -> Int -> a -> a
bigF' bigZ ω n t
  | n == 1 = t * bigZ 1 (ω 1)
  | t `S.member` bigD (n - 1) = 0
  | t `S.member` bigD n = bigZ undefined  (ω n)
  | otherwise = undefined

linearInterpolation :: Fractional a => Ord a => [(Ratio Integer, a)] -> (a -> a)
linearInterpolation xzs = f where
  xs = map fst xzs
  zs = map snd xzs
  f t | t < fromRational (head xs) || t > fromRational (last xs) = error "Cannot interpolate"
      | otherwise = m * zs!!i + (1 - m) * zs!!(i - 1)
          where
            ys = map fromRational xs
            m = (t - ys!!(i - 1)) / (ys!!i - ys!!(i - 1))
            i = binarySearch (V.fromList ys) t

binarySearch :: (Ord a) =>
                Vector a -> a -> Int
binarySearch vec x = loop 0 (V.length vec - 1)
  where
    loop !l !u
      | u <= l    = l
      | otherwise = let e = vec V.! k in if x <= e then loop l k else loop (k+1) u
      where k = l + (u - l) `shiftR` 1
