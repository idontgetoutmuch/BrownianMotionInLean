module Brownian where

import           Data.Bits
import           Data.List (unfoldr)
import qualified Data.Map as M
import           Data.Map ( Map )
import           Data.Maybe ( fromJust )
import           Data.Ratio
import qualified Data.Set as S
import           Data.Set ( Set )
import qualified Data.Vector as V
import           Data.Vector ( Vector )


bigD :: Enum a => Ord a => Fractional a => Int -> [a]
bigD n = [ k / 2^n | k <- [0 .. 2^n] ]

natIndToRatInd :: Enum a => Ord a => Fractional a => Int -> Map Int a
natIndToRatInd n = M.fromList [ (k, fromIntegral k / 2^n) | k <- [0 .. 2^n] ]

invert :: Ord v => Map k [v] -> Map v [k]
invert m = M.fromListWith (++) pairs
    where pairs = [(v, [k]) | (k, vs) <- M.toList m, v <- vs]

ratIndToNatInd :: (Ord v, Enum v, Fractional v) => Int -> Map v Int
ratIndToNatInd n = M.map head $ invert (M.map return (natIndToRatInd n))

bigF :: (Ord k, Enum k, Fractional k) =>
        (Int -> t -> k) -> (Int -> t) -> Int -> k -> k
bigF bigZ ω n t
  | n == 0 = t * bigZ 0 (ω 0)
  | t `elem` bigD (n - 1) = 0
  | t `elem` bigD n = s n * bigZ (fromJust $ M.lookup t (ratIndToNatInd n))  (ω n)
  | otherwise = linearInterpolation xys t
      where
        xys = map f (bigD n)
        f d | d `elem` bigD (n - 1) = (d, 0)
            | otherwise             = (d, g d)
        g d = s n * bigZ (fromJust $ M.lookup d (ratIndToNatInd n)) (ω n)
        s n | odd n = recip 2^m
            | otherwise = (recip 2^m) / (last $ mySqrt 2)
          where
            m = (n + 1) `div` 2

mySqrt :: Fractional a => a -> [a]
mySqrt x = unfoldr f (5, x)
  where
    f (0, y) = Nothing
    f (n, y) = Just ((1 / 2) * (y + x / y), (n - 1, (1 / 2) * (y + x / y)))

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

phiInverse :: Double -> Double
phiInverse p =
    if p < 0.5
    then - (rationalApprox $ sqrt (-2 * log p))
    else    rationalApprox $ sqrt (-2 * log (1 - p))
  where
    rationalApprox t = t - num / den
      where
        num = ((0.010328*t + 0.802853)*t + 2.515517)
        den = (((0.001308*t + 0.189269)*t + 1.432788)*t + 1.0)

omegas :: [Double]
omegas = [
  0.437639887, 0.159490213, 0.850264188, 0.293955553, 0.734972546, 0.049096870,
  0.562870972, 0.666760075, 0.256047653, 0.835598406, 0.394648163, 0.991624972,
  0.280294377, 0.720808459, 0.297438190, 0.646008072, 0.636298260, 0.237148565,
  0.288070797, 0.952476848, 0.628257900, 0.318845856, 0.450491344, 0.318241273,
  0.782383124, 0.125192138, 0.334831648, 0.589181548, 0.336003894, 0.570987151,
  0.237508246, 0.150647015, 0.713890495, 0.671867005, 0.084020712, 0.253469971,
  0.265774285, 0.608736769, 0.185620648, 0.927583319, 0.232579881, 0.126427327,
  0.944567202, 0.395007102, 0.662707262, 0.924395813, 0.952670431, 0.006715528,
  0.617714369, 0.269431612, 0.596463384, 0.574498176, 0.280772088, 0.219273222,
  0.003115862, 0.208043369, 0.899984950, 0.802478569, 0.553600569, 0.727199909,
  0.339203733, 0.976450584, 0.896603724, 0.668537614, 0.755125114, 0.650034555,
  0.799166358, 0.715017913, 0.502278788, 0.651452619, 0.749095031, 0.278316605,
  0.644701052, 0.158053017, 0.331026945, 0.698561308, 0.502622389, 0.993999406,
  0.369642583, 0.386373925, 0.140260389, 0.542360593, 0.811527815, 0.319520898,
  0.098348205, 0.347891061, 0.546993859, 0.580981405, 0.697614873, 0.592670241,
  0.415133025, 0.240129063, 0.033776963, 0.985240292, 0.810636813, 0.610633254,
  0.652974149, 0.238983888, 0.207344322, 0.232387795, 0.596875018, 0.625023427,
  0.082313183, 0.298520443, 0.961561512, 0.773936497, 0.205384156, 0.417672050,
  0.524243065, 0.501318275, 0.410149148, 0.669247977, 0.587375080, 0.242536615,
  0.188816136, 0.823220255, 0.502364083, 0.694788706, 0.329996688, 0.725594516,
  0.941219683, 0.866146516, 0.996719332, 0.776777143, 0.036674927, 0.424446622,
  0.318117135, 0.748728539
  ]

test :: Int -> Double -> Double
test n = bigF (const phiInverse) (omegas!!) n

test' :: Int -> [(Double, Double)]
test' n = map (\t ->  (t, test n t)) [0.00, 0.001 .. 1.00]

bmApprox :: Int -> [(Double, Double)]
bmApprox n = foldr (\tzs s -> zip (map fst s) (zipWith (+) (map snd tzs) (map snd s))) (head tzss) (tail tzss)
  where
    tzss :: [[(Double, Double)]]
    tzss = (map test' [0 .. n])

