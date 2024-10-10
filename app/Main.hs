import Brownian
import Graphics.Rendering.Chart.Easy
import Graphics.Rendering.Chart.Backend.Cairo


test' :: Int -> [(Double, Double)]
test' n = map (\t ->  (t, test n t)) [0.00, 0.01 .. 1.00]

main :: IO ()
main = toFile def "example1_big.png" $ do
    layout_title .= "Paths"
    setColors [opaque blue, opaque red]
    plot (line "0"  [test' 0])
    plot (points "1" (test' 1))
    plot (points "2" (test' 2))
