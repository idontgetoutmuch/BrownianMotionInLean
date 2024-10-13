import Brownian
import Graphics.Rendering.Chart.Easy
import Graphics.Rendering.Chart.Backend.Cairo


main :: IO ()
main = toFile def "example1_big.png" $ do
    layout_title .= "Paths"
    setColors [opaque blue, opaque red, opaque orange, opaque green]
    plot (line "0"  [bmApprox 0])
    plot (line "1"  [bmApprox 1])
    plot (line "2"  [bmApprox 2])
    plot (line "3"  [bmApprox 3])
    plot (line "11"  [bmApprox 11])
    -- plot (line "0"  [test' 0])
    -- plot (line "1"  [test' 1])
    -- plot (line "2"  [test' 2])
    -- plot (line "3"  [test' 3])
    -- plot (line "4"  [test' 4])


