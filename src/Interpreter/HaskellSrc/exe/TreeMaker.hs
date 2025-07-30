module Main where
    
import CoqExtraction
import Prelude

startNode :: Node
startNode = makeInitialNode (RExp (EExp testqsort))

runKTauSteps :: Integer -> PID -> Node -> Node
runKTauSteps n _    node | n <= 0 = node
runKTauSteps n pid  node =
    case interProcessTauStepFunc node pid of
        Just node' -> runKTauStep (n - 1) pid node'
        _ -> node 

advanceAllProcesses :: (Node, [Action]) -> (Node, [Action])

-- main :: IO Integer
-- main = 