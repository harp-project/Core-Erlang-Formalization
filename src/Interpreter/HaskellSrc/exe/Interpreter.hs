module Main where

import CoqExtraction
import ExampleProgs
import Scheduler

import Prelude
import Control.Monad.IO.Class
import Control.Monad.State.Strict

exampleForExec :: (Node, PID)
exampleForExec = makeInitialConfig (RExp (EExp testlife4))

type NodeState s = StateT (Node, s) IO

displayAction :: Scheduler s => PID -> Action -> NodeState s ()
displayAction pid action =
  case action of
    Coq__UU03c4_ -> return ()
    Coq__UU03b5_ -> liftIO $ putStr "(P" >> putStr (show pid) >> putStrLn ") eps"
    ASelf _ -> return ()
    ASend ps pd sig -> do
      liftIO $ putStr "(P" >> putStr (show ps) >> putStr ") ==[ (P" >> putStr (show pd) >> putStr ") ]==>\n\t"
      liftIO $ print sig
    AArrive ps pd sig -> do
      liftIO $ putStr "(P" >> putStr (show pd) >> putStr ") <==[ (P" >> putStr (show ps) >> putStr ") ]==\n\t"
      liftIO $ print sig
    ASpawn p _ _ _ -> do
      liftIO $ putStr "(P" >> putStr (show pid) >> putStr ") --{spawned}--> (P" >> putStr (show p) >> putStrLn ")"

finishOffIfDead :: Scheduler s => PID -> NodeState s ()
finishOffIfDead pid = do
  (node, sched) <- get
  when (isDead node pid)
    (if isTotallyDead node pid
     then void $ put (node, removePID sched pid)
     else case nodeSimpleStep node (Left pid) of
       Just (node', action) -> do
         displayAction pid action
         put (node', changeByAction sched pid True action)
         finishOffIfDead pid
       _ -> liftIO $ putStr "Error: could not kill process P" >> putStr (show pid)
    )

evalProgram :: Scheduler s => NodeState s ()
evalProgram = do
  (node, sched) <- get
  case isEmpty sched of
    True -> return ()
    False -> 
      case getOperation sched of
        (_, Nothing) -> liftIO $ putStr "Error: the scheduler does not produce a step\n" >> putStrLn (show sched)
        (sched', Just (Left pid)) ->
          case nodeSimpleStep node (Left pid) of
            Just (node', action) -> do
              displayAction pid action
              put (node', changeByAction sched' pid False action)
              finishOffIfDead pid
              evalProgram
            _ -> do
              put (node, sched')
              evalProgram
        (sched', Just (Right (src, dst))) ->
          case nodeSimpleStep node (Right (src, dst)) of
            Just (node', action) -> do
              displayAction dst action
              put (node', changeByAction sched' dst False action)
              evalProgram
            _ -> 
              liftIO $ putStr "Error: could not deliver signal between P" 
                >> putStr (show src) >> putStr " and P" >> putStr (show dst) >> putStr "\n"
                >> putStr "(a signal might not have been sent)"

main :: IO ()
main = runStateT evalProgram (fst exampleForExec, RoundRobin 10000 10000 [snd exampleForExec] [] 0) >>= print

-- ghc -O2 -prof -fprof-late -rtsopts Interpreter.hs   <- won't work for now, because of a lack of profiling libraries
-- ghc -O2 -fprof-late -rtsopts
-- ./Interpreter +RTS -p -hc -l   <- won't work for now, because of a lack of profiling libraries
-- ./Interpreter +RTS -l
-- eventlog2html
-- Data.Map.Strict for maps
-- Containers, UnorderedContainers (be strict if possible)
-- Data.ByteString.Char8
