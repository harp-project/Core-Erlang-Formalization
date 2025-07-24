module Main where

import CoqExtraction
import ExampleProgs
import SchedulerOld
import SchedulerTest2

import Prelude
import Control.Monad.IO.Class
import Control.Monad.State.Strict
--import Control.Monad.Trans.State.Strict (runStateT)

type NodeState = StateT (((Node, RRConfig), PID), [(PID, PID)]) IO

exampleForExec :: (((Node, RRConfig), PID), [(PID, PID)])
exampleForExec = makeInitialNodeConf (RExp (EExp testlife4))

getPidPairFromAction :: Action -> Maybe (PID, PID)
getPidPairFromAction action =
  case action of
    ASend ps pd _ -> Just (ps, pd)
    _ -> Nothing

displayAction :: PID -> Action -> NodeState ()
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

evalKSteps :: Integer -> NodeState ()
evalKSteps 0 = finishOffIfDead
evalKSteps k = do
  (((node, conf), _), msgs) <- get
  -- liftIO $ print node >> putStrLn "" >> putStrLn "" >> putStrLn "" >> putStrLn ""
  let mPid = currPID conf
  case mPid of
    Just pid ->
      if isDead node pid
      then finishOffIfDead
      else
        case nodeSimpleStep node (Left pid) of
          Just (node', action) -> do
            displayAction pid action
            case getPidPairFromAction action of
              Just pp -> do
                put (((node', newConfByAction conf action), 0), pp : msgs)
                evalKSteps (k - 1)
              Nothing -> do
                put (((node', newConfByAction conf action), 0), msgs)
                evalKSteps (k-1)
          _ -> return ()
    _ -> return ()

finishOffIfDead :: NodeState ()
finishOffIfDead = do
  (((node, conf), hipid), msgs) <- get
  let mPid = currPID conf
  case mPid of
    Just pid ->
      when (isDead node pid)
        (if isTotallyDead node pid
        then
          void (put (((node, delCurrFromConf conf), hipid), msgs))
        else
          (case nodeSimpleStep node (Left pid) of
            Just (node', action) -> do
              displayAction pid action
              put (((node', conf), 0), msgs)
              finishOffIfDead
            _ -> return ()))
    _ -> return ()

deliverAllSignals :: NodeState ()
deliverAllSignals = do
  (((node, conf), hipid), msgs) <- get
  case msgs of
    [] -> return ()
    (src, dst) : msrest -> do
      case nodeSimpleStep node (Right (src, dst)) of
        Just (node', action) -> do
          displayAction dst action
          put (((node', conf), 0), msrest)
          deliverAllSignals
        _ -> do
          put (((node, conf), hipid), msrest)
          deliverAllSignals

emptyEther :: NodeState ()
emptyEther = deliverAllSignals

-- runStateT (evalKSteps 112) exampleForExec

evalProgram :: Integer -> NodeState ()
evalProgram k = do
  (((_, conf), _), _) <- get
  case currPID conf of
    Just _ -> do
      evalKSteps k
      emptyEther
      (((node', conf'), hipid'), msgs') <- get
      put (((node', nextConf conf'), hipid'), msgs')
      -- liftIO $ putStrLn "Completed round " >> print (show n) >> print conf'
      evalProgram k
    Nothing -> return ()


--main :: IO ()
--main = runStateT (evalProgram 10000) exampleForExec >>= print

type NodeState' s = StateT (Node, s) IO

displayAction' :: Scheduler s => PID -> Action -> NodeState' s ()
displayAction' pid action =
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

finishOffIfDead' :: Scheduler s => PID -> NodeState' s ()
finishOffIfDead' pid = do
  (node, sched) <- get
  when (isDead node pid)
    (if isTotallyDead node pid
     then void $ put (node, removePID sched pid)
     else case nodeSimpleStep node (Left pid) of
       Just (node', action) -> do
         displayAction' pid action
         put (node', changeByAction sched pid True action)
         finishOffIfDead' pid
       _ -> liftIO $ putStr "Error: could not kill process P" >> putStr (show pid)
    )

evalProgram' :: Scheduler s => NodeState' s ()
evalProgram' = do
  (node, sched) <- get
  case isEmpty sched of
    True -> return ()
    False -> 
      case getOperation sched of
        (_, Nothing) -> liftIO $ putStr "Error: the scheduler does not produce a step\n" >> putStrLn (show sched)
        (sched', Just (Left pid)) ->
          case nodeSimpleStep node (Left pid) of
            Just (node', action) -> do
              displayAction' pid action
              put (node', changeByAction sched' pid False action)
              finishOffIfDead' pid
              evalProgram'
            _ -> do
              put (node, sched')
              evalProgram'
        (sched', Just (Right (src, dst))) ->
          case nodeSimpleStep node (Right (src, dst)) of
            Just (node', action) -> do
              displayAction' dst action
              put (node', changeByAction sched' dst False action)
              evalProgram'
            _ -> 
              liftIO $ putStr "Error: could not deliver signal between P" 
                >> putStr (show src) >> putStr " and P" >> putStr (show dst) >> putStr "\n"
                >> putStr "(a signal might not have been sent)"

main :: IO ()
main = runStateT evalProgram' (fst $ fst $ fst exampleForExec, RoundRobin 10000 10000 [0] [] 0) >>= print

-- ghc -O2 -prof -fprof-late -rtsopts Interpreter.hs   <- won't work for now, because of a lack of profiling libraries
-- ghc -O2 -fprof-late -rtsopts
-- ./Interpreter +RTS -p -hc -l   <- won't work for now, because of a lack of profiling libraries
-- ./Interpreter +RTS -l
-- eventlog2html
-- Data.Map.Strict for maps
-- Containers, UnorderedContainers (be strict if possible)
-- Data.ByteString.Char8
