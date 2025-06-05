module Main where

import CoqExtraction
import Prelude
import Control.Monad.IO.Class
import Control.Monad.State.Strict
import Control.Monad.Trans.State.Strict (runStateT)

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
  (((node, conf), hipid), msgs) <- get
  let mPid = currPID conf
  case mPid of
    Just pid ->
      if isDead node pid
      then finishOffIfDead
      else
        case interProcessStepFuncFast node hipid (Left pid) of
          Just ((node', action), hipid') -> do
            displayAction pid action
            case getPidPairFromAction action of
              Just pp -> do
                put (((node', newConfByAction conf action), hipid'), pp : msgs)
                evalKSteps (k - 1)
              Nothing -> do
                put (((node', newConfByAction conf action), hipid'), msgs)
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
          (case interProcessStepFuncFast node hipid (Left pid) of
            Just ((node', action), hipid') -> do
              displayAction pid action
              put (((node', conf), hipid'), msgs)
              finishOffIfDead
            _ -> return ()))
    _ -> return ()

deliverAllSignals :: NodeState ()
deliverAllSignals = do
  (((node, conf), hipid), msgs) <- get
  case msgs of
    [] -> return ()
    (src, dst) : msrest -> do
      case interProcessStepFuncFast node hipid (Right (src, dst)) of
        Just ((node', action), hipid') -> do
          displayAction dst action
          put (((node', conf), hipid'), msrest)
          deliverAllSignals
        _ -> do
          put (((node, conf), hipid), msrest)
          deliverAllSignals

emptyEther :: NodeState ()
emptyEther = deliverAllSignals

-- runStateT (evalKSteps 112) exampleForExec

evalProgram :: Integer -> Integer -> NodeState ()
evalProgram k n = do
  (((_, conf), _), _) <- get
  case n of
    10000000 -> return ()
    _ ->
      case currPID conf of
        Just _ -> do
          evalKSteps k
          emptyEther
          (((node', conf'), hipid'), msgs') <- get
          put (((node', nextConf conf'), hipid'), msgs')
          -- liftIO $ putStrLn "Completed round " >> print (show n) >> print conf'
          evalProgram k (n + 1)
        Nothing -> return ()


main :: IO ()
main = runStateT (evalProgram 10000 0) exampleForExec >>= print

-- ghc -O2 -prof -fprof-late -rtsopts Interpreter.hs   <- won't work for now, because of a lack of profiling libraries
-- ghc -O2 -fprof-late -rtsopts
-- ./Interpreter +RTS -p -hc -l   <- won't work for now, because of a lack of profiling libraries
-- ./Interpreter +RTS -l
-- eventlog2html
-- Data.Map.Strict for maps
-- Containers, UnorderedContainers (be strict if possible)
-- Data.ByteString.Char8
