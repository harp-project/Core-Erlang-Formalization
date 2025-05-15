import CoqExtraction
import Prelude
import Control.Monad (when, unless, void)
import Control.Monad.IO.Class
import Control.Monad.State.Class
import Control.Monad.Trans.State (runStateT, StateT)

type NodeState = StateT (Node, RRConfig) IO

exampleForExec :: (Node, RRConfig)
exampleForExec = makeInitialNodeConf ex_Process

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
  (node, conf) <- get
  let mPid = currPID conf
  case mPid of
    Just pid ->
      if isDead node pid
      then finishOffIfDead
      else
        case nodeSimpleStep node (Left pid) of
          Just (node', action) -> do
            displayAction pid action
            put (node', newConfByAction conf action)
            evalKSteps (k-1)
          _ -> return ()
    _ -> return ()

finishOffIfDead :: NodeState ()
finishOffIfDead =
  do
  (node, conf) <- get
  let mPid = currPID conf
  case mPid of
    Just pid ->
      when (isDead node pid)
        (if isTotallyDead node pid
        then
          void (put (node, delCurrFromConf conf))
        else
          (case nodeSimpleStep node (Left pid) of
            Just (node', action) -> do
              displayAction pid action
              put (node', conf)
              finishOffIfDead
            _ -> return ()))
    _ -> return ()

-- runStateT (evalKSteps 112) exampleForExec