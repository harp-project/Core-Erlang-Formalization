import CoqExtraction
import Prelude
import Control.Monad (when, unless, void)
import Control.Monad.IO.Class
import Control.Monad.State.Class
import Control.Monad.Trans.State (runStateT)

type NodeState m = (MonadState (Node, RRConfig) m, MonadIO m)

exampleForExec :: (Node, RRConfig)
exampleForExec = makeInitialNodeConf ex_Process

evalKSteps :: NodeState m => Integer -> m ()
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
            liftIO $ putStr "PID #" >> print pid >> putStrLn "just make an action:"
            liftIO $ print action
            put (node', conf)
            evalKSteps (k-1)
          _ -> return ()
    _ -> return ()

finishOffIfDead :: NodeState m => m ()
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
              liftIO $ putStr "PID #" >> print pid >> putStrLn "just make an action:"
              liftIO $ print action
              put (node', conf)
              finishOffIfDead
            _ -> return ()))
    _ -> return ()

-- runStateT (evalKSteps 112) exampleForExec