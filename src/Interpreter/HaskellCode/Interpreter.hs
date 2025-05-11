import CoqExtraction
import Prelude
import Control.Monad.IO.Class
import Control.Monad.State.Class
import Control.Monad.Trans.State (runStateT)

type NodeState m = (MonadState (Node, RRConfig) m, MonadIO m)

exampleForExec :: (Node, RRConfig)
exampleForExec = makeInitialNodeConf ex_Process

evalKSteps :: NodeState m => Integer -> m ()
evalKSteps 0 = return ()
evalKSteps k = do
  (node, conf) <- get
  let pid = Prelude.fst $ nextPIDConf conf
  case nodeSimpleStep node (Left pid) of
    Just (node', action) -> do
      liftIO $ putStr "PID #" >> print pid >> putStrLn "just make an action:"
      liftIO $ print action
      put (node', conf)
      evalKSteps (k-1)
    _ -> return ()

-- runStateT (evalKSteps 112) exampleForExec