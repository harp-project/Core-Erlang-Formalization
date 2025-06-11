import CoqExtraction
import Prelude
import Control.Monad (when, unless, void)
import Control.Monad.IO.Class
import Control.Monad.State.Class
import Control.Monad.Trans.State (runStateT, StateT)

type NodeState = StateT (Node, RRConfig) IO

exampleForExec :: (Node, RRConfig)
exampleForExec = makeInitialNodeConf (RExp (EExp testlife3))

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
            node' `seq` put (node', newConfByAction conf action)
            evalKSteps (k-1)
          _ -> return ()
    _ -> return ()

finishOffIfDead :: NodeState ()
finishOffIfDead = do
  (node, conf) <- get
  let mPid = currPID conf
  case mPid of
    Just pid ->
      when (isDead node pid)
        (if isTotallyDead node pid
        then
          node `seq` void (put (node, delCurrFromConf conf))
        else
          (case nodeSimpleStep node (Left pid) of
            Just (node', action) -> do
              displayAction pid action
              node' `seq` put (node', conf)
              finishOffIfDead
            _ -> return ()))
    _ -> return ()

deliverSignal :: (PID, PID) -> NodeState ()
deliverSignal (src, dst) = do
  (node, conf) <- get
  case nodeSimpleStep node (Right (src, dst)) of
    Just (node', action) -> do
      displayAction dst action
      node' `seq` put (node', conf)
    _ -> return ()

deliverAllSignals :: [(PID, PID)] -> NodeState ()
deliverAllSignals [] = return ()
deliverAllSignals (x : xs) = do
  deliverSignal x
  deliverAllSignals xs

emptyEther :: NodeState ()
emptyEther = do
  (node, conf) <- get
  deliverAllSignals (etherNonEmpty node)

-- runStateT (evalKSteps 112) exampleForExec

evalProgram :: Integer -> Integer -> NodeState ()
evalProgram k n = do
  (node, conf) <- get
  case n of
    10000000 -> return ()
    _ ->
      case currPID conf of
        Just _ -> do
          evalKSteps k
          emptyEther
          (node', conf') <- get
          node' `seq` put (node', nextConf conf')
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
