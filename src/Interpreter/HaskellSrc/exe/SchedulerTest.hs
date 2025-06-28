import CoqExtraction
import Control.Monad.State
import Data.List

(!?) :: [a] -> Int -> Maybe a
xs !? n
  | n < 0     = Nothing
  | otherwise = foldr (\x r k -> case k of
                                   0 -> Just x
                                   _ -> r (k-1)) (const Nothing) xs n

class Monad a => Scheduler a where
    isEmpty :: a Bool
    addPID :: PID -> a ()
    removePID :: PID -> a ()
    changeByAction :: PID -> Bool -> Action -> a ()
    getOperation :: a (Maybe (Either PID (PID, PID)))

-- State: original K, currently left from k, list of PIDs, list of Signal src-dst pairs, index
type RoundRobin = State (Int, Int, [PID], [(PID, PID)], Int)

rrInit :: Int -> RoundRobin ()
rrInit k = put (k, 0, [], [], 0)

rrIsEmpty :: RoundRobin Bool
rrIsEmpty = get >>= \(_, _, l, _, _) -> return $ null l

rrAddPID :: PID -> RoundRobin ()
rrAddPID pid = do
    (k, i, l, s, ind) <- get
    case find (== pid) l of
        Nothing ->
            put (k, i, (pid : l), s, ind + 1)
        Just _ -> return ()

rrRemovePID :: PID -> RoundRobin ()
rrRemovePID pid = do
    (k, i, l, s, ind) <- get
    case find (== pid) l of
        Just _ ->
            put (k, i, delete pid l, s, ind - 1)
        Nothing -> return ()

rrAddSig :: (PID, PID) -> RoundRobin ()
rrAddSig pids = do
    (k, i, l, s, ind) <- get
    put (k, i, l, (pids : s), ind)

rrChangeByAction :: PID -> Bool -> Action -> RoundRobin ()
rrChangeByAction _ _ action = 
    case action of
    ASpawn pid _ _ _ -> rrAddPID pid
    ASend src dst _ -> rrAddSig (src, dst)
    _ -> return ()

rrGetOperation :: RoundRobin (Maybe (Either PID (PID, PID)))
rrGetOperation = do
    (k, i, l, s, ind) <- get
    if (i > 0)
    then
        case l !? ind of
            Just pid -> do
                put (k, i-1, l, s, ind)
                return $ Just $ Left pid
            Nothing -> return Nothing
    else
        case s of
            [] -> return Nothing
            [s] -> 
                if ind == (Data.List.length l - 1)
                then do
                    put (k, k, l, [], 0)
                    return $ Just $ Right s
                else do
                    put (k, k, l, [], ind + 1)
                    return $ Just $ Right s
            (s : ss) -> do
                put (k, i, l, ss, ind)
                return $ Just $ Right s

instance Scheduler RoundRobin where
    isEmpty = rrIsEmpty
    addPID = rrAddPID
    removePID = rrRemovePID
    changeByAction = rrChangeByAction
    getOperation = rrGetOperation






















