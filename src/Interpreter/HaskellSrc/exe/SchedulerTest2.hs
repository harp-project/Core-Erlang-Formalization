module SchedulerTest2 where

import CoqExtraction
import Data.List

(!?) :: [a] -> Int -> Maybe a
xs !? n
  | n < 0     = Nothing
  | otherwise = foldr (\x r k -> case k of
                                   0 -> Just x
                                   _ -> r (k-1)) (const Nothing) xs n

class (Show a, Eq a) => Scheduler a where
    isEmpty :: a -> Bool
    addPID :: a -> PID -> a
    removePID :: a -> PID -> a
    changeByAction :: a -> PID -> Bool -> Action -> a
    getOperation :: a -> (a, Maybe (Either PID (PID, PID)))

-- State: original K, currently left from k, list of PIDs, list of Signal src-dst pairs, index
data RoundRobin = RoundRobin Int Int [PID] [(PID, PID)] Int
    deriving (Eq, Show)

rrInit :: Int -> RoundRobin
rrInit k = RoundRobin k k [] [] 0

rrIsEmpty :: RoundRobin -> Bool
rrIsEmpty (RoundRobin _ _ l _ _) = null l

rrAddPID :: RoundRobin -> PID -> RoundRobin
rrAddPID (RoundRobin k i l s ind) pid =
    case find (== pid) l of
        Nothing -> RoundRobin k i (pid : l) s (ind + 1)
        Just _ -> RoundRobin k i l s ind

rrRemovePID :: RoundRobin -> PID -> RoundRobin
rrRemovePID (RoundRobin k i l s ind) pid =
    case find (== pid) l of
        Just _ -> RoundRobin k i (delete pid l) s (ind - 1)
        Nothing -> RoundRobin k i l s ind

rrAddSig :: RoundRobin -> (PID, PID) -> RoundRobin
rrAddSig (RoundRobin k i l s ind) pids =
    RoundRobin k i l (pids : s) ind

rrChangeByAction :: RoundRobin -> PID -> Bool -> Action -> RoundRobin
rrChangeByAction rr _ _ action =
    case action of
        ASpawn pid _ _ _ -> rrAddPID rr pid
        ASend src dst _ -> rrAddSig rr (src, dst)
        _ -> rr

rrGetOperation :: RoundRobin -> (RoundRobin, Maybe (Either PID (PID, PID)))
rrGetOperation (RoundRobin k i l s ind) =
    if (i > 0)
    then case l !? ind of
        Just pid -> (RoundRobin k (i-1) l s ind, Just $ Left $ pid)
        Nothing -> (RoundRobin k i l s ind, Nothing)
    else case s of
        [] ->
            let ind' = (if ind == (Data.List.length l - 1) then 0 else (ind + 1)) in
            case l !? ind' of
                Just pid -> (RoundRobin k (k-1) l s ind', Just $ Left $ pid)
                Nothing -> (RoundRobin k (k-1) l s ind', Nothing)
        [s'] ->
            let ind' = (if ind == (Data.List.length l - 1) then 0 else (ind + 1)) in
            (RoundRobin k k l [] ind', Just $ Right $ s')
        (s' : ss) ->
            (RoundRobin k i l ss ind, Just $ Right $ s')

instance Scheduler RoundRobin where
    isEmpty = rrIsEmpty
    addPID = rrAddPID
    removePID = rrRemovePID
    changeByAction = rrChangeByAction
    getOperation = rrGetOperation




















