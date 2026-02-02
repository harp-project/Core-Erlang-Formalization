module Scheduler where

import CoqExtraction
import Data.List

(!?) :: [a] -> Int -> Maybe a
xs !? n
  | n < 0     = Nothing
  | otherwise = foldr (\x r k -> case k of
                                   0 -> Just x
                                   _ -> r (k-1)) (const Nothing) xs n

-- isEmpty		: True if there are no processes to be scheduled, false otherwise
-- addPID		: Add a PID of a process to the schedule (not used directly in the interpreter)
-- removePID		: Remove a PID of a process from the schedule (used when processes terminate completely)
-- changeByAction	: Gets the PID of the process, a boolean whether the process is dead or not 
--			  (True if dead, False if alive), and the action that was performed on it.
--			  The PID is given, because tau and epsilon steps do not contain it. The internal
--			  changes to the schedule should be decided by the developer.
-- getOperation		: Gives back a new scheduler, along with a potential operation to be taken.
--			  If no steps can be taken (e.g. the scheduler is empty), Nothing should be given.
--			  Otherwise, a single PID can be given to perform a non-arrival action to the process
--			  assigned to it, or a pair of PIDs to make a signal arrive from a source to a destination.
--			  Note that signals in the Ether should be accounted for by the developer.
--			  With changeByAction, an ASend action means that a signal was sent to the Ether, but it
--			  has not arrived yet.
class (Show a, Eq a) => Scheduler a where
    isEmpty :: a -> Bool
    addPID :: a -> PID -> a
    removePID :: a -> PID -> a
    changeByAction :: a -> PID -> Bool -> Action -> a
    getOperation :: a -> (a, Maybe (Either PID (PID, PID)))

-- This is a variation of round-robin scheduling. Note that it differs from the classic
-- implementation in that new processes get inserted to a fixed point of the cycle.
-- The scheduler takes K non-arrival steps on a single process, then delivers all
-- signals in the Ether, and then moves on to the next process. If an ASpawn action
-- was taken, the new process' PID gets put into the cycle. If an ASend action was taken,
-- the (src, dst) pair is remembered.

-- The first Int is the original K, the secong Int is the amount of steps left from K,
-- [PID] is the list of PIDs to be scheduled, [(PID, PID)] is the source-destination
-- pair list of signals floating in the Ether, and the last Int is a pointer to the
-- list of PIDs in the scheduler.
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
        Just _ -> 
            -- When removing a PID, the pointer needs to be modified. In case the
            -- pointer points to a positive index, 1 is subtracted. If it points
            -- to the 0th index, the last position needs to be given, which is
            -- length l - 2. (The original last index was length l - 1, but the
            -- list will contain 1 fewer element)
            let ind' = (if (ind > 0) then (ind - 1) else (length l - 2)) in
                RoundRobin k i (delete pid l) s ind'
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

