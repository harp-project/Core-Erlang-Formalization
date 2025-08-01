module Main where

import CoqExtraction
import Prelude
import Data.Tree
import Data.Hashable
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Control.Monad.Trans.State
import CoqExtraction (interProcessStepFuncFast, interProcessStepFunc)

type ErlNode = Node
type HashSetST = StateT (HS.HashSet Int) IO
type ActionPIDTuple = ((PID, Maybe PID), Action)
type SignalPIDTuple = ((PID, PID), Signal)

data TreeNode = TreeNode {
    getDepthLevel :: Int,
    getParentAction :: Maybe ActionPIDTuple,
    getErlNodeHash :: Int,
    getErlNode :: ErlNode,
    getPossibleNAActions :: HM.HashMap (PID, Maybe PID) Action,
    getPIDsTauIncomplete :: [PID]
}

startErlNode :: ErlNode
startErlNode = makeInitialNode (RExp (EExp testqsort))

hashErlNode :: ErlNode -> Int
hashErlNode = hash . show

startTreeNode :: TreeNode
startTreeNode = TreeNode {
    getDepthLevel = 0,
    getParentAction = Nothing,
    getErlNodeHash = hashErlNode startErlNode,
    getErlNode = startErlNode,
    getPossibleNAActions = HM.empty,
    getPIDsTauIncomplete = []
}

actionToActionTuple :: PID -> Action -> ActionPIDTuple
actionToActionTuple pid a =
    case a of
        AArrive _ dest _        -> ((dest, Nothing), a)
        ASpawn spawned _ _ _    -> ((pid, Just spawned), a)
        _                       -> ((pid, Nothing), a)

etherSignalToActionTuple :: SignalPIDTuple -> ActionPIDTuple
etherSignalToActionTuple ((src, dest), s) =
    let a = AArrive src dest s
    in  ((dest, Nothing), a)

getArrivalActionList :: ErlNode -> [ActionPIDTuple]
getArrivalActionList (eth, _) =
    map etherSignalToActionTuple
        (HM.toList (HM.mapMaybe
            (\x -> if null x
                then Nothing
                else Just (head x)) eth))

runKTauSteps :: Integer -> PID -> ErlNode -> (ErlNode, [ActionPIDTuple])
runKTauSteps n pid node | n <= 0 = (node, [((pid, Nothing), Coq__UU03c4_)])
runKTauSteps n pid node =
    case nodeTauFirstStep node pid of
        Just (node', al) -> if null al
                                then runKTauSteps (n - 1) pid node'
                                else (node', [actionToActionTuple pid (head al)])
        _ -> (node, [])

foldingErlNodeFunc :: (ErlNode, [ActionPIDTuple]) -> PID -> (ErlNode, [ActionPIDTuple])
foldingErlNodeFunc (erlNode, aptList) pid =
    let (erlNode', aptList') = runKTauSteps 1000000 pid erlNode
    in  (erlNode', aptList' ++ aptList)

advanceProcesses :: [PID] -> TreeNode -> (TreeNode, [ActionPIDTuple])
advanceProcesses pidList (TreeNode dl precA _ erlNode actHM) =
    let (erlNode', actList) = foldl foldingErlNodeFunc (erlNode, []) pidList
    in  (TreeNode {
        getDepthLevel = dl,
        getParentAction = precA,
        getErlNodeHash = hashErlNode erlNode',
        getErlNode = erlNode',
        getPossibleNAActions = actHM
    }, actList)
    -- add tau action weed out

executeTreeNodePredAction :: TreeNode -> ([PID], TreeNode)
executeTreeNodePredAction orig@(TreeNode dl precA enh erlNode actHM) =
    case precA of
        Nothing -> (currentProcessList erlNode, orig)
        Just a  -> interProcessStepFunc
        -- finish it

-- pipelineFunc:: (treeNode) -> monad (treeNode, [treeNodes])

-- check the depth lvl
-- prec action
-- make pid list
-- advance pids =
    -- advance erlNode
    -- transform getErlNodeHash, getPossibleNAActions, getPIDsTauIncomplete
    -- (weed out tau step = make new treeNode)
-- check hash
-- compute all actions and [treeNodes]
    -- treeNode = prevTreeNode
    -- (if we take from NAA)



main :: IO ()
main = print "Hello Haskell"