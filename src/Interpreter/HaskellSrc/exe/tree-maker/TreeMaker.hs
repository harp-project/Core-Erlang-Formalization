
module Main where

import RocqExtraction
    ( PID,
      Redex(RExp),
      Exp(EExp),
      Signal,
      Action(..),
      Node,
      makeInitialConfig,
      nodeTauFirstStep,
      interProcessStepFunc )
import ExampleProgs ( testpmap )
import qualified Data.Tree as DT
import Data.Hashable ( Hashable(hash) )
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Control.Monad.Trans.State ( get, modify, StateT, runStateT )
import Data.Maybe (catMaybes, isNothing, fromJust)
import Control.Monad.IO.Class (liftIO)
import Data.List (intercalate)

type ErlNode = Node
type HashSetST = StateT (HS.HashSet Int) IO
type ActionPIDTuple = ((PID, Maybe PID), Action)
type SignalPIDTuple = ((PID, PID), Signal)

data TreeNode = TreeNode {
    getDepthLevel :: Int,
    getParentAction :: Maybe ActionPIDTuple,
    getErlNodeHash :: Int,
    getErlNode :: ErlNode,
    getPossibleNAActions :: HS.HashSet ActionPIDTuple,
    getPIDsTauIncomplete :: [PID]
}

-- configurable
tauStepsLimit :: Integer
tauStepsLimit = 100000000000

-- configurable
maxDepth :: Int
maxDepth = 300

-- configurable (replace testpmap w/ smth from ExampleProgs.hs)
startErlNode :: (ErlNode, PID)
startErlNode = makeInitialConfig (RExp (EExp testpmap))

hashErlNode :: ErlNode -> Int
hashErlNode = hash

startTreeNode :: TreeNode
startTreeNode = TreeNode {
    getDepthLevel = 0,
    getParentAction = Nothing,
    getErlNodeHash = hashErlNode (fst startErlNode),
    getErlNode = fst startErlNode,
    getPossibleNAActions = HS.empty,
    getPIDsTauIncomplete = [snd startErlNode]
}

-- convert an Action and the target pid into the canonical ActionPIDTuple
actionToActionTuple :: PID -> Action -> ActionPIDTuple
actionToActionTuple pid a =
    case a of
        AArrive _ dest _        -> ((dest, Nothing), a)
        ASpawn spawned _ _ _    -> ((pid, Just spawned), a)
        _                       -> ((pid, Nothing), a)

-- convert an ether signal to an AArrive tuple
etherSignalToActionTuple :: SignalPIDTuple -> ActionPIDTuple
etherSignalToActionTuple ((src, dest), s) =
    let a = AArrive src dest s
    in  ((dest, Nothing), a)

-- from Ether, take first signal of each key (if any) and form arrival
-- ActionPIDTuples (possible arrival actions).
getArrivalActionList :: Node -> [ActionPIDTuple]
getArrivalActionList (eth, _) =
    map etherSignalToActionTuple
        (HM.toList (HM.mapMaybe
            (\x -> if null x then Nothing else Just (head x)) eth))

-- I forgot that self steps should be compressed, too: try a tau step,
-- if it produces an ASelf action, attempt to apply that ASelf via
-- interProcessStepFunc, then try tau again.
nodeTauOrSelfFirstStep :: Node -> PID -> Maybe (Node, [Action])
nodeTauOrSelfFirstStep node pid =
    case nodeTauFirstStep node pid of
        Just (node', (ASelf selfID) : _) ->
            case interProcessStepFunc node' (ASelf selfID) pid of
                Just node'' -> nodeTauFirstStep node'' pid
                _           -> Nothing
        val -> val

-- run up to k tau/self steps for a PID. Return:
--   (resultingNode, listOfNewActionTuplesProduced, listOfPIDsThatHitLimit)
runKTauSteps :: Integer -> PID -> ErlNode -> (ErlNode, [ActionPIDTuple], [PID])
runKTauSteps n pid node | n <= 0 = (node, [], [pid])
runKTauSteps n pid node =
    case nodeTauOrSelfFirstStep node pid of
        Just (node'@(_, processPool), al) ->
            if null al
                -- Better to alter the Rocq definition of nodeTauFirstStep
                -- since the lookup is already performed there once
                -- maybe can just return a flag indicating if the process is dead
                then case HM.lookup pid processPool of
                    Just (Left _)   -> runKTauSteps (n - 1) pid node'
                    _               -> (node', [], [])
                else (node', [actionToActionTuple pid (head al)], [])
        _ -> (node, [], [])

-- fold function to advance PIDs
foldingErlNodeFunc :: (ErlNode, [ActionPIDTuple], [PID]) -> PID -> (ErlNode, [ActionPIDTuple], [PID])
foldingErlNodeFunc (erlNode, aptList, incTauPIDl) pid =
    let (erlNode', aptList', incTauPIDl') = runKTauSteps tauStepsLimit pid erlNode
    in  (erlNode', aptList' ++ aptList, incTauPIDl' ++ incTauPIDl)

-- advance a list of PIDs on a TreeNode
advanceProcesses :: [PID] -> TreeNode -> (TreeNode, [ActionPIDTuple])
advanceProcesses pidList (TreeNode dl precA _ erlNode actHS _) =
    let (erlNode', actList, incTauList') = foldl foldingErlNodeFunc (erlNode, [], []) pidList
    in  (TreeNode {
        getDepthLevel = dl,
        getParentAction = precA,
        getErlNodeHash = hashErlNode erlNode',
        getErlNode = erlNode',
        getPossibleNAActions = actHS,
        getPIDsTauIncomplete = incTauList'
    }, actList)

-- Unfolding func for treeBuild
generateChildren :: TreeNode -> HashSetST (TreeNode, [TreeNode])
generateChildren parent@(TreeNode dl _ _ erlNode possibleNAActions pidsTauInc) = do
    _ <- liftIO $ putStrLn (renderNode True parent)
    if dl >= maxDepth
      then return (parent, [])
      else do
        let arrivalList = getArrivalActionList erlNode
        let naaList = HS.toList possibleNAActions
        let aaList = arrivalList
        let candidates
                | null naaList && null aaList && not (null pidsTauInc) = [Nothing]
                | otherwise = map Just (naaList ++ aaList)
        childNodes <- concat <$> mapM (makeChild parent) candidates
        return (parent, childNodes)

makeChild :: TreeNode -> Maybe ActionPIDTuple -> HashSetST [TreeNode]
makeChild parent@(TreeNode dl _ _ erlNode possibleNAActions pidsTauInc) mParentAction =
  do
    let childInit = parent {
        getDepthLevel = dl + 1,
        getParentAction = mParentAction
    }
    erlNodeAfterParentAction <- case mParentAction of
        Nothing -> return erlNode
        Just ((pid, _), action) ->
            case interProcessStepFunc erlNode action pid of
                Just node' -> return node'
                Nothing -> return erlNode
    let pidsFromParent = case mParentAction of
            Nothing -> []
            Just ((pid, mPid), _) -> pid : catMaybes [mPid]
    let pidListToAdvance = HS.toList (HS.fromList (pidsFromParent ++ pidsTauInc))
    let correctedPNAAs = if isNothing mParentAction
                                then possibleNAActions
                                else HS.delete (fromJust mParentAction) possibleNAActions
    let child' = childInit {
        getErlNode = erlNodeAfterParentAction,
        getPossibleNAActions = correctedPNAAs
    }

    let (advancedChild, producedApt) = advanceProcesses pidListToAdvance child'
    let newPossibleNAActions = HS.union (getPossibleNAActions advancedChild) (HS.fromList producedApt)

    let finalizedChild = advancedChild {
        getPossibleNAActions = newPossibleNAActions
    }

    seen <- get
    let h = getErlNodeHash finalizedChild
    if HS.member h seen
      then do
        -- set an "empty" config for ErlNode since we want to cut off the branch
        -- but candidates can be fetched from ether if it's not empty
        _ <- liftIO $ putStrLn $ show h ++ " seen!"
        return [finalizedChild {
            getErlNode = (HM.empty, HM.empty),
            getPossibleNAActions = HS.empty,
            getPIDsTauIncomplete = []
        }]
      else do
        modify (HS.insert h)
        return [finalizedChild]

-- Build the tree starting from startTreeNode
buildTree :: HashSetST (DT.Tree TreeNode)
buildTree = do
    modify (HS.insert $ getErlNodeHash startTreeNode)
    DT.unfoldTreeM generateChildren startTreeNode

renderAction :: Action -> String
renderAction (AArrive _ dest _) = "Arrive to " ++ show dest
renderAction (ASpawn child _ _ _) = show child ++ " spawned"
renderAction (ASend src _ _) = "Send from " ++ show src
renderAction (ASelf pid) = "Self in " ++ show pid
renderAction Coq__UU03b5_ = "Epsilon"
renderAction Coq__UU03c4_ = "Tau"

renderActionPIDTuple :: ActionPIDTuple -> String
renderActionPIDTuple ((pid, mSpawn), action) =
    "(target=" ++ show pid ++ ", spawn=" ++ show mSpawn ++ ", act=" ++ renderAction action ++ ")"

renderParentAction :: String -> TreeNode -> String
renderParentAction def node = maybe def renderActionPIDTuple (getParentAction node)

renderNode :: Bool -> TreeNode -> String
renderNode hideErlNode node =
    let parentActStr = renderParentAction "Nothing" node
        possibleNAStr = show $ map renderActionPIDTuple (HS.toList (getPossibleNAActions node)
                                                        ++ getArrivalActionList (getErlNode node))
        tauIncompStr = show $ getPIDsTauIncomplete node
        erlNodeStr = if hideErlNode then "<hidden>" else show $ getErlNode node
    in " parentAct=" ++ parentActStr
        ++ " hash=" ++ show (getErlNodeHash node)
        ++ " possibleActions=" ++ possibleNAStr
        ++ " PIDsTauIncomplete=" ++ tauIncompStr
        ++ " erlNode=" ++ erlNodeStr

-- Print the whole Tree with indentation
renderTree :: Bool -> DT.Tree TreeNode -> String
renderTree hideErlNode = renderTreeLevel 0
    where
        renderTreeLevel indent (DT.Node nd children) =
            replicate (indent * 2) ' ' ++ renderNode hideErlNode nd ++ "\n"
            ++ concatMap (renderTreeLevel (indent + 1)) children

renderJsonNodeArray :: HS.HashSet Int -> String
renderJsonNodeArray hs =
    "\"nodes\":[" ++
    intercalate ","
        (map
            (\x -> "{\"data\":{\"id\":\"" ++ show x
                    ++ "\",\"label\":\"" ++ show x ++ "\"}}")
            (HS.toList hs))
    ++ "]"

renderJsonEdgeArray :: DT.Tree TreeNode -> String
renderJsonEdgeArray tree = "\"edges\":[" ++ renderTreeEdges tree ++ "]"
    where
        renderTreeEdges (DT.Node node children) =
            let source = show $ getErlNodeHash node in
                intercalate "," $ filter (not . null)
                    (map (\(DT.Node childNode _) ->
                        let target = show $ getErlNodeHash childNode
                            label =  renderParentAction "*" childNode
                            edgeId = source ++ show (getErlNodeHash childNode)
                        in
                            "{\"data\":{\"id\":\"" ++ edgeId ++
                            "\",\"source\":\"" ++ source ++
                            "\",\"target\":\"" ++ target ++
                            "\",\"label\":\"" ++ label ++ "\"}}"
                    ) children ++ map renderTreeEdges children)

main :: IO ()
main = do
    putStrLn "TreeMaker started..."
    (tree, finalSeenSet) <- runStateT buildTree HS.empty
    let output =
            "=== Execution tree (with erlNode hidden) ===\n"
            ++ renderTree True tree
            ++ "\n\n" ++
            -- "=== Execution tree (with erlNode shown) ===\n"
            -- ++ renderTree False tree=
            -- ++ "\n\n" ++
            "=== Hashes of seen nodes ===\n"
            ++ show (HS.toList finalSeenSet)

    writeFile "execution_tree.txt" output
    putStrLn "Execution tree saved to execution_tree.txt"

    -- JSON Builder --
    putStrLn "Building JSON..."
    let jsonNodeArray = renderJsonNodeArray finalSeenSet
    let jsonEdgeArray = renderJsonEdgeArray tree
    let jsonObject = "{\"elements\":{"
                     ++ jsonNodeArray ++ ","
                     ++ jsonEdgeArray ++ "}}"
    writeFile "./exe/tree-maker/graph-drawer/input.json" jsonObject
    putStrLn "Done!"
