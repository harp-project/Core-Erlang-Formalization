
module Main where

import CoqExtraction
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

-- I am nothing without my code completion
-- data Lit =
--    Atom Prelude.String
--  | Integer Prelude.Integer
-- data Pat =
--    PVar
--  | PLit Lit
--  | PCons Pat Pat
--  | PTuple (([]) Pat)
--  | PMap (([]) ((,) Pat Pat))
--  | PNil
-- type FunId = (,) Prelude.Integer Prelude.Integer
-- type Var = Prelude.Integer
-- data Exp =
--    VVal Val
--  | EExp NonVal
-- data Val =
--    VNil
--  | VLit Lit
--  | VPid PID
--  | VCons Val Val
--  | VTuple (([]) Val)
--  | VMap (([]) ((,) Val Val))
--  | VVar Var
--  | VFunId FunId
--  | VClos (([]) ((,) ((,) Prelude.Integer Prelude.Integer) Exp)) Prelude.Integer
--  Prelude.Integer Exp
-- data NonVal =
--    EFun Prelude.Integer Exp
--  | EValues (([]) Exp)
--  | ECons Exp Exp
--  | ETuple (([]) Exp)
--  | EMap (([]) ((,) Exp Exp))
--  | ECall Exp Exp (([]) Exp)
--  | EPrimOp Prelude.String (([]) Exp)
--  | EApp Exp (([]) Exp)
--  | ECase Exp (([]) ((,) ((,) (([]) Pat) Exp) Exp))
--  | ELet Prelude.Integer Exp Exp
--  | ESeq Exp Exp
--  | ELetRec (([]) ((,) Prelude.Integer Exp)) Exp
--  | ETry Exp Prelude.Integer Exp Prelude.Integer Exp
-- data ExcClass =
--    Error
--  | Throw
--  | Exit
-- type Exception = (,) ((,) ExcClass Val) Val
-- type ValSeq = ([]) Val
-- data Redex =
--    RExp Exp
--  | RValSeq ValSeq
--  | RExc Exception
--  | RBox
-- data FrameIdent =
--    IValues
--  | ITuple
--  | IMap
--  | ICall Val Val
--  | IPrimOp Prelude.String
--  | IApp Val
-- data Frame =
--    FCons1 Exp
--  | FCons2 Val
--  | FParams FrameIdent (([]) Val) (([]) Exp)
--  | FApp1 (([]) Exp)
--  | FCallMod Exp (([]) Exp)
--  | FCallFun Val (([]) Exp)
--  | FCase1 (([]) ((,) ((,) (([]) Pat) Exp) Exp))
--  | FCase2 (([]) Val) Exp (([]) ((,) ((,) (([]) Pat) Exp) Exp))
--  | FLet Prelude.Integer Exp
--  | FSeq Exp
--  | FTry Prelude.Integer Exp Prelude.Integer Exp
-- type FrameStack = ([]) Frame
-- type Decision = Prelude.Bool
-- type RelDecision a b = a -> b -> Decision
-- type Mapset' munit =
--   munit
--   -- singleton inductive, whose constructor was Mapset 
-- type Gmap k a = HM.HashMap k a
--   -- singleton inductive, whose constructor was GMap
-- type Gset k = HS.HashSet k
-- type Mailbox = (,) (([]) Val) (([]) Val)
-- type ProcessFlag = Prelude.Bool
-- type LiveProcess =
--   (,) ((,) ((,) ((,) FrameStack Redex) Mailbox) (Gset PID)) ProcessFlag
-- type DeadProcess = Gmap PID Val
-- type Process = Prelude.Either LiveProcess DeadProcess
-- data Signal =
--    SMessage Val
--  | SExit Val Prelude.Bool
--  | SLink
--  | SUnlink
-- data Action =
--    ASend PID PID Signal
--  | AArrive PID PID Signal
--  | ASelf PID
--  | ASpawn PID Val Val Prelude.Bool
--  | Coq__UU03c4_
--  | Coq__UU03b5_
-- type PID = Prelude.Integer
-- type Ether = Gmap ((,) PID PID) (([]) Signal)
-- type ProcessPool = Gmap PID Process
-- type Node = (,) Ether ProcessPool

-- makeInitialNode :: Redex -> Node
-- makeInitialNode = undefined
-- nodeTauFirstStep :: Node -> PID -> Prelude.Maybe ((,) Node (([]) Action))
-- nodeTauFirstStep = undefined
-- interProcessStepFunc :: Node -> Action -> PID -> Prelude.Maybe Node
-- interProcessStepFunc = undefined
-- makeInitialConfig :: Redex -> (,) Node PID
-- makeInitialConfig = undefined
-- testpmap :: NonVal
-- testpmap = undefined

-- deriving instance Prelude.Show Lit
-- deriving instance GHC.Base.Eq Lit
-- deriving instance Prelude.Show Pat
-- deriving instance GHC.Base.Eq Pat
-- deriving instance Prelude.Show Exp
-- deriving instance GHC.Base.Eq Exp
-- deriving instance Prelude.Show Val
-- deriving instance GHC.Base.Eq Val
-- deriving instance Prelude.Show NonVal
-- deriving instance GHC.Base.Eq NonVal
-- deriving instance Prelude.Show ExcClass
-- deriving instance GHC.Base.Eq ExcClass
-- deriving instance Prelude.Show Redex
-- deriving instance GHC.Base.Eq Redex
-- deriving instance Prelude.Show FrameIdent
-- deriving instance GHC.Base.Eq FrameIdent
-- deriving instance Prelude.Show Frame
-- deriving instance GHC.Base.Eq Frame
-- deriving instance Prelude.Show Signal
-- deriving instance GHC.Base.Eq Signal
-- deriving instance Prelude.Show Action
-- deriving instance GHC.Base.Eq Action

-- -- ====================| instances of Hashable for TreeMaker.hs |====================
-- -- Since the possible non-arrival actions' collection for each tree node is a HashSet
-- -- type Action needs to have a Hashable instance.
-- -- Done in a hacky way: first we hash an int representing the constructor type and
-- -- then proceed to hash an actual value of the datatype.
-- -- P.S. potentially not needed, if you change th type of possibleNAActions to list.

-- instance Hashable Lit where
--   hashWithSalt s (Atom a)   = s `hashWithSalt` (0::Int) `hashWithSalt` a
--   hashWithSalt s (Integer n)= s `hashWithSalt` (1::Int) `hashWithSalt` n

-- instance Hashable Exp where
--   hashWithSalt s (VVal v)   = s `hashWithSalt` (0::Int) `hashWithSalt` v
--   hashWithSalt s (EExp e)   = s `hashWithSalt` (1::Int) `hashWithSalt` e

-- instance Hashable Pat where
--   hashWithSalt s PVar              = s `hashWithSalt` (0::Int)
--   hashWithSalt s (PLit l)          = s `hashWithSalt` (1::Int) `hashWithSalt` l
--   hashWithSalt s (PCons p1 p2)     = s `hashWithSalt` (2::Int) `hashWithSalt` p1 `hashWithSalt` p2
--   hashWithSalt s (PTuple ps)       = s `hashWithSalt` (3::Int) `hashWithSalt` ps
--   hashWithSalt s (PMap xs)         = s `hashWithSalt` (4::Int) `hashWithSalt` xs
--   hashWithSalt s PNil              = s `hashWithSalt` (5::Int)

-- instance Hashable ExcClass where
--   hashWithSalt s Exit = s `hashWithSalt` (0::Int)
--   hashWithSalt s Error = s `hashWithSalt` (1::Int)
--   hashWithSalt s Throw = s `hashWithSalt` (2::Int)

-- instance Hashable Redex where
--   hashWithSalt s (RExp e)    = s `hashWithSalt` (0::Int) `hashWithSalt` e
--   hashWithSalt s (RValSeq v) = s `hashWithSalt` (1::Int) `hashWithSalt` v
--   hashWithSalt s (RExc ex)   = s `hashWithSalt` (2::Int) `hashWithSalt` ex
--   hashWithSalt s RBox        = s `hashWithSalt` (3::Int)

-- instance Hashable NonVal where
--   hashWithSalt s (EFun i e)          = s `hashWithSalt` (0::Int) `hashWithSalt` i `hashWithSalt` e
--   hashWithSalt s (EValues xs)        = s `hashWithSalt` (1::Int) `hashWithSalt` xs
--   hashWithSalt s (ECons a b)         = s `hashWithSalt` (2::Int) `hashWithSalt` a `hashWithSalt` b
--   hashWithSalt s (ETuple es)         = s `hashWithSalt` (3::Int) `hashWithSalt` es
--   hashWithSalt s (EMap xs)           = s `hashWithSalt` (4::Int) `hashWithSalt` xs
--   hashWithSalt s (ECall a b cs)      = s `hashWithSalt` (5::Int) `hashWithSalt` a `hashWithSalt` b `hashWithSalt` cs
--   hashWithSalt s (EPrimOp op es)     = s `hashWithSalt` (6::Int) `hashWithSalt` op `hashWithSalt` es
--   hashWithSalt s (EApp f args)       = s `hashWithSalt` (7::Int) `hashWithSalt` f `hashWithSalt` args
--   hashWithSalt s (ECase e xs)        = s `hashWithSalt` (8::Int) `hashWithSalt` e `hashWithSalt` xs
--   hashWithSalt s (ELet v e1 e2)      = s `hashWithSalt` (9::Int) `hashWithSalt` v `hashWithSalt` e1 `hashWithSalt` e2
--   hashWithSalt s (ESeq a b)          = s `hashWithSalt` (10::Int) `hashWithSalt` a `hashWithSalt` b
--   hashWithSalt s (ELetRec xs e)      = s `hashWithSalt` (11::Int) `hashWithSalt` xs `hashWithSalt` e
--   hashWithSalt s (ETry body v1 h1 v2 h2) =
--     s `hashWithSalt` (12::Int)
--       `hashWithSalt` body
--       `hashWithSalt` v1
--       `hashWithSalt` h1
--       `hashWithSalt` v2
--       `hashWithSalt` h2

-- instance Hashable Val where
--   hashWithSalt s VNil            = s `hashWithSalt` (0::Int)
--   hashWithSalt s (VLit l)        = s `hashWithSalt` (1::Int) `hashWithSalt` l
--   hashWithSalt s (VPid p)        = s `hashWithSalt` (2::Int) `hashWithSalt` p
--   hashWithSalt s (VCons a b)     = s `hashWithSalt` (3::Int) `hashWithSalt` a `hashWithSalt` b
--   hashWithSalt s (VTuple xs)     = s `hashWithSalt` (4::Int) `hashWithSalt` xs
--   hashWithSalt s (VMap xs)       = s `hashWithSalt` (5::Int) `hashWithSalt` xs
--   hashWithSalt s (VVar v)        = s `hashWithSalt` (6::Int) `hashWithSalt` v
--   hashWithSalt s (VFunId f)      = s `hashWithSalt` (7::Int) `hashWithSalt` f
--   hashWithSalt s (VClos env a b e) =
--     s `hashWithSalt` (8::Int)
--       `hashWithSalt` env
--       `hashWithSalt` a
--       `hashWithSalt` b
--       `hashWithSalt` e

-- instance Hashable Signal where
--   hashWithSalt s (SMessage v)  = s `hashWithSalt` (0::Int) `hashWithSalt` v
--   hashWithSalt s (SExit v b)   = s `hashWithSalt` (1::Int) `hashWithSalt` v `hashWithSalt` b
--   hashWithSalt s SLink         = s `hashWithSalt` (2::Int)
--   hashWithSalt s SUnlink       = s `hashWithSalt` (3::Int)

-- instance Hashable Action where
--   hashWithSalt s (ASend p1 p2 sig) =
--     s `hashWithSalt` (0::Int) `hashWithSalt` p1
--       `hashWithSalt` p2 `hashWithSalt` sig

--   hashWithSalt s (AArrive p1 p2 sig) =
--     s `hashWithSalt` (1::Int) `hashWithSalt` p1
--       `hashWithSalt` p2 `hashWithSalt` sig

--   hashWithSalt s (ASelf pid) =
--     s `hashWithSalt` (2::Int) `hashWithSalt` pid

--   hashWithSalt s (ASpawn pid v1 v2 b) =
--     s `hashWithSalt` (3::Int)
--       `hashWithSalt` pid
--       `hashWithSalt` v1
--       `hashWithSalt` v2
--       `hashWithSalt` b

--   hashWithSalt s Coq__UU03c4_ = s `hashWithSalt` (4::Int)
--   hashWithSalt s Coq__UU03b5_ = s `hashWithSalt` (5::Int)

-- instance Hashable FrameIdent where
--   hashWithSalt s IValues         = s `hashWithSalt` (0::Int)
--   hashWithSalt s ITuple          = s `hashWithSalt` (1::Int)
--   hashWithSalt s IMap            = s `hashWithSalt` (2::Int)
--   hashWithSalt s (ICall a b)     = s `hashWithSalt` (3::Int) `hashWithSalt` a `hashWithSalt` b
--   hashWithSalt s (IPrimOp op)    = s `hashWithSalt` (4::Int) `hashWithSalt` op
--   hashWithSalt s (IApp v)        = s `hashWithSalt` (5::Int) `hashWithSalt` v

-- instance Hashable Frame where
--   hashWithSalt s (FCons1 e)          = s `hashWithSalt` (0::Int) `hashWithSalt` e
--   hashWithSalt s (FCons2 v)          = s `hashWithSalt` (1::Int) `hashWithSalt` v
--   hashWithSalt s (FParams frameid vs es)  =
--     s `hashWithSalt` (2::Int) `hashWithSalt` frameid
--       `hashWithSalt` vs `hashWithSalt` es
--   hashWithSalt s (FApp1 es)          = s `hashWithSalt` (3::Int) `hashWithSalt` es
--   hashWithSalt s (FCallMod e es)     = s `hashWithSalt` (4::Int) `hashWithSalt` e `hashWithSalt` es
--   hashWithSalt s (FCallFun v es)     = s `hashWithSalt` (5::Int) `hashWithSalt` v `hashWithSalt` es
--   hashWithSalt s (FCase1 xs)         = s `hashWithSalt` (6::Int) `hashWithSalt` xs
--   hashWithSalt s (FCase2 vs e xs)    = s `hashWithSalt` (7::Int) `hashWithSalt` vs `hashWithSalt` e `hashWithSalt` xs
--   hashWithSalt s (FLet v e)          = s `hashWithSalt` (8::Int) `hashWithSalt` v `hashWithSalt` e
--   hashWithSalt s (FSeq e)            = s `hashWithSalt` (9::Int) `hashWithSalt` e
--   hashWithSalt s (FTry v1 e1 v2 e2)  =
--     s `hashWithSalt` (10::Int)
--       `hashWithSalt` v1 `hashWithSalt` e1
--       `hashWithSalt` v2 `hashWithSalt` e2

-- I am nothing without my code complete END

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
                -- Better to alter the Coq definition of nodeTauFirstStep
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
