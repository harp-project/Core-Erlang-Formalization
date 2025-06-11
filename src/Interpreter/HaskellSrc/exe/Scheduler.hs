module Scheduler where

import qualified Prelude
import CoqExtraction

import qualified Data.HashMap.Strict
import qualified Data.HashSet

data Ne_list a =
   Ne_single a
 | Ne_cons a (Ne_list a)
 deriving (Prelude.Eq, Prelude.Show)

nth_error_ne :: (Ne_list a1) -> Prelude.Integer -> Prelude.Maybe a1
nth_error_ne l n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    case l of {
     Ne_single x -> Prelude.Just x;
     Ne_cons x _ -> Prelude.Just x})
    (\n' ->
    case l of {
     Ne_single _ -> Prelude.Nothing;
     Ne_cons _ l' -> nth_error_ne l' n'})
    n

length_ne :: (Ne_list a1) -> Prelude.Integer
length_ne l =
  case l of {
   Ne_single _ -> Prelude.succ 0;
   Ne_cons _ l' -> Prelude.succ (length_ne l')}

delete_nth_ne :: (Ne_list a1) -> Prelude.Integer -> Prelude.Maybe
                 (Ne_list a1)
delete_nth_ne l n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    case l of {
     Ne_single _ -> Prelude.Nothing;
     Ne_cons _ l' -> Prelude.Just l'})
    (\n' ->
    case l of {
     Ne_single _ -> Prelude.Nothing;
     Ne_cons x l' ->
      case l' of {
       Ne_single _ ->
        (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
          (\_ -> Prelude.Just (Ne_single x))
          (\_ -> Prelude.Nothing)
          n';
       Ne_cons _ _ ->
        case delete_nth_ne l' n' of {
         Prelude.Just l'' -> Prelude.Just (Ne_cons x l'');
         Prelude.Nothing -> Prelude.Nothing}}})
    n

data RRConfig =
   RREmpty
 | RRConf (Ne_list PID) Prelude.Integer
 deriving (Prelude.Eq, Prelude.Show)

currPID :: RRConfig -> Prelude.Maybe PID
currPID conf =
  case conf of {
   RREmpty -> Prelude.Nothing;
   RRConf l n -> nth_error_ne l n}

nextConf :: RRConfig -> RRConfig
nextConf conf =
  case conf of {
   RREmpty -> RREmpty;
   RRConf l n ->
    case ltb (Prelude.succ n) (length_ne l) of {
     Prelude.True -> RRConf l (Prelude.succ n);
     Prelude.False -> RRConf l 0}}

insertToConf :: RRConfig -> PID -> RRConfig
insertToConf conf p =
  case conf of {
   RREmpty -> RRConf (Ne_single p) 0;
   RRConf l n -> RRConf (Ne_cons p l) (Prelude.succ n)}

newConfByAction :: RRConfig -> Action -> RRConfig
newConfByAction conf a =
  case a of {
   ASpawn newPID _ _ _ -> insertToConf conf newPID;
   _ -> conf}

delCurrFromConf :: RRConfig -> RRConfig
delCurrFromConf conf =
  case conf of {
   RREmpty -> RREmpty;
   RRConf l n ->
    case delete_nth_ne l n of {
     Prelude.Just l' ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ -> RRConf l' (pred (length_ne l')))
        (\n' -> RRConf l' n')
        n;
     Prelude.Nothing -> RREmpty}}

makeInitialNodeConf :: Redex -> (,) ((,) ((,) Node RRConfig) PID)
                       (([]) ((,) PID PID))
makeInitialNodeConf r =
  let {
   p = Prelude.Left ((,) ((,) ((,) ((,) ([]) r) emptyBox) Data.HashSet.empty)
    Prelude.False)}
  in
  let {
   initPID = (\pids -> if Data.HashSet.null pids then 0 else (Prelude.maximum (Data.HashSet.toList pids) Prelude.+ 1))
               (usedPIDsProcNew p)}
  in
  (,) ((,) ((,) ((,) Data.HashMap.Strict.empty
  (Data.HashMap.Strict.singleton initPID p)) (RRConf (Ne_single initPID) 0))
  (Prelude.succ initPID)) ([])

