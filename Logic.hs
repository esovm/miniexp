
import qualified Data.Set as DS 
import qualified Data.Map as DM

import Control.Monad.State
import Control.Monad.Trans.Maybe

import Data.Maybe



data Term = Const String | Var String
  deriving (Eq, Show)

data Pred = Pred String [Term]
  deriving Show

data Formula = Atom Pred | And Formula Formula | Or Formula Formula



type Antecedent = Formula
type Succedent  = Pred
data Rule = Antecedent :=> Succedent


type PredMap = DM.Map String [Term]
type WorkMem = State PredMap

deleteElem _ _ = Nothing
       
lhsCheck :: Formula -> MaybeT WorkMem ()

lhsCheck (Atom (Pred name args)) =
  do (mArgs, mem') <- fmap (DM.updateLookupWithKey deleteElem name) get
     guard (isJust mArgs)
     let args' = fromJust mArgs
     guard (args == args')
     put mem'
     return ()

lhsCheck (And a b) =
  lhsCheck a >> lhsCheck b
  
lhsCheck (Or a b) =
  lhsCheck a `mplus` lhsCheck b

fwdApplyRule :: Rule -> MaybeT WorkMem ()
fwdApplyRule (ant :=> Pred name args) =
  lhsCheck ant >> (put $ DM.singleton name args) 
     
fwdInferring :: [Rule] -> MaybeT WorkMem ()
fwdInferring = msum . map fwdApplyRule -- laziness is great !!!
     
runFwdInferring :: [Pred] -> [Rule] -> [Pred]
runFwdInferring ps rs = fromMem $ snd $ runState (runMaybeT (fwdInferring rs)) mem
  where
    mem = DM.fromList $ map (\ (Pred name args) -> (name, args)) ps
    fromMem = map (\ (name, args) -> Pred name args) . DM.toList
-------------------------------

mem = DM.insert "IsHuge" [Const "MyHouse"] $ DM.singleton "HasPony" [Const "Tony"]

exp1 = runState (runMaybeT (lhsCheck (Atom (Pred "IsHuge" [Const "MyHouse"])))) mem

-- can't use twice check
exp2 = runState (
          runMaybeT (
            lhsCheck (
              And (Atom (Pred "IsHuge" [Const "MyHouse"])) (Atom (Pred "IsHuge" [Const "MyHouse"]))))) mem

exp3 = runState (
          runMaybeT (
            lhsCheck (
              And (Atom (Pred "IsHuge" [Const "MyHouse"])) (Atom (Pred "HasPony" [Const "Tony"]))))) mem

exp4 = runState (
          runMaybeT (
            lhsCheck (
              Or (Atom (Pred "IsHuge" [Const "MyHouse"])) (Atom (Pred "IsHuge" [Const "MyHouse"]))))) mem

preds = [Pred "IsHuge" [Const "MyHouse"]
        ,Pred "HasPony" [Const "Tony"]]
        
rules = [Atom (Pred "IsHuge" [Const "MyHouse"]) :=> Pred "GreatHouse" [Const "MyHouse"]]

