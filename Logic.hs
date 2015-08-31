
import qualified Data.Set as DS 
import qualified Data.Map as DM

import Control.Monad.State
import Control.Monad.Trans.Maybe

import Data.Maybe



data Term = Const String | Var String
  deriving (Eq, Show)

data Pred = Pred String [Term]

data Formula = Atom Pred | And Formula Formula | Or Formula Formula



type Antecedent = Formula
type Succedent  = Pred
data Rule = Antecedent :=> Succedent


type PredMap = DM.Map String [Term]
type WorkMem = State PredMap

deleteElem _ _ = Nothing
       
fwdInfer :: Formula -> MaybeT WorkMem ()

fwdInfer (Atom (Pred name args)) =
  do (mArgs, mem') <- fmap (DM.updateLookupWithKey deleteElem name) get
     guard (isJust mArgs)
     let args' = fromJust mArgs
     guard (args == args')
     put mem'
     return ()

fwdInfer (And a b) =
  fwdInfer a >> fwdInfer b
  
fwdInfer (Or a b) =
  fwdInfer a `mplus` fwdInfer b
     
-------------------------------

mem = DM.insert "IsHuge" [Const "MyHouse"] $ DM.singleton "HasPony" [Const "Tony"]

exp1 = runState (runMaybeT (fwdInfer (Atom (Pred "IsHuge" [Const "MyHouse"])))) mem

-- can't use twice check
exp2 = runState (
          runMaybeT (
            fwdInfer (
              And (Atom (Pred "IsHuge" [Const "MyHouse"])) (Atom (Pred "IsHuge" [Const "MyHouse"]))))) mem

exp3 = runState (
          runMaybeT (
            fwdInfer (
              And (Atom (Pred "IsHuge" [Const "MyHouse"])) (Atom (Pred "HasPony" [Const "Tony"]))))) mem

exp4 = runState (
          runMaybeT (
            fwdInfer (
              Or (Atom (Pred "IsHuge" [Const "MyHouse"])) (Atom (Pred "IsHuge" [Const "MyHouse"]))))) mem


