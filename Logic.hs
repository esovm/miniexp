{-# LANGUAGE GADTs #-}

import qualified Data.Set as DS 
import qualified Data.Map as DM
import qualified Data.Vector as DV

import Control.Monad.State
import Control.Monad.Trans.Maybe

import Data.List
import Data.Maybe
import Data.Ord

{-
  Fact definition. It's just a string. But it's made
  as `newtype` in order to make different `Show` and
  other classes instances.
-}
newtype Fact = Fact { factToString :: String }
  deriving (Eq, Ord)

{-
  Fact's recency
-}
newtype Recency = Recency { recencyToInt :: Int }

type Fact2Recency = DM.Map Fact Recency

{-
  Goal definition
-}
data Action = Assert Fact
            | Terminate
            deriving (Eq, Ord)
            
type Goal = [Action]
            
{-
  Productions
-}
data Prod = [Fact] :=> [Action]
{-
  Getters
-}
prodLHS :: Prod -> [Fact]
prodLHS (fs :=> _) = fs

prodRHS :: Prod -> [Action]
prodRHS (_ :=> as) = as

{-
  Production's concreteness
-}
newtype Concr = Concr { concrToInt :: Int }
{-
  Production's priority
-}
newtype Prio  = Prio { prioToInt :: Int }

{-
  Production's concreteness and Production's priorities
  are constant (or at least are rarely updating values).
  So it's possible to express them as vectors.
-}
type ProdConcr = DV.Vector Concr
type ProdPrio  = DV.Vector Prio

{-
  Productions won'e be added frequently (or won't be at all).
  So we can keep them in vector.
-}
type ProdVec = DV.Vector Prod

{-
  Having productions inside vector give us an ability
  to access productions via their index. We'll call
  it production's id. 
-}
type ProdID = Int

{-
  Also, we can find what rule was most effective
  for reaching a particular goal.
-}
newtype Usef = Usef { usefToInt :: Int }
type ProdUsef = DM.Map (ProdID, Goal) Usef -- how useful was production with ProdID
                                           -- in reaching a goal Goal.
                                           
{-
  Working memory. It consists from dynamic data.
-}
data WorkMem =
  WorkMem { wmFact2Rec :: Fact2Recency
          , wmMaxRec   :: Recency
          , wmProdUsef :: ProdUsef }

workMemFacts :: WorkMem -> [Fact]
workMemFacts = map fst . DM.toList . wmFact2Rec

{-
  Checks whether there are a facts in working memory
-}
hasFacts :: WorkMem -> [Fact] -> Bool
hasFacts wm = all (flip DM.member $ wmFact2Rec wm)


{-
  Productions data (or static (or almost static) memory)
-}
data ProdData =
  ProdData { pdProdConcr   :: ProdConcr
           , pdProdPrio    :: ProdPrio
           , pdProdVec     :: ProdVec
           , pdFact2ProdID :: Fact2ProdID }

restoreProd :: ProdData -> ProdID -> Prod
restoreProd pd pIDs = pv DV.! pIDs
  where
    pv = pdProdVec pd
           
restoreProds :: ProdData -> [ProdID] -> [Prod]
restoreProds pd pIDs = map ((DV.!) pv) pIDs
  where
    pv = pdProdVec pd

{-
  Map from facts to productions. It should
  help to limit the number of productions
  in searching for conflict set.
-}
type Fact2ProdID = DM.Map Fact ProdID
           
{-
  System's state.
-}
newtype SysState = SysState (WorkMem, ProdData)

{-
  Returns active productions which may be (possibly) applied.
-}
activeProdIDs :: SysState -> [ProdID]
activeProdIDs (SysState (wm, pd)) =
  nub $ catMaybes $ map (flip DM.lookup f2p) $ workMemFacts wm
  where
    f2p = pdFact2ProdID pd

type ProdUsed = DS.Set ProdID

{-
  Getting productions which can be fired.
  Or, getting conflict set of productions.
-}
getConflictSet :: ProdUsed -> SysState -> [ProdID]
getConflictSet ss@(SysState (wm, pd)) =
  filter (hasFacts wm . prodLHS . restoreProd pd) $ activeProdIDs ss
  
{-
  Returns a production from conflict set to apply
  (conflict set resolution).
-}
resolveConflictSet :: [ProdID] -> Goal -> SysState -> Maybe ProdID
resolveConflictSet [] _ _ = Nothing
resolveConflictSet pIDs goal (SysState (wm, pd)) =
  Just $ fst $ maximumBy (comparing snd) $
    map (\ pId -> (pId, getScore pId)) pIDs 
  where    

    getPUsef pId =
      case DM.lookup (pId, goal) (wmProdUsef wm) of
             Just a  -> a
             Nothing -> Usef 0
             
    getPRecency pId = Recency $ sum $
      map (recencyToInt . (DM.!) (wmFact2Rec wm)) $ prodLHS $ restoreProd pd pId

    getPConcr pId = (pdProdConcr pd) DV.! pId
    getPPrio  pId = (pdProdPrio pd)  DV.! pId
    
    getScore pId = combine (getPConcr   pId)
                           (getPPrio    pId)
                           (getPRecency pId)
                           (getPUsef    pId)
   

-- Combines Usef Concr Prio and Recency into score
combine :: Concr -> Prio -> Recency -> Usef -> Int
combine (Concr c) (Prio p) (Recency r) (Usef u) =
  c + p + r + u
  
-- Getting production to fire
getProdToFire :: Goal -> SysState -> Maybe ProdID
getProdToFire goal sysState =
  resolveConflictSet (getConflictSet sysState) goal sysState
  
{-
  Next fuctions are stateful
-}

--type ExpSysState = State (SysState, DS.Set ProdID)
