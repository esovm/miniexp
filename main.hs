import qualified Data.Map as DM
import qualified Data.Set as DS
import qualified Data.Vector as DV

import Data.List
import Data.Maybe
import Data.Ord

import Debug.Trace

import Control.Monad.State

{- Basics -}

-- fact
newtype Fact = Fact String
  deriving (Eq, Ord, Show)

-- production's LHS
newtype LHS = LHS { lhs2facts :: [Fact] }
  deriving Show

-- production's RHS
newtype Assertion = Assert [Fact]
  deriving Show
data ExtAction = Continue | Exit
  deriving Show
data RHS = RHS Assertion ExtAction
  deriving Show

-- production
data Prod = LHS :=> RHS
  deriving Show

prodLHS :: Prod -> LHS
prodLHS (lhs :=> _) = lhs

prodRHS :: Prod -> RHS
prodRHS (_ :=> rhs) = rhs


{- Working Memory -}

-- fact recency value
type Recency = Int
type Fact2Recency = DM.Map Fact Recency

data WorkMem =
  WorkMem { wmFact2Recency :: Fact2Recency
          , wmCurrRecency  :: Recency }

-- checks whether there are a facts in working memory
hasFacts :: WorkMem -> [Fact] -> Bool
hasFacts wm = all (flip DM.member $ wmFact2Recency wm)

-- executes assertion
execAssertion :: Assertion -> WorkMem -> WorkMem
execAssertion (Assert []) wm              = wm
execAssertion (Assert fs) (WorkMem fr cr) =
  let fr' = foldl (\ fr f -> DM.insert f cr fr) fr fs
    in WorkMem fr' (cr + 1)
    
-- returns all facts
getFacts :: WorkMem -> [Fact]
getFacts = map fst . DM.toList . wmFact2Recency
    
-- returns fact's recency
getFactRecency :: WorkMem -> Fact -> Recency
getFactRecency wm f = (wmFact2Recency wm) DM.! f

-- removes facts from working memory
removeFacts :: WorkMem -> [Fact] -> WorkMem
removeFacts wm fs =
  let f2r = foldl (\ f2r f -> DM.delete f f2r) (wmFact2Recency wm) fs
    in WorkMem f2r $ wmCurrRecency wm
    
cleanWorkMem :: WorkMem -> WorkMem
cleanWorkMem wm =
  let fs' = DM.fromList $ map (\ f -> (f, 0)) $ getFacts wm
    in WorkMem fs' 1
    
{- Productions Data -}

type Concr = Int
type Prio  = Int
type ProdConcr = DV.Vector Concr
type ProdPrio  = DV.Vector Prio

type ProdVec = DV.Vector Prod

type ProdId = Int
type Fact2ProdId = DM.Map Fact ProdId 

data ProdData =
  ProdData { pdProdConcr   :: ProdConcr
           , pdProdPrio    :: ProdPrio
           , pdProdVec     :: ProdVec
           , pdFact2ProdId :: Fact2ProdId }
           
id2prod :: ProdData -> ProdId -> Prod
id2prod pd pId = (pdProdVec pd) DV.! pId 
           
type ProdUsed = DS.Set ProdId

-- returns id's of active productions which may (possibly) fire
-- (production must not be used)
activeProdIDs :: WorkMem -> ProdData -> ProdUsed ->  [ProdId]
activeProdIDs wm pd pu =
  filter (not . flip DS.member pu) $
    nub $ catMaybes $ map (flip DM.lookup f2p) $ getFacts wm
  where
    f2p = pdFact2ProdId pd

-- extracts conflict set from active productions ids
getConflictSet :: WorkMem -> ProdData -> [ProdId] -> [ProdId]
getConflictSet wm pd =
  filter (hasFacts wm . lhs2facts . prodLHS . id2prod pd)
  
-- returns recency of production 
getProdRecency :: WorkMem -> Prod -> Recency
getProdRecency wm = sum . map (getFactRecency wm) . lhs2facts . prodLHS

-- returns recency of production by it's id
id2recency :: WorkMem -> ProdData -> ProdId -> Recency
id2recency wm pd pId = wm `getProdRecency` (pd `id2prod` pId)

-- returns priority of production by it's id
id2prio :: ProdData -> ProdId -> Prio
id2prio pd pId = (pdProdPrio pd) DV.! pId

-- returns concreteness of production by it's id
id2concr :: ProdData -> ProdId -> Concr
id2concr pd pId = (pdProdConcr pd) DV.! pId

-- Resolves conflict set by getting a production
-- with maximum priority, recency and concreteness.
-- If conflict set is empty, then there is no rules
-- to apply.
resolveConflictSet :: WorkMem -> ProdData -> [ProdId] -> Maybe ProdId
resolveConflictSet _ _ [] = Nothing
resolveConflictSet wm pd ps =
  Just $ fst $ maximumBy (comparing snd) $
    map (\ pId -> (pId, getScore pId)) ps 
  where    
    getScore pId =
      let
        rec = id2recency wm pd pId
        pri = id2prio pd pId
        con = id2concr pd pId
      in rec + pri + con

-- Getting production to fire
getProdToFire :: WorkMem -> ProdData -> ProdUsed -> Maybe ProdId
getProdToFire wm pd pu =
    resolveConflictSet wm pd $ getConflictSet wm pd $ activeProdIDs wm pd pu 


{- Stateful part -}

-- state of execution
type ExecState = State (WorkMem, ProdData, ProdUsed)

data ExecResult = Failure | Success
  deriving Show

fwdExecStep :: ExecState ExecResult
fwdExecStep = traceShow "ff" $ do (wm, pd, pu) <- get
                                  case getProdToFire wm pd pu of
                                     Nothing -> return Failure
                                     Just p  -> do ext <- fireProd p
                                                   case ext of
                                                     Exit     -> return Success
                                                     Continue -> cleanData >> fwdExecStep

fireProd :: ProdId -> ExecState ExtAction
fireProd pId = do (wm, pd, pu) <- get
                  let (lhs :=> rhs) = id2prod pd pId
                      pu'           = DS.insert pId pu 
                      wm'           = removeFacts wm $ lhs2facts lhs
                  put (wm', pd, pu')
                  execRHS rhs                    

execRHS :: RHS -> ExecState ExtAction
execRHS (RHS a e) = do (wm, pd, pu) <- get
                       let wm' = execAssertion a wm
                       return e

cleanData :: ExecState ()
cleanData = do (wm, pd, pu) <- get
               let wm' = cleanWorkMem wm
               put (wm', pd, DS.empty)
    
runFwd :: [Fact] -> [(Prod, Prio)] -> ([Fact], ExecResult)
runFwd fs ps =
  let f2r   = foldl (\ f2r f -> DM.insert f 0 f2r) DM.empty fs
      wm    = WorkMem f2r 1
      pVec  = DV.fromList $ map fst ps
      prios = DV.fromList $ map snd ps
      n     = length ps
      pcons = DV.generate n (\ id -> length $ lhs2facts $ prodLHS $ pVec DV.! id)
      f2pid = foldl (\ f2pid (fs, pid) ->
                foldl (\ f2pid f -> DM.insert f pid f2pid) f2pid fs) DM.empty $
                  map (\ id -> (lhs2facts $ prodLHS $ pVec DV.! id, id)) [1..n]
      pd    = ProdData pcons prios pVec f2pid
      in case runState fwdExecStep (wm, pd, DS.empty) of
           (r, (wm', _, _)) -> (getFacts wm', r)

        
{- Forward inferring examples -}

allFacts  = [Fact "Animal is dead"
            ,Fact "Animal is alive"
            ,Fact "Object is animal"
            ,Fact "Object is human"
            ,Fact "Human is alive"
            ,Fact "Human is dead"
            ,Fact "Object can talk" ]
            
allProds = [LHS [Fact "Object can talk"] :=> RHS (Assert [Fact "Object is human"]) Continue]

facts = [Fact "Object can talk"]
prods = zeroPrio allProds

zeroPrio = map (\ p -> (p, 0))

runExpl = runFwd facts prods

