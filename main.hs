
import qualified Data.Map as DM
import qualified Data.Set as DS
import qualified Data.Vector as DV

import Data.List
import Data.Maybe
import Data.Ord

import Debug.Trace

import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Reader

import Control.Applicative
-- -- -- -- -- -- -- -- -- -- -- -- -- --


{-
  Facts are just strings.
-}
newtype Fact = Fact String
  deriving (Eq, Ord, Show)

{-
  Rules are of type:
  
    if A & B ... & C then D.
-}
data Rule = [Fact] :=> Fact
  deriving (Eq, Ord, Show)
  
-- condition
ruleCondt :: Rule -> [Fact]
ruleCondt (condt :=> _) = condt

-- conclusion
ruleConcl :: Rule -> Fact
ruleConcl (_ :=> concl) = concl

{-
  Forward inferrence mechanic:
  
    1) If there is a fact in working memory,
    then it's true fact.
  
    2) Once rule was apllied, it's conditions
    are removed from working memory.

    3) Once rule was applied, it's conclusion
    is added to working memory.

    4) If there is no rule to apply, then
    inferrence terminates.

-}

-- Concreteness
newtype Concr = Concr Int
  deriving Show

ruleConcr :: Rule -> Concr
ruleConcr (cond :=> _) = Concr $ length cond

{-
  
  Inferrence Engine.

  In order to avoid trying to apply all rules available
  we may try rules which conditions are partially or
  fully contains in working memory.
-}

newtype RuleId = RuleId Int
  deriving (Eq, Ord, Show)

data Engine =
  Engine { engId2Rule  :: DV.Vector Rule
         , engId2Concr :: DV.Vector Concr
         , engCond2Ids :: DM.Map Fact (DS.Set RuleId)  -- which rules has this fact as condition
         , engRule2Id  :: DM.Map Rule RuleId
         , engConc2Ids :: DM.Map Fact (DS.Set RuleId) }-- which rules has this fact as conclusion

--
id2Rule :: Engine -> RuleId -> Rule
id2Rule eng rId = (engId2Rule eng) DV.! (toInt rId)

--
id2Concr :: Engine -> RuleId -> Concr
id2Concr eng rId = (engId2Concr eng) DV.! (toInt rId)

--
cond2ids :: Engine -> Fact -> DS.Set RuleId
cond2ids eng f = (engCond2Ids eng) DM.! f

--

lookupIdsByGoal :: Engine -> Fact -> Maybe (DS.Set RuleId)
lookupIdsByGoal eng f = DM.lookup f (engConc2Ids eng)

--
lookupIdsByFact :: Engine -> Fact -> Maybe (DS.Set RuleId)
lookupIdsByFact eng f = DM.lookup f (engCond2Ids eng)

--
rule2id :: Engine -> Rule -> RuleId
rule2id eng r = (engRule2Id eng) DM.! r

initEngine :: [Rule] -> Engine
initEngine rs = let
  size   = length rs
  i2r    = DV.fromListN size rs
  i2c    = DV.fromListN size $ map ruleConcr rs
  cnd2is = initCond2Ids
  r2i    = DM.fromList idxRs
  cnc2is = initConc2Ids
  
  in Engine i2r i2c cnd2is r2i cnc2is
  where
    
    idxRs = zip rs $ map RuleId [0..] 
    
    initCond2Ids =
      let idxFs = map (\ (r, i) -> (ruleCondt r, i)) idxRs
        in foldl insertCondt DM.empty idxFs
        where
          insertCondt f2is (condt, id) =
            let idS = DS.singleton id in
              foldl (\ f2is f -> DM.insertWith DS.union f idS f2is) f2is condt 
       
    initConc2Ids =
      let idxCs = map (\ (r, i) -> (ruleConcl r, i)) idxRs
        in foldl (\ c2is (c, i) ->
              DM.insertWith DS.union c (DS.singleton i) c2is) DM.empty idxCs
       
printEngine :: Engine -> IO ()
printEngine (Engine i2r i2c cnd2is r2i cnc2ids) =
  do putStrLn "Inferrence engine\n"
     putStrLn ("Rules:\n" ++ show i2r)
     putStrLn ("Rule's concretenesses:\n" ++ show i2c)
     putStrLn ("Facts and related rules (by id):\n" ++ show cnd2is)
     putStrLn ("Rule's ids:\n" ++ show r2i)
     putStrLn ("Goals to rules:\n" ++ show cnc2ids)
        
{- Working memory -}

-- Recency
newtype Recency = Recency Int
  deriving (Eq, Ord, Show)

-- Working memory
newtype WorkMem =
  WorkMem { wmFact2Recency :: DM.Map Fact Recency }
  
hasFact :: WorkMem -> Fact -> Bool
hasFact wm = flip DM.member (wmFact2Recency wm)

hasFacts :: WorkMem -> [Fact] -> Bool
hasFacts wm fs =
  let fm = DM.fromList $ map (\ f -> (f, Recency 0)) fs
    in fm `DM.isSubmapOf` wmFact2Recency wm 

initWorkMem :: [Fact] -> WorkMem
initWorkMem fs = WorkMem $ DM.fromList $ zip fs $ repeat $ Recency 0

-- Working memory's facts
workMemFacts :: WorkMem -> [Fact]
workMemFacts = map fst . DM.toList . wmFact2Recency

-- Recency of fact
factRecency :: WorkMem -> Fact -> Recency
factRecency (WorkMem f2r) f = f2r DM.! f

lookupRecency :: WorkMem -> Fact -> Maybe Recency
lookupRecency (WorkMem f2r) f = DM.lookup f f2r

-- Recency of rule (by it's id)
ruleRecency :: WorkMem -> Engine -> RuleId -> Recency
ruleRecency wm eng rId = combine $
  catMaybes $ map (lookupRecency wm) $ ruleCondt $ id2Rule eng rId
  where
    combine = Recency . sum . map (\ (Recency r) -> r)
    
-- Retrieves set of rules (by ids) related to current
-- working memory state.
activeSet :: WorkMem -> Engine -> DS.Set RuleId
activeSet wm eng = DS.unions $ catMaybes $
  workMemFacts wm >>= pure . lookupIdsByFact eng
  
-- Makes a conflict set (set of rules which can be applied)
-- from a given set of rule's ids.
conflictSet :: WorkMem -> Engine -> DS.Set RuleId -> DS.Set RuleId
conflictSet wm eng = DS.map fst .
  DS.filter (hasFacts wm . ruleCondt . snd) .
    DS.map (\ id -> (id, id2Rule eng id)) 

-- Once we got conflict set, we are sure we can apply any
-- it's rule. So we can just pick one with higher priority.
-- Priority here is a sum of rule's recency with rule's
-- concreteness values.
getIdToFire :: WorkMem -> Engine -> DS.Set RuleId -> RuleId
getIdToFire wm eng = getWithMaxPrio
  {-if DS.null rs
    then Nothing
    else Just $ getWithMaxPrio rs 
  -}
  where
  
    getPrio id = sum $ [concr, recen] <*> [id]

    concr = toInt . id2Concr eng
    recen = toInt . ruleRecency wm eng

    getWithMaxPrio = fst . maximumBy (comparing snd) .
                       map (\ id -> (id, getPrio id)) . DS.toList 


-- Forward Inferrence mode --

type CycleCounter = Int

type InfState r = MaybeT (ReaderT Engine (StateT (WorkMem, CycleCounter) IO)) r

toInfState :: Maybe a -> InfState a
toInfState = MaybeT . return

fwdGetCycleCount :: InfState CycleCounter
fwdGetCycleCount = do (_, c) <- get
                      return c

fwdConflict :: InfState (DS.Set RuleId)
fwdConflict = do eng     <- ask
                 (wm, _) <- get
                 return $ conflictSet wm eng (activeSet wm eng)
                 
fwdRuleToFire :: DS.Set RuleId -> InfState Rule
fwdRuleToFire rs = do eng <- ask
                      (wm, _) <- get
                      return $ id2Rule eng $ getIdToFire wm eng rs

fwdFireRule :: Rule -> InfState ()
fwdFireRule (ant :=> suc) =
  do (wm, c) <- get
     let antM = DM.fromList $ zip ant $ repeat $ Recency 0
         m'   = wmFact2Recency wm DM.\\ antM
         m''  = DM.insert suc (Recency c) m'
         wm'  = WorkMem m''
     put (wm', c)
     
fwdPrintRulesByIds :: DS.Set RuleId -> InfState ()
fwdPrintRulesByIds rIDs =
  do eng <- ask
     liftIO $ printRules $ map (id2Rule eng) $ DS.toList rIDs
     
fwdPrintWorkMem :: InfState ()
fwdPrintWorkMem = do (wm, _) <- get
                     liftIO $ printWorkMem wm
     
fwdIncCounter :: InfState ()
fwdIncCounter = do (wm, c) <- get
                   put (wm, c + 1)
        
fwdMode :: InfState ()
fwdMode = do c <- fwdGetCycleCount

             when (c == 1) $
               liftIO $ putStrLn "Start."

             liftIO $ putStrLn $ "Forward Mode. Step " ++ show c ++ ";\n"
             
             cnfRs <- fwdConflict
             
             liftIO $ putStrLn "Conflict Set:"
             fwdPrintRulesByIds cnfRs
             liftIO $ putStr "\n"
             
             if DS.null cnfRs
               then do liftIO $ putStrLn "Conflict set is empty. Result:"
                       fwdPrintWorkMem
                                 
               else do r <- fwdRuleToFire cnfRs   
                       
                       liftIO $ do putStrLn "Firing Rule:"
                                   printRule r
                                   putStr "\n"
                       
                       fwdFireRule r
                       
                       fwdPrintWorkMem
                       liftIO $ putStr "\n\n"
               
                       fwdIncCounter        
                       fwdMode
         
runFwdMode :: WorkMem -> Engine -> IO (Maybe (), (WorkMem, CycleCounter))
runFwdMode wm eng = runStateT (runReaderT (runMaybeT fwdMode) eng) (wm, 1)


{- toString like functions -}

showFacts :: [Fact] -> String
showFacts fs =
  let (h, t) = splitAt 1 $ map show fs
      t'     = map (' ':) t
      in between "[" "]" $ intercalate ",\n" $ h ++ t'
  where
    between l r m = l ++ m ++ r

showRule :: Rule -> String
showRule (ant :=> suc) =
  showFacts ant ++ "\n" ++ conclInd ++ ":=> " ++ show suc
  where
    conclIndLen = 4
    conclInd = replicate conclIndLen ' '
    
showRules :: [Rule] -> String
showRules [] = "-- \\\\ --"
showRules rs = intercalate ";\n" $ map showRule rs

showWorkMem :: WorkMem -> String
showWorkMem = ("Working Memory:\n" ++) .
  intercalate ";\n" .
    map (\ (f, r) -> factInd ++ show f ++ "; " ++ show r) .
      DM.toList . wmFact2Recency
  where
    factIndLen = 2
    factInd = replicate factIndLen ' '
    
printWorkMem = putStrLn . showWorkMem
printRules   = putStrLn . showRules
printRule    = putStrLn . showRule
--printFact    = putStrLn . showFact
printFacts   = putStrLn . showFacts
    
--------------------------------------------------------------
{- Backward inferrence mode -}

conflictRules :: Engine -> Fact -> [RuleId]
conflictRules eng goal =
  case lookupIdsByGoal eng goal of
    Nothing -> []
    Just rs -> DS.toList rs

bwdConflict :: Fact -> InfState [Rule]
bwdConflict goal = do eng <- ask
                      return $ map (id2Rule eng) $ conflictRules eng goal

bwdSubGoals :: Fact -> InfState [[Fact]]
bwdSubGoals goal = do rs  <- bwdConflict goal
                      eng <- ask
                      return $ map ruleCondt rs 

bwdProveGoals :: [Fact] -> InfState ()
bwdProveGoals = sequence_ . map bwdMode

bwdProveSubGoals :: [[Fact]] -> InfState ()
bwdProveSubGoals = msum . map bwdProveGoals

bwdMode :: Fact -> InfState ()
bwdMode goal = do (wm, c) <- get
                  liftIO $ do putStrLn $ "Backward Mode."
                              putStrLn $ "Proving " ++ show goal ++ ";"
                              putStr "\n"
                  if hasFact wm goal
                    then liftIO $ putStrLn $ show goal ++ " has been found in working memory. Proved. Exit.\n"
                    else do cnfRs <- bwdConflict goal
                            liftIO $ do putStrLn "Rules to achive goal:"
                                        printRules cnfRs
                                        putStr "\n"
                            let subGs = map ruleCondt cnfRs
                            liftIO $ do putStrLn "Subgoals:"
                                        printSubGoals subGs
                                        putStr "\n"
                                        
                            when (null subGs) $
                              liftIO $ putStrLn "No subgoals to prove found. Abort."
                              
                            bwdProveSubGoals subGs
                            liftIO $ do putStrLn $ show goal ++ " has been proven by subgoals:"
                                        printSubGoals subGs
                                        putStrLn "\nExit backward mode."

runBwdMode :: WorkMem -> Engine -> Fact -> IO (Maybe (), (WorkMem, CycleCounter))
runBwdMode wm eng goal = runStateT (runReaderT (runMaybeT (bwdMode goal)) eng) (wm, 1)

printSubGoals [] = putStrLn "-- \\\\ --"
printSubGoals gs = sequence_ $ map printFacts gs

--------------------------------------------------------------
-- auxiliary class for casting `Int`s newtypes
class IntLike n where
  toInt :: n -> Int
  
instance IntLike Recency where
  toInt (Recency r) = r
  
instance IntLike Concr where
  toInt (Concr c) = c
  
instance IntLike RuleId where
  toInt (RuleId id) = id
  

{- Examples -}
    
exmRules =
  [ [Fact "Animal can sweam", Fact "Animal is big", Fact "Animal is mammal"] :=> Fact "Animal is whale"
  , [Fact "Animal can sweam", Fact "Animal is bird"] :=> Fact "Animal is penguin"
  , [Fact "Animal can walk", Fact "Animal has fur", Fact "Animal is big", Fact "Animal is mammal"] :=> Fact "Object is bear"
  , [Fact "Animal can walk", Fact "Animal can talk"] :=> Fact "Animal is human"
  , [Fact "Animal can walk"] :=> Fact "Animal is on land" ]
  
exmFacts = [Fact "Animal can sweam", Fact "Animal is bird"]

exmWM  = initWorkMem exmFacts
exmENG = initEngine exmRules
