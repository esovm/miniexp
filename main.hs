
-- This modules will be necessery later --
import qualified Data.Map as DM
import qualified Data.Set as DS
import qualified Data.Vector as DV

import Data.List
import Data.Maybe
import Data.Ord

import Debug.Trace

import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Reader

import Control.Applicative
-- -- -- -- -- -- -- -- -- -- -- -- -- --*

{-

  Best recomendation for any project and for this one
  especially:
  
    KEEP IT SIMPLE STUPID

                        ~ KISS

-}

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
    
    5) Order in which rules are applied is following:
    most concrete and most recent rules are preffered.
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
         , engFact2Ids :: DM.Map Fact (DS.Set RuleId)
         , engRule2Id  :: DM.Map Rule RuleId }

--
id2Rule :: Engine -> RuleId -> Rule
id2Rule eng rId = (engId2Rule eng) DV.! (toInt rId)

--
id2Concr :: Engine -> RuleId -> Concr
id2Concr eng rId = (engId2Concr eng) DV.! (toInt rId)

--
fact2ids :: Engine -> Fact -> DS.Set RuleId
fact2ids eng f = (engFact2Ids eng) DM.! f

lookupIdsByFact :: Engine -> Fact -> Maybe (DS.Set RuleId)
lookupIdsByFact eng f = DM.lookup f (engFact2Ids eng)

--
rule2id :: Engine -> Rule -> RuleId
rule2id eng r = (engRule2Id eng) DM.! r

initEngine :: [Rule] -> Engine
initEngine rs = let
  size = length rs
  i2r  = DV.fromListN size rs
  i2c  = DV.fromListN size $ map ruleConcr rs
  f2is = initFact2Ids
  r2i  = DM.fromList idxRs
  in Engine i2r i2c f2is r2i
  where
    
    idxRs = zip rs $ map RuleId [0..] 
    
    initFact2Ids =
      let idxFs = map (\ (r, i) -> (ruleCondt r, i)) idxRs
        in foldl insertCondt DM.empty idxFs
        where
          insertCondt f2is (condt, id) =
            let idS = DS.singleton id in
              foldl (\ f2is f -> DM.insertWith DS.union f idS f2is) f2is condt 
       
printEngine :: Engine -> IO ()
printEngine (Engine i2r i2c f2is r2i) =
  do putStrLn "Inferrence engine\n"
     putStrLn ("Rules:\n" ++ show i2r)
     putStrLn ("Rule's concretenesses:\n" ++ show i2c)
     putStrLn ("Facts and related rules (by id):\n" ++ show f2is)
     putStrLn ("Rule's ids:\n" ++ show r2i) 
        
{- Working memory -}

-- Recency
newtype Recency = Recency Int
  deriving Show

-- Working memory
newtype WorkMem =
  WorkMem { wmFact2Recency :: DM.Map Fact Recency }
  
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
--relatedRules :: WorkMem -> Engine -> DS.Set RuleId
relatedRules wm eng = DS.unions $ catMaybes $
  workMemFacts wm >>= pure . lookupIdsByFact eng
  
  
  
-- Sorts rules in descending order by comparing
-- a sum of rule's recency and concreteness.
-- Most concrete and recent rule comes first.
sortRules :: WorkMem -> Engine -> [RuleId] -> [RuleId]
sortRules wm eng rIds= map fst $ sortDesc $ zip rIds $ map getScore rIds
  where 
  
    sortDesc = sortBy (flip $ comparing snd)
 
    getScore id = sum $
      [toInt . id2Concr eng, toInt . ruleRecency wm eng] <*> [id]
    
-- Tries to apply rule (by id). If possible,
-- returns a Working Memory without rule's
-- condition.
tryApply :: WorkMem -> Engine -> RuleId -> Maybe (RuleId, Rule, WorkMem)
tryApply (WorkMem f2r) eng rId =
  let r    = id2Rule eng rId
      cnd  = ruleCondt r
      f2rs = removeCnd cnd
      in case span isJust f2rs of
           (js, []) -> fmap (\ x -> (rId, r, WorkMem x)) $ head js
           _        -> Nothing
  where
  
    del _ _ = Nothing
    
    removeCnd = scanr (\ f mF2r ->
                  do f2r <- mF2r
                     case DM.updateLookupWithKey del f f2r of
                       (Nothing, _)   -> Nothing
                       (Just _, f2r') -> return f2r') (Just f2r)
    
    
firstApplicable :: WorkMem -> Engine -> [RuleId] -> Maybe (RuleId, Rule, WorkMem)
firstApplicable wm eng = msum . map (tryApply wm eng)

-- Forward Inferrence mode --

type CycleCounter = Int

type InfState r = MaybeT (ReaderT Engine (StateT (WorkMem, CycleCounter) IO)) r

toInfState :: Maybe a -> InfState a
toInfState = MaybeT . return

fwdMode :: InfState ()
fwdMode = do eng     <- ask
             (wm, c) <- get
             liftIO $ putStrLn $ "Forward Mode. Step " ++ show c ++ ";\n"
             
             let relRs = DS.toList $ relatedRules wm eng
                 srtRs = sortRules wm eng relRs
             liftIO $ putStrLn "Related Rules (ordered):"
             liftIO $ printRules $ map (id2Rule eng) srtRs
             liftIO $ putStrLn ""
             
             (rId, r,  wm') <- toInfState $ firstApplicable wm eng srtRs
             liftIO $ putStrLn $ "Firing Rule:"
             liftIO $ printRule r
             liftIO $ putStrLn ""
             
             let wm'' = WorkMem $ DM.insert (ruleConcl r) (Recency c) $ wmFact2Recency wm'
             liftIO $ putStrLn $ "Working Memory:"
             liftIO $ printWorkMem wm''
             liftIO $ putStrLn "\n"
             
             put (wm'', c + 1)
             fwdMode
         
runFwdMode :: WorkMem -> Engine -> IO (WorkMem, CycleCounter)
runFwdMode wm eng = fmap snd $ runStateT (runReaderT (runMaybeT fwdMode) eng) (wm, 1)


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
showWorkMem = intercalate ";\n" . map (\ (f, r) -> show f ++ "; " ++ show r) . DM.toList . wmFact2Recency

printWorkMem = putStrLn . showWorkMem
printRules   = putStrLn . showRules
printRule    = putStrLn . showRule
    
--------------------------------------------------------------
{- Backward inferrence mode -}



--------------------------------------------------------------
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
  
exmFacts = [Fact "Animal can walk", Fact "Animal is mammal"]

exmWM  = initWorkMem exmFacts
exmENG = initEngine exmRules
