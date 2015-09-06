{-# LANGUAGE GADTs #-}

import qualified Data.Set as DS 
import qualified Data.Map as DM
import qualified Data.Vector as DV

import Control.Monad.State
import Control.Monad.Trans.Maybe

import Data.Maybe


-- Looks like it's possible to use strings as facts.
-- There is no need in predicates for reasoning. 
newtype Fact = Fact { factToString :: String }
  deriving (Eq, Ord)
-- Fact's recency data
newtype Recency = Recency { recencyToInt :: Int } -- +1 to current time step  
type FactRecency = DM.Map Fact Recency
  
-- Production's concreteness
newtype Concr = Concr { concrToInt :: Int } -- number of production's conditions
-- Production's priority
newtype Prio = Prio { prioToInt :: Int } -- value to set up by expert
-- Production's successful usage value when proving some goal (usefulness)
newtype Usef = Usef { usefToInt :: Int } -- number of successful usages

-- ID of production
type ProdID = Int

-- Actions
data Action = Assert [Fact] -- adds list of facts to a working memory
            | Terminate     -- terminates inferring
            deriving (Eq, Ord)

type Goal = [Action]
  
-- Data about successful usage of production when proving some goal
type ProdUsef = DM.Map (ProdID, Goal) Usef

-- Data about production's concretness
type ProdConcr   = DV.Vector Concr
-- Data about production's priority
type ProdPrio    = DV.Vector Prio
-- Data about production's conditions recency
type ProdRecency = DV.Vector Recency
  
-- Productions manager. Keeps all data about productions.
-- Can solve what production to apply.
data ProdManager = ProdManager Int ProdConcr ProdPrio ProdRecency ProdUsef

-- Combines Usef Concr Prio and Recency into score
combine :: Concr -> Prio -> Recency -> Usef -> Int
combine (Concr c) (Prio p) (Recency r) (Usef u) =
  c + p + r + u

resolve :: ProdManager -> Goal -> ProdID
resolve (ProdManager n pc pp pr pu) goal =
  -- getting scores of productions
  let scores = DV.generate n
        (\ pId -> combine (pc DV.! pId)
                          (pp DV.! pId)
                          (pr DV.! pId)
                          (puVec DV.! pId))
                            in DV.maxIndex scores 
  where
    -- Convertion of map `pu` into vector
    puVec = DV.fromListN n $ map
      (\ pId -> case DM.lookup (pId, goal) pu of
                  Just a  -> a
                  Nothing -> Usef 0) [1..n]

initManager :: FactRecency -> ProdUsef 

  
data WorkMemElem =
  WMElem { fact     :: Fact
         , recency  :: Int
         , priority :: Int }

