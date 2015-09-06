{-# LANGUAGE GADTs #-}

import qualified Data.Set as DS 
import qualified Data.Map as DM

import Control.Monad.State
import Control.Monad.Trans.Maybe

import Data.Maybe



type Object = String
  
data Fact = Fact String [Object]
  deriving (Eq, Ord, Show)

fact2atom :: Fact -> Formula
fact2atom (Fact x y) = Atom x y

data Formula = Atom String [Object] | And Formula Formula | Or Formula Formula
  deriving (Eq, Ord, Show)

type Antecedent = Formula
type Succedent  = Fact
data Rule = Antecedent :=> Succedent
  deriving (Eq, Ord)
  
ruleAnt (ant :=> _) = ant
ruleSuc (_ :=> suc) = suc

formula2facts :: Formula -> [Fact]
formula2facts (Atom name args) = [Fact name args]
formula2facts (And a b) = [a, b] >>= formula2facts
formula2facts (Or  a b) = [a, b] >>= formula2facts


type Fact2Rules = DM.Map Fact [Rule]

addRule :: Rule -> Fact2Rules -> Fact2Rules
addRule r f2r = insertKeyNodes f2r [r] $ formula2facts $ ruleAnt r 
  where  
    insertKeyNodes m v = foldl (\ m k -> DM.insertWith (++) k v m) m

relatedRules :: Fact2Rules -> [Fact] -> [Rule]
relatedRules f2r = catMaybes . map (lookupRule f2r) 
  where
    lookupRule m f = fmap head $ DM.lookup f m



