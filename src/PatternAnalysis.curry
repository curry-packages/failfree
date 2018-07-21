--- Pattern completeness analysis for Curry programs.
---
--- @author Michael Hanus
--- @version April 2018
-----------------------------------------------------------------------------

module PatternAnalysis where

import Data.List               (delete)

import Analysis.ProgInfo
import Analysis.Types
import Analysis.TotallyDefined ( siblingCons )
import FlatCurry.Types

------------------------------------------------------------------------------
-- The completeness analysis assigns to an operation a flag indicating
-- whether this operation is completely defined on its input types,
-- i.e., reducible for all ground data terms for all non-deterministic
-- computation branches.

-- The possible outcomes of the completeness analysis:
data Completeness =
     Complete       -- completely defined
   | InComplete     -- incompletely defined

------------------------------------------------------------------------------
--- Pattern completeness analysis

-- Shows the result of the completeness analysis.
showComplete :: AOutFormat -> Completeness -> String
showComplete AText Complete     = "complete"
showComplete ANote Complete     = ""
showComplete _     InComplete   = "incomplete"


analysePatternComplete :: ProgInfo [(QName,Int)] -> FuncDecl -> Completeness
analysePatternComplete consinfo fdecl = anaFun fdecl
 where
  anaFun (Func _ _ _ _ (Rule _ e)) = isComplete consinfo e
  anaFun (Func _ _ _ _ (External _)) = Complete

isComplete :: ProgInfo [(QName,Int)] -> Expr -> Completeness
isComplete _ (Var _)      = Complete
isComplete _ (Lit _)      = Complete
isComplete consinfo (Comb _ f es) =
  if f==("Prelude","commit") && length es == 1
  then isComplete consinfo (head es)
  else Complete
isComplete _ (Free _ _) = Complete
isComplete _ (Let _ _) = Complete
isComplete consinfo (Or e1 e2) =
   combineAndResults (isComplete consinfo e1) (isComplete consinfo e2)
-- if there is no branch, it is incomplete:
isComplete _ (Case _ _ []) = InComplete
-- for literal branches we assume that not all alternatives are provided:
isComplete _ (Case _ _ (Branch (LPattern _)   _ : _)) = InComplete
isComplete consinfo (Case _ _ (Branch (Pattern cons _) bexp : ces)) =
    combineAndResults
      (checkAllCons (maybe [] (map fst) (lookupProgInfo cons consinfo)) ces)
      (isComplete consinfo bexp)
  where
   -- check for occurrences of all constructors in each case branch:
   checkAllCons []    _  = Complete
   checkAllCons (_:_) [] = InComplete
   checkAllCons (_:_) (Branch (LPattern _)   _ : _) = InComplete -- should not occur
   checkAllCons (c:cs) (Branch (Pattern i _) e : ps) =
     combineAndResults (checkAllCons (delete i (c:cs)) ps)
                       (isComplete consinfo e)
isComplete consinfo (Typed e _) = isComplete consinfo e

-- Combines the completeness results in different branches.
combineAndResults :: Completeness -> Completeness -> Completeness
combineAndResults Complete     Complete     = Complete
combineAndResults Complete     InComplete   = InComplete
combineAndResults InComplete   _            = InComplete
