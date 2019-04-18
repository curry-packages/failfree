-----------------------------------------------------------------------------
--- A simplifier for type-annotated FlatCurry programs.
--- In particular, it replaces calls to Eq.== implementations by Prelude.==
---
--- @author  Michael Hanus
--- @version April 2019
---------------------------------------------------------------------------

module SimpFlatCurry where

import List ( find, isPrefixOf )

-- Imports from dependencies:
import FlatCurry.Annotated.Goodies
import FlatCurry.Annotated.Types
import FlatCurry.Types

import TypedFlatCurryGoodies

----------------------------------------------------------------------------

simpProg :: TAProg -> TAProg
simpProg = updProgExps simpExpr

--- Implements the following transformations:
--- * simplify equality instance on lists
--- * simplify EQ.== calls
--- * simplify uses of otherwise:
---       case otherwise of { True -> e1 ; False -> e2 } ==> e1
--- * simplify application of `Prelude.$`:
---       f $ e ==> f e
simpExpr :: TAExpr -> TAExpr
simpExpr exp = case exp of
  AVar   _ _ -> exp
  ALit   _ _ -> exp
  AComb  ty ct (qf,qt) args -> simpComb ty ct (qf,qt) (map simpExpr args)
  ALet   ty bs e -> ALet ty (map (\ (v,b) -> (v, simpExpr b)) bs) (simpExpr e)
  AOr    ty e1 e2  -> AOr ty (simpExpr e1) (simpExpr e2)
  ACase  ty ct e brs -> if isOtherwise e
                          then simpExpr (trueBranch brs)
                          else ACase ty ct (simpExpr e) (map simpBranch brs)
  ATyped ty e te -> ATyped ty (simpExpr e) te
  AFree  ty vs e -> AFree  ty vs (simpExpr e)
 where
  simpComb ty ct (qf, qt) args
   -- simplify application of `Prelude.$`:
   | qf == pre "$" && length args == 2
   = case head args of
       AComb _ (FuncPartCall n) qft1 fargs ->
            AComb ty (if n==1 then FuncCall else FuncPartCall (n-1)) qft1
                  (fargs ++ [args!!1])
       _ -> AComb  ty ct (qf,qt) args
   -- simplify equality instance on lists:
   | ct == FuncCall && qf == pre "_impl#==#Prelude.Eq#[]"
   = AComb ty ct (pre "==", dropArgTypes 1 qt {- TODO: remove first type arg -} )
                 (tail args)
   -- simplify equal class calls:
   | otherwise
   = simpArithExp (simpClassEq (AComb ty ct (qf,qt) args))

  simpBranch (ABranch p e) = ABranch p (simpExpr e)

  isOtherwise e = case e of AComb _ _ (qf,_) _ -> qf == pre "otherwise"
                            _ -> False

  trueBranch brs =
    maybe (error "simpExpr: Branch with True pattern does not exist!")
          (\ (ABranch _ e) -> e)
          (find (\ (ABranch p _) -> isTruePattern p) brs)

  isTruePattern p = case p of APattern _ (qf,_) [] -> qf == pre "True"
                              _ -> False

simpClassEq :: TAExpr -> TAExpr
simpClassEq exp = case exp of
  AComb ty FuncCall (qt1,_)
        [AComb _ FuncCall (qt2,_)
          [AComb _ FuncCall (qt3,eqty) [_], e1], e2]
   | qt1 == pre "apply" && qt2 == pre "apply" && qt3 == pre "=="
   -> AComb ty FuncCall (pre "==", dropArgTypes 1 eqty) [e1,e2]
  _ -> exp

--- Simplify arithmetic expressions, i.e.,
---     apply (apply op e1) e2 ==> op [e1,e2]
simpArithExp :: TAExpr -> TAExpr
simpArithExp exp = case exp of
  AComb ty FuncCall (qt1,_)
        [AComb _ FuncCall (qt2,_)
          [AComb _ FuncCall ((mn,fn),opty) [], e1], e2]
   | qt1 == pre "apply" && qt2 == pre "apply" && mn == "Prelude"
   -> maybe exp
            (\_ -> AComb ty FuncCall ((mn,fn), dropArgTypes 1 opty) [e1,e2])
            (lookup fn arithPrimOps)
  _ -> exp

----------------------------------------------------------------------------
