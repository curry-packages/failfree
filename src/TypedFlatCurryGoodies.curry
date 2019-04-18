-----------------------------------------------------------------------------
--- Some goodies to deal with type-annotated FlatCurry programs.
---
--- @author  Michael Hanus
--- @version April 2019
---------------------------------------------------------------------------

module TypedFlatCurryGoodies where

import Directory    ( doesFileExist )
import FilePath     ( (</>) )
import IOExts
import List         ( find, maximum, nub, union )
import Maybe        ( fromJust )
import System       ( exitWith )

-- Imports from dependencies:
import Data.FiniteMap
import FlatCurry.Annotated.Files         ( readTypedFlatCurry )
import FlatCurry.Annotated.Goodies
import FlatCurry.Annotated.Pretty        ( ppExp )
import FlatCurry.Annotated.Types
import FlatCurry.Annotated.TypeSubst
import System.CurryPath ( getLoadPathForModule, lookupModuleSource
                        , stripCurrySuffix )
import Text.Pretty      ( showWidth )

import PackageConfig ( packagePath )
import ToolOptions
import VerifierState

-- Type synomyms for type-annotated FlatCurry entities:
type TAProg       = AProg       TypeExpr
type TAFuncDecl   = AFuncDecl   TypeExpr
type TARule       = ARule       TypeExpr
type TAExpr       = AExpr       TypeExpr
type TABranchExpr = ABranchExpr TypeExpr
type TAPattern    = APattern    TypeExpr

----------------------------------------------------------------------------
--- Reads a typed FlatCurry program together with a possible `_SPEC` program
--- (containing further contracts) or exits with a failure message
--- in case of some typing error.
readTypedFlatCurryWithSpec :: Options -> String -> IO TAProg
readTypedFlatCurryWithSpec opts mname = do
  whenStatus opts $ putStr $
    "Loading typed FlatCurry program '" ++ mname ++ "'..."
  prog     <- readTypedFlatCurry mname
  loadpath <- getLoadPathForModule specName
  mbspec   <- lookupModuleSource (loadpath ++ [packagePath </> "include"])
                                 specName
  maybe ( whenStatus opts (putStrLn "done") >> return prog )
        (\ (_,specname) -> do
           let specpath = stripCurrySuffix specname
           when (optVerb opts > 0) $ putStr $
             "'" ++ (if optVerb opts > 1 then specpath else specName) ++ "'..."
           specprog <- readTypedFlatCurry specpath
           whenStatus opts $ putStrLn "done"
           return (unionTAProg prog (rnmProg mname specprog))
        )
        mbspec
 where
  specName = mname ++ "_SPEC"

--- Returns the union of two typed FlatCurry programs.
unionTAProg :: TAProg -> TAProg -> TAProg
unionTAProg (AProg name imps1 types1 funcs1 ops1)
            (AProg _    imps2 types2 funcs2 ops2) =
  AProg name (filter (/=name) (union imps1 imps2))
        (types1++types2) (funcs1++funcs2) (ops1++ops2)

----------------------------------------------------------------------------
--- Extract all user-defined typed FlatCurry functions that might be called
--- by a given list of functions.
getAllFunctions :: IORef VState -> [TAFuncDecl] -> [QName] -> IO [TAFuncDecl]
getAllFunctions vstref currfuncs newfuns = do
  currmods <- readIORef vstref >>= return . currTAProgs
  getAllFuncs currmods newfuns
 where
  getAllFuncs _ [] = return (reverse currfuncs)
  getAllFuncs currmods (newfun:newfuncs)
    | newfun `elem` map (pre . fst) transPrimCons ++ map funcName currfuncs
      || isPrimOp newfun
    = getAllFunctions vstref currfuncs newfuncs
    | fst newfun `elem` map progName currmods
    = maybe
        (-- if we don't find the qname, it must be a constructor:
         getAllFunctions vstref currfuncs newfuncs)
        (\fdecl -> getAllFunctions vstref
                      (fdecl : currfuncs)
                      (newfuncs ++ nub (funcsOfFuncDecl fdecl)))
        (find (\fd -> funcName fd == newfun)
              (progFuncs
                 (fromJust (find (\m -> progName m == fst newfun) currmods))))
    | otherwise -- we must load a new module
    = do let mname = fst newfun
         putStrLn $ "Loading module '" ++ mname ++ "' for '"++ snd newfun ++"'"
         newmod <- readTypedFlatCurry mname
         modifyIORef vstref (addProgToState newmod)
         getAllFunctions vstref currfuncs (newfun:newfuncs)

--- Returns the names of all functions/constructors occurring in the
--- body of a function declaration.
funcsOfFuncDecl :: TAFuncDecl -> [QName]
funcsOfFuncDecl fd =
  nub (trRule (\_ _ e -> funcsOfExp e) (\_ _ -> []) (funcRule fd))
 where
  funcsOfExp = trExpr (\_ _ -> [])
                      (\_ _ -> [])
                      (\_ _ (qn,_) fs -> qn : concat fs)
                      (\_ bs fs -> concatMap snd bs ++ fs)
                      (\_ _ -> id)
                      (\_ -> (++))
                      (\_ _ fs fss -> concat (fs:fss))
                      (\_ -> id)
                      (\_ fs _ -> fs)

--- Returns `True` if the expression is non-deterministic,
--- i.e., if `Or` or `Free` occurs in the expression.
ndExpr :: TAExpr -> Bool
ndExpr = trExpr (\_ _ -> False)
                (\_ _ -> False)
                (\_ _ _ nds -> or nds)
                (\_ bs nd -> nd || any snd bs)
                (\_ _ _ -> True)
                (\_ _ _ -> True)
                (\_ _ nd bs -> nd || or bs)
                (\_ -> id)
                (\_ nd _ -> nd)

--- Pretty prints an expression.
ppTAExpr :: TAExpr -> String
ppTAExpr e = showWidth 200 (ppExp e)

--- Sets the top annotation of a pattern.
setAnnPattern :: TypeExpr -> TAPattern -> TAPattern
setAnnPattern ann (ALPattern _ lit) = ALPattern ann lit
setAnnPattern ann (APattern _ aqn vars) = APattern ann aqn vars

----------------------------------------------------------------------------
--- Is a qualified FlatCurry name primitive?
isPrimOp :: QName -> Bool
isPrimOp (mn,fn) = mn=="Prelude" && fn `elem` map fst preludePrimOps

--- Primitive operations of the prelude and their SMT names.
preludePrimOps :: [(String,String)]
preludePrimOps = arithPrimOps ++
  [("not","not")
  ,("&&","and")
  ,("||","or")
  ,("otherwise","true")
  ,("apply","apply") -- TODO...
  ]

--- Primitive arithmetic operations of the prelude and their SMT names.
arithPrimOps :: [(String,String)]
arithPrimOps =
  [("==","=")
  ,("_impl#==#Prelude.Eq#Prelude.Int","=")
  ,("_impl#==#Prelude.Eq#Prelude.Char","=")
  ,("/=","/=")  -- will be translated as negated '='
  ,("_impl#/=#Prelude.Eq#Prelude.Int","/=")
  ,("_impl#/=#Prelude.Eq#Prelude.Char","/=")
  ,("_impl#+#Prelude.Num#Prelude.Int","+")
  ,("_impl#-#Prelude.Num#Prelude.Int","-")
  ,("_impl#*#Prelude.Num#Prelude.Int","*")
  ,("_impl#negate#Prelude.Num#Prelude.Int","-")
  ,("_impl#div#Prelude.Integral#Prelude.Int","div")
  ,("_impl#mod#Prelude.Integral#Prelude.Int","mod")
  ,("_impl#rem#Prelude.Integral#Prelude.Int","rem")
  ,("_impl#>#Prelude.Ord#Prelude.Int",">")
  ,("_impl#<#Prelude.Ord#Prelude.Int","<")
  ,("_impl#>=#Prelude.Ord#Prelude.Int",">=")
  ,("_impl#<=#Prelude.Ord#Prelude.Int","<=")
  ,("_impl#>#Prelude.Ord#Prelude.Float",">")
  ,("_impl#<#Prelude.Ord#Prelude.Float","<")
  ,("_impl#>=#Prelude.Ord#Prelude.Float",">=")
  ,("_impl#<=#Prelude.Ord#Prelude.Float","<=")
  ,("_impl#>#Prelude.Ord#Prelude.Char",">")
  ,("_impl#<#Prelude.Ord#Prelude.Char","<")
  ,("_impl#>=#Prelude.Ord#Prelude.Char",">=")
  ,("_impl#<=#Prelude.Ord#Prelude.Char","<=")
  ]

--- Some primitive constructors from the prelude and their SMT names.
transPrimCons :: [(String,String)]
transPrimCons =
  [("True","true")
  ,("False","false")
  ,("[]","nil")
  ,(":","insert")
  ,("()","unit")
  ,("(,)","mk-pair")
  ,("LT","LT")
  ,("EQ","EQ")
  ,("GT","GT")
  ,("Nothing","Nothing")
  ,("Just","Just")
  ,("Left","Left")
  ,("Right","Right")
  ] ++
  map (\i -> ('(' : take (i-1) (repeat ',') ++ ")", "Tuple" ++ show i)) [3..15]

----------------------------------------------------------------------------
--- Eta-expansion of user-defined function declarations.
etaExpandFuncDecl :: TAFuncDecl -> TAFuncDecl
etaExpandFuncDecl fdecl@(AFunc _ _ _ _ (AExternal _ _)) = fdecl
etaExpandFuncDecl (AFunc qn ar vis texp (ARule tr args rhs)) =
  AFunc qn (ar + length etavars) vis texp
        (ARule tr (args ++ etavars)
               (applyExp rhs (map (\ (v,t) -> AVar t v) etavars)))
 where
  freshvar = maximum (0 : map fst args ++ allVars rhs) + 1
  argtypes = argTypes texp
  etavars  = zip [freshvar ..] (drop ar argtypes)

--- Apply arguments to a given FlatCurry expression by transforming
--- this expression whenever possible.
applyExp :: TAExpr -> [TAExpr] -> TAExpr
applyExp exp [] = exp
applyExp exp vars@(v1:vs) = case exp of
  AComb te ct (qf,qt) cargs -> case ct of
    FuncPartCall m -> applyExp (AComb (dropArgTypes 1 te)
                                      (if m==1 then FuncCall
                                               else FuncPartCall (m-1))
                                      (qf,qt) 
                                      (cargs ++ [v1]))
                               vs
    _ -> applyExp (AComb (dropArgTypes 1 te) FuncCall
                         (pre "apply", FuncType (annExpr v1) te) [exp, v1]) vs
  ACase  te ct e brs -> ACase (adjustType te) ct e
                 (map (\ (ABranch p be) -> ABranch p (applyExp be vars)) brs)
  AOr    te e1 e2 -> AOr (adjustType te) (applyExp e1 vars) (applyExp e2 vars)
  ALet   te bs e  -> ALet   (adjustType te) bs (applyExp e vars)
  AFree  te fvs e -> AFree  (adjustType te) fvs (applyExp e vars)
  ATyped te e ty  -> ATyped (adjustType te) (applyExp e vars) (adjustType ty)
  AVar   te _     -> applyExp (AComb (dropArgTypes 1 te) FuncCall
                                     (pre "apply", FuncType (annExpr v1) te)
                                     [exp, v1]) vs
  ALit   _  _     -> error "etaExpandFuncDecl: cannot apply literal"
 where
  adjustType ty = dropArgTypes (length vars) ty 

--- Remove the given number of argument types from a (nested) functional type.
dropArgTypes :: Int -> TypeExpr -> TypeExpr
dropArgTypes n ty
  | n==0      = ty
  | otherwise = case ty of FuncType _ rt -> dropArgTypes (n-1) rt
                           _ -> error "dropArgTypes: too few argument types"

----------------------------------------------------------------------------
--- Is the type expression a base type?
isBaseType :: TypeExpr -> Bool
isBaseType (TVar _)         = False
isBaseType (TCons _ targs)  = null targs
isBaseType (FuncType _ _)   = False
isBaseType (ForallType _ _) = False

----------------------------------------------------------------------------
--- Compute type matching, i.e., if `matchType t1 t2 = s`, then `t2 = s(t1)`.
matchType :: TypeExpr -> TypeExpr -> Maybe AFCSubst
matchType t1 t2 = case (t1,t2) of
  (TVar v        , _) -> Just $ if t1 == t2 then emptyAFCSubst
                                            else addToFM emptyAFCSubst v t2
  (TCons tc1 ts1 , TCons tc2 ts2) | tc1 == tc2 -> matchTypes ts1 ts2
  (FuncType a1 r1, FuncType a2 r2) -> matchTypes [a1,r1] [a2,r2]
  (ForallType _ _, _) -> error "matchType: ForallType occurred"
  (_, ForallType _ _) -> error "matchType: ForallType occurred"
  _ -> Nothing

matchTypes :: [TypeExpr] -> [TypeExpr] -> Maybe AFCSubst
matchTypes []       []       = Just emptyAFCSubst
matchTypes []       (_:_)    = Nothing
matchTypes (_:_)    []       = Nothing
matchTypes (t1:ts1) (t2:ts2) = do
  s <- matchType t1 t2
  t <- matchTypes (map (subst s) ts1)(map (subst s) ts2)
  return (plusFM s t)

----------------------------------------------------------------------------
--- Transform name into Prelude-qualified name.
pre :: String -> QName
pre f = ("Prelude",f)

----------------------------------------------------------------------------
