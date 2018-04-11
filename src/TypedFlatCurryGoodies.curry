-----------------------------------------------------------------------------
--- Some goodies to deal with type-annotated FlatCurry programs.
---
--- @author  Michael Hanus
--- @version September 2017
---------------------------------------------------------------------------

module TypedFlatCurryGoodies where

import FlatCurry.Files
import IOExts
import List         ( find, nub )
import Maybe        ( fromJust )
import Pretty       ( pPrint )
import System       ( exitWith )

-- Imports from dependencies:
--import FlatCurry.Annotated.Files   ( readTypedFlatCurry )
import FlatCurry.Annotated.Goodies
import FlatCurry.Annotated.Pretty        ( ppExp )
import FlatCurry.Annotated.Types
import FlatCurry.Annotated.TypeInference ( inferProg )

import VerificationState

-- Type synomyms for type-annotated FlatCurry entities:
type TAProg       = AProg       TypeExpr
type TAFuncDecl   = AFuncDecl   TypeExpr
type TARule       = ARule       TypeExpr
type TAExpr       = AExpr       TypeExpr
type TABranchExpr = ABranchExpr TypeExpr
type TAPattern    = APattern    TypeExpr

----------------------------------------------------------------------------
--- Reads a type FlatCurry program or exit with a failure message
--- in case of some typing error.
readTypedFlatCurry :: String -> IO TAProg
readTypedFlatCurry mname = do
  prog <- readFlatCurry mname
  inferProg prog >>=
    either (\e -> putStrLn ("Error during FlatCurry type inference:\n" ++ e) >>
                  exitWith 1)
           return

----------------------------------------------------------------------------
--- Extract all user-defined typed FlatCurry functions that might be called
--- by a given list of functions.
getAllFunctions :: IORef VState -> [TAFuncDecl] -> [QName]
                -> IO [TAFuncDecl]
getAllFunctions vstref currfuns newfuns = do
  currmods <- readIORef vstref >>= return . currTAProgs
  getAllFunctions' currfuns currmods newfuns
 where
  getAllFunctions' currfuncs _ [] = return (reverse currfuncs)
  getAllFunctions' currfuncs currmods (newfun:newfuncs)
    | newfun `elem` standardConstructors ++ map funcName currfuncs
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
ppTAExpr e = pPrint (ppExp e)

----------------------------------------------------------------------------
--- Is a qualified FlatCurry name primitive?
isPrimOp :: QName -> Bool
isPrimOp (mn,fn) = mn=="Prelude" && fn `elem` map fst preludePrimOps

--- Primitive operations of the prelude and their SMT names.
preludePrimOps :: [(String,String)]
preludePrimOps =
  [("==","=")
  ,("+","+")
  ,("-","-")
  ,("negate","-")
  ,("*","*")
  ,("div","div")
  ,("mod","mod")
  ,("rem","rem")
  ,(">",">")
  ,(">=",">=")
  ,("<","<")
  ,("<=","<=")
  ,("not","not")
  ,("&&","and")
  ,("||","or")
  ,("apply","") -- SMT name not used
  ]

--- Primitive constructors from the prelude and their SMT names.
primCons :: [(String,String)]
primCons =
  [("True","true")
  ,("False","false")
  ,("[]","nil")
  ,(":","insert")
  ]

-- Some standard constructors from the prelude.
standardConstructors :: [QName]
standardConstructors =
  map (pre . fst) primCons ++ [pre "()", pre "(,)", pre "(,,)"]

----------------------------------------------------------------------------

pre :: String -> QName
pre f = ("Prelude",f)

showQName :: QName -> String
showQName (mn,fn) = mn ++ "." ++ fn

----------------------------------------------------------------------------
