-----------------------------------------------------------------------------
--- A tool to verify non-failure properties of Curry operations.
---
--- @author  Michael Hanus
--- @version November 2025
---------------------------------------------------------------------------

module Main where

import Control.Monad      ( unless, when )
import Data.IORef
import Data.List          ( (\\), elemIndex, find, maximum, minimum
                          , partition, union )
import Data.Maybe         ( catMaybes )
import System.Environment ( getArgs )

-- Imports from dependencies:
import Analysis.ProgInfo
import Analysis.TotallyDefined           ( siblingCons )
import Analysis.Types
import CASS.Server                       ( analyzeGeneric, analyzePublic )
import Contract.Names
import Contract.Usage                    ( checkContractUsage )
import Control.Monad.Trans.Class         ( lift )
import Control.Monad.Trans.State         ( StateT, get, put, evalStateT )
import Debug.Profile
import FlatCurry.TypeAnnotated.TypeSubst ( substRule )
import FlatCurry.Files                   ( readFlatCurryInt )
import FlatCurry.Types hiding ( pre )
import FlatCurry.Annotated.Goodies
import FlatCurry.ShowIntMod              ( showCurryModule )
import RW.Base                           ( ReadWrite )
import System.FilePath                   ( (</>) )
import System.IOExts                     ( evalCmd )
import System.Path                       ( fileInPath )
import System.Process                    ( exitWith )

-- Imports from package modules:
import ESMT
import Curry2SMT
import FlatCurry.Typed.Read
import FlatCurry.Typed.Goodies
import FlatCurry.Typed.Names
import FlatCurry.Typed.Types
import PackageConfig ( packagePath )
import ToolOptions
import VerifierState

------------------------------------------------------------------------
-- To support testing:

test :: Int -> String -> IO ()
test v = verifyNonFailingMod defaultOptions { optVerb = v }

testv :: String -> IO ()
testv = test 3

testcv :: String -> IO ()
testcv = verifyNonFailingMod defaultOptions { optVerb = 3, optContract = True }

------------------------------------------------------------------------

banner :: String
banner = unlines [bannerLine,bannerText,bannerLine]
 where
   bannerText = "Fail-Free Verification Tool for Curry (Version of 28/09/24)"
   bannerLine = take (length bannerText) (repeat '=')

---------------------------------------------------------------------------
main :: IO ()
main = do
  args <- getArgs
  (opts,progs) <- processOptions banner args
  let optname = optName opts
  if not (null optname)
    then putStrLn $ "Non-failure condition for '" ++ optname ++ "':\n" ++
                    encodeContractName (optname ++ "'nonfail")
    else do
      z3exists <- fileInPath "z3"
      if z3exists
        then do
          when (optVerb opts > 0) $ putStrLn banner
          verifyNonFailingModules opts [] progs
        else do
          putStrLn "NON-FAILING ANALYSIS SKIPPED:"
          putStrLn "The SMT solver Z3 is required for the verifier to work"
          putStrLn "but the program 'z3' is not found on the PATH!"
          exitWith 1

verifyNonFailingModules :: Options -> [String] -> [String] -> IO ()
verifyNonFailingModules _ _ [] = return ()
verifyNonFailingModules opts verifiedmods (mod:mods)
  | mod `elem` verifiedmods
  = verifyNonFailingModules opts verifiedmods mods
  | optRec opts
  = do (Prog _ imps _ _ _) <- readFlatCurryInt mod
       let newimps = filter (`notElem` verifiedmods) imps
       if null newimps
         then do printWhenStatus opts ""
                 verifyNonFailingMod opts mod
                 verifyNonFailingModules opts (mod:verifiedmods) mods
         else verifyNonFailingModules opts verifiedmods
                     (newimps ++ mod : (mods \\ newimps))
  | otherwise -- non-recursive
  = do verifyNonFailingMod opts mod
       verifyNonFailingModules opts (mod:verifiedmods) mods
  

verifyNonFailingMod :: Options -> String -> IO ()
verifyNonFailingMod opts modname = do
  printWhenStatus opts $ "Analyzing module '" ++ modname ++ "':"
  prog <- readSimpTypedFlatCurryWithSpec opts modname
  let errs = checkContractUsage (progName prog)
               (map (\fd -> (snd (funcName fd), funcType fd)) (progFuncs prog))
  unless (null errs) $ do
    putStr $ unlines (map showOpError errs)
    exitWith 1
  impprogs <- mapM (readSimpTypedFlatCurryWithSpec opts) (progImports prog)
  let allprogs = prog : impprogs
      vinfo  = foldr addFunsToVerifyInfo (initVerifyInfo opts)
                     (map progFuncs allprogs)
      vstate = foldr addProgToState (initVState vinfo) allprogs
  siblingconsinfo <- loadAnalysisWithImports siblingCons prog
  pi1 <- getProcessInfos
  printWhenAll opts $ unlines $
    ["ORIGINAL PROGRAM:", line, showCurryModule (unAnnProg prog), line]
  vstref <- newIORef vstate
  proveNonFailingFuncs opts siblingconsinfo vstref (progFuncs prog)
  stats <- readIORef vstref
  pi2 <- getProcessInfos
  let tdiff = maybe 0 id (lookup ElapsedTime pi2) -
              maybe 0 id (lookup ElapsedTime pi1)
  when (optTime opts) $ putStrLn $
    "TOTAL VERIFICATION TIME  : " ++ show tdiff ++ " msec"
  when (optVerb opts > 0 || not (isVerified stats)) $
    putStr (showStats stats)
 where
  line = take 78 (repeat '-')

  showOpError (qf,err) =
    snd qf ++ " (module " ++ fst qf ++ "): " ++ err

-- Loads CASS analysis results for a module and its imported entities.
loadAnalysisWithImports ::
  (Read a, Show a, ReadWrite a, Eq a) => Analysis a -> TAProg -> IO (ProgInfo a)
loadAnalysisWithImports analysis prog = do
  maininfo <- analyzeGeneric analysis (progName prog)
                >>= return . either id error
  impinfos <- mapM (\m -> analyzePublic analysis m >>=
                                                     return . either id error)
                    (progImports prog)
  return $ foldr combineProgInfo maininfo impinfos

---------------------------------------------------------------------------
-- The state of the transformation process contains
-- * the current assertion
-- * a fresh variable index
-- * a list of all introduced variables and their types:
data TransState = TransState
  { cAssertion :: Term
  , freshVar   :: Int
  , varTypes   :: [(Int,TypeExpr)]
  }

makeTransState :: Int -> [(Int,TypeExpr)] -> TransState
makeTransState = TransState tTrue

emptyTransState :: TransState
emptyTransState = makeTransState 0 []

-- The type of the state monad contains the transformation state.
--type TransStateM a = State TransState a
type TransStateM a = StateT TransState IO a

-- Gets the current fresh variable index of the state.
getFreshVarIndex :: TransStateM Int
getFreshVarIndex = get >>= return . freshVar

-- Sets the fresh variable index in the state.
setFreshVarIndex :: Int -> TransStateM ()
setFreshVarIndex fvi = do
  st <- get
  put $ st { freshVar = fvi }

-- Gets a fresh variable index and increment the index in the state.
getFreshVar :: TransStateM Int
getFreshVar = do
  st <- get
  put $ st { freshVar = freshVar st + 1 }
  return $ freshVar st

-- Increments fresh variable index.
incFreshVarIndex :: TransState -> TransState
incFreshVarIndex st = st { freshVar = freshVar st + 1 }

-- Gets the variables and their types stored in the state.
getVarTypes :: TransStateM [(Int,TypeExpr)]
getVarTypes = get >>= return . varTypes

-- Adds variables and their types to the state.
addVarTypes :: [(Int,TypeExpr)] -> TransStateM ()
addVarTypes vts = do
  st <- get
  put $ st { varTypes = vts ++ varTypes st }

-- Gets the current assertion stored in the state.
getAssertion :: TransStateM Term
getAssertion = get >>= return . cAssertion

-- Sets the current assertion in the state.
setAssertion :: Term -> TransStateM ()
setAssertion formula = do
  st <- get
  put $ st { cAssertion = formula }

-- Add a formula to the current assertion in the state by conjunction.
addToAssertion :: Term -> TransStateM ()
addToAssertion formula = do
  st <- get
  put $ st { cAssertion = tConj [cAssertion st, formula] }

---------------------------------------------------------------------------
-- Prove that a list of defined functions is fail free (w.r.t. their
-- non-fail conditions).
proveNonFailingFuncs :: Options -> ProgInfo [(QName,Int)] -> IORef VState
                     -> [TAFuncDecl] -> IO ()
proveNonFailingFuncs opts siblingconsinfo vstref =
  mapM_ (proveNonFailingFunc opts siblingconsinfo vstref)

-- Prove that a function is fail free (w.r.t. their non-fail condition).
proveNonFailingFunc :: Options -> ProgInfo [(QName,Int)] -> IORef VState
                    -> TAFuncDecl -> IO ()
proveNonFailingFunc opts siblingconsinfo vstref fdecl =
  unless (isContractOp (funcName fdecl) || isProperty fdecl) $ do
    printWhenIntermediate opts $
      "Operation to be analyzed: " ++ snd (funcName fdecl)
    modifyIORef vstref incNumAllInStats
    let efdecl = etaExpandFuncDecl fdecl
    proveNonFailingRule opts siblingconsinfo vstref
                        (funcName efdecl) (funcType efdecl)
                        (funcRule efdecl)

-- Prove that a function rule is fail free (w.r.t. their non-fail condition).
-- The rule is in eta-expanded form.
proveNonFailingRule :: Options -> ProgInfo [(QName,Int)] -> IORef VState
                    -> QName -> TypeExpr -> TARule -> IO ()
proveNonFailingRule _ _ vstref qn ftype (AExternal _ _) = do
  ti <- readVerifyInfoRef vstref
  let atypes = argTypes ftype
      args   = zip [1 .. length atypes] atypes
  nfcond <- evalStateT (nonfailPreCondExpOf ti qn ftype args) emptyTransState
  unless (nfcond == tTrue) $ modifyIORef vstref incNumNFCInStats
proveNonFailingRule opts siblingconsinfo vstref qn@(_,fn) ftype
                    (ARule _ rargs rhs) = do
  ti <- readVerifyInfoRef vstref
  let st = makeTransState (maximum (0 : map fst rargs ++ allVars rhs) + 1) rargs
  (flip evalStateT) st $ do
    -- compute non-fail precondition of operation:
    precondformula <- nonfailPreCondExpOf ti qn ftype rargs
    setAssertion precondformula
    unless (precondformula == tTrue) $ lift $
      modifyIORef vstref incNumNFCInStats
    -- verify only if the precondition is different from always failing:
    unless (precondformula == tFalse) $ proveNonFailExp ti rhs
 where
  proveNonFailExp ti exp = case simpExpr exp of
    AComb _ ct (qf,qfty) args -> do
      mapM_ (proveNonFailExp ti) args
      when (isCombTypeFuncPartCall ct) $
        let qnnonfail = toNonFailQName qf
        in maybe
             (return ()) -- h.o. call nonfailing if op. has no non-fail cond.
             (\_ -> lift $ do
               let reason = "due to call '" ++ ppTAExpr exp ++ "'"
               modifyIORef vstref (addFailedFuncToStats fn reason)
               printWhenIntermediate opts $
                 fn ++ ": POSSIBLY FAILING CALL OF '" ++ snd qf ++ "'")
             (find (\fd -> funcName fd == qnnonfail) (nfConds ti))
      when (ct==FuncCall) $ do
        lift $ printWhenIntermediate opts $ "Analyzing call to " ++ snd qf
        precond <- getAssertion
        (bs,_)   <- normalizeArgs args
        bindexps <- mapM (binding2SMT True ti) bs
        let callargs = zip (map fst bs) (map annExpr args)
        nfcondcall <- nonfailPreCondExpOf ti qf qfty callargs
        -- TODO: select from 'bindexps' only demanded argument positions
        vartypes <- getVarTypes
        valid <- if nfcondcall == tTrue
                   then return (Just True) -- true non-fail cond. is valid
                   else lift $ do
                     modifyIORef vstref incFailTestInStats
                     let title = "SMT script to verify non-failing call of '" ++
                                 snd qf ++ "' in function '" ++ fn ++ "'"
                     checkImplicationWithSMT opts vstref title vartypes
                       precond (tConj bindexps) nfcondcall
        if valid == Just True
          then lift $ printWhenIntermediate opts $
                 fn ++ ": NON-FAILING CALL OF '" ++ snd qf ++ "'"
          else lift $ do
            let reason = if valid == Nothing
                           then "due to SMT error"
                           else "due to call '" ++ ppTAExpr exp ++ "'"
            modifyIORef vstref (addFailedFuncToStats fn reason)
            printWhenIntermediate opts $
              fn ++ ": POSSIBLY FAILING CALL OF '" ++ snd qf ++ "'"
    ACase _ _ e brs -> do
      proveNonFailExp ti e
      maybe
       (do -- check a case expression for missing constructors:
          freshvar <- getFreshVar
          let freshtypedvar = (freshvar, annExpr e)
          be <- binding2SMT True ti (freshvar,e)
          addToAssertion be
          addVarTypes [freshtypedvar]
          let misscons = missingConsInBranch siblingconsinfo brs
          st <- get -- use same state to prove missing and non-fail branches
          mapM_ (verifyMissingCons freshtypedvar exp) misscons
          put st
          mapM_ (proveNonFailBranch ti freshtypedvar) brs
       )
       (\ (fe,te) -> do
           -- check a Boolean case with True/False branch:
           be <- pred2SMT e
           st <- get
           addToAssertion (tNot be)
           proveNonFailExp ti fe
           put st
           addToAssertion be
           proveNonFailExp ti te
       )
       (testBoolCase brs)
    AOr _ e1 e2 -> do st <- get -- use same state for both branches
                      proveNonFailExp ti e1
                      put st
                      proveNonFailExp ti e2
    ALet _ bs e -> do (rbs,re) <- renameLetVars bs e
                      mapM_ (proveNonFailExp ti) (map snd rbs)
                      proveNonFailExp ti re
    AFree _ fvs e -> do (_,re) <- renameFreeVars fvs e
                        proveNonFailExp ti re
    ATyped _ e _ -> proveNonFailExp ti e
    AVar _ _ -> return ()
    ALit _ _ -> return ()

  -- verify whether a variable (2. argument) can have the constructor (3. arg.)
  -- as a value w.r.t. the collected assertions
  verifyMissingCons (var,vartype) exp (cons,_) = do
    let title = "check missing constructor case '" ++ snd cons ++
                "' in function '" ++ fn ++ "'"
    lift $ printWhenIntermediate opts $
      title ++ "\nVAR: " ++ show (var,vartype) ++ "\nCASE:: " ++
      show (unAnnExpr (simpExpr exp))
    lift $ modifyIORef vstref incPatTestInStats
    
    vartypes <- getVarTypes
    precond  <- getAssertion
    valid <- lift $ checkImplicationWithSMT opts vstref
                      ("SMT script to " ++ title) vartypes precond tTrue
                      (tNot (constructorTest False cons (TSVar var) vartype))
    unless (valid == Just True) $ lift $ do
      let reason = if valid == Nothing
                     then "due to SMT error"
                     else "maybe not defined on constructor '" ++
                          showQName cons ++ "'"
      modifyIORef vstref (addFailedFuncToStats fn reason)
      printWhenIntermediate opts $
        "POSSIBLY FAILING BRANCH in function '" ++ fn ++
        "' with constructor " ++ snd cons

  proveNonFailBranch ti (var,vartype) branch = do
    ABranch p e <- renamePatternVars branch
    -- set pattern type correctly (important for [] pattern)
    let bpat = pat2SMT (setAnnPattern vartype p)
    addToAssertion (tEquVar var bpat)
    proveNonFailExp ti e

-- Returns the constructors (name/arity) which are missing in the given
-- branches of a case construct.
missingConsInBranch :: ProgInfo [(QName,Int)] -> [TABranchExpr] -> [(QName,Int)]
missingConsInBranch _ [] =
  error "missingConsInBranch: case with empty branches!"
missingConsInBranch _ (ABranch (ALPattern _ _) _ : _) =
  error "TODO: case with literal pattern"
missingConsInBranch siblingconsinfo
                    (ABranch (APattern _ (cons,_) _) _ : brs) =
  let othercons = maybe (error $ "Sibling constructors of " ++
                                 showQName cons ++ " not found!")
                        id
                        (lookupProgInfo cons siblingconsinfo)
      branchcons = map (patCons . branchPattern) brs
  in filter ((`notElem` branchcons) . fst) othercons

-- Simplifies a FlatCurry expression (only at the top-level!)
-- by considering the semantics of some predefined operations.
simpExpr :: TAExpr -> TAExpr
simpExpr exp = case exp of
  AComb ty FuncCall (qf,_) args ->
    if qf == pre "?"
      then AOr ty (args!!0) (args!!1)
      else if qf == pre "ord" || qf == pre "id" -- ops without preconditions
             then head args -- note: Char is implemented as Int in SMT
             else exp
  _ -> exp

-- Translates a FlatCurry expression to a Boolean formula representing
-- the binding of a variable (represented by its index in the first
-- component) to the translated expression (second component).
-- The translated expression is normalized when necessary.
-- For this purpose, a "fresh variable index" is passed as a state.
-- Moreover, the returned state contains also the types of all fresh variables.
-- If the first argument is `False`, the expression is not strictly demanded,
-- i.e., possible contracts of it (if it is a function call) are ignored.
binding2SMT :: Bool -> VerifyInfo -> (Int,TAExpr) -> TransStateM Term
binding2SMT demanded ti (resvar,exp) =
 case simpExpr exp of
  AVar _ i -> return $ if resvar==i then tTrue
                                    else tEquVar resvar (TSVar i)
  ALit _ l -> return (tEquVar resvar (lit2SMT l))
  AComb rtype ct (qf,_) args -> do
    (bs,nargs) <- normalizeArgs args
    -- TODO: select from 'bindexps' only demanded argument positions
    bindexps <- mapM (binding2SMT (isPrimOp qf || optStrict (toolOpts ti)) ti)
                     bs
    comb2bool qf rtype ct nargs bs bindexps
  ALet _ bs e -> do
    bindexps <- mapM (binding2SMT False ti)
                    (map (\ ((i,_),ae) -> (i,ae)) bs)
    bexp <- binding2SMT demanded ti (resvar,e)
    return (tConj (bindexps ++ [bexp]))
  AOr _ e1 e2  -> do
    bexp1 <- binding2SMT demanded ti (resvar,e1)
    bexp2 <- binding2SMT demanded ti (resvar,e2)
    return (tDisj [bexp1, bexp2])
  ACase _ _ e brs   -> do
    freshvar <- getFreshVar
    addVarTypes [(freshvar, annExpr e)]
    argbexp <- binding2SMT demanded ti (freshvar,e)
    bbrs    <- mapM branch2bool (map (\b->(freshvar,b)) brs)
    return (tConj [argbexp, tDisj bbrs])
  ATyped _ e _ -> binding2SMT demanded ti (resvar,e)
  AFree _ _ _ -> error "Free variables not yet supported!"
 where
   comb2bool qf rtype ct nargs bs bindexps
    | qf == pre "otherwise"
      -- specific handling for the moment since the front end inserts it
      -- as the last alternative of guarded rules...
    = return (tEquVar resvar tTrue)
    | ct == ConsCall
    = return (tConj (bindexps ++
                    [tEquVar resvar
                             (TComb (cons2SMT (null nargs) False qf rtype)
                                    (map arg2bool nargs))]))
    | qf == pre "apply"
    = -- cannot translate h.o. apply: ignore it
      return tTrue
    | isPrimOp qf
    = return (tConj (bindexps ++
                    [tEquVar resvar
                             (TComb (cons2SMT True False qf rtype)
                                    (map arg2bool nargs))]))
    | otherwise -- non-primitive operation: add contract only if demanded
    = do let targs = zip (map fst bs) (map annExpr nargs)
         precond  <- preCondExpOf ti qf targs
         postcond <- postCondExpOf ti qf (targs ++ [(resvar,rtype)])
         return (tConj (bindexps ++
                       if demanded && optContract (toolOpts ti)
                         then [precond,postcond]
                         else []))
   
   branch2bool (cvar, ABranch p e) = do
     branchbexp <- binding2SMT demanded ti (resvar,e)
     addVarTypes patvars
     return (tConj [ tEquVar cvar (pat2SMT p), branchbexp])
    where
     patvars = if isConsPattern p
                 then patArgs p
                 else []

   arg2bool e = case e of AVar _ i -> TSVar i
                          ALit _ l -> lit2SMT l
                          _ -> error $ "Not normalized: " ++ show e

-- Returns the conjunction of the non-failure condition and precondition
-- (if the tool option `contract` is set) expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding the `freshvar` index to them.
nonfailPreCondExpOf :: VerifyInfo -> QName -> TypeExpr -> [(Int,TypeExpr)]
                    -> TransStateM Term
nonfailPreCondExpOf ti qf ftype args =
  if optContract (toolOpts ti)
    then do
      (fvars,nfcond) <- nonfailCondExpOf ti qf ftype args
      precond <- preCondExpOf ti qf (args ++ fvars)
      -- simplify term in order to check later for trivial precondition
      return (simpTerm (tConj [nfcond,precond]))
    else do
      (_,rt) <- nonfailCondExpOf ti qf ftype args
      return rt

-- Returns the non-failure condition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- All local variables are renamed by adding the `freshvar` index to them.
-- If the non-failure condition requires more arguments (due to a
-- higher-order call), fresh arguments are added which are also returned.
nonfailCondExpOf :: VerifyInfo -> QName -> TypeExpr -> [(Int,TypeExpr)]
                 -> TransStateM ([(Int,TypeExpr)], Term)
nonfailCondExpOf ti qf ftype args =
  maybe
    (predefs qf)
    (\fd -> let moreargs = funcArity fd - length args in
            if moreargs > 0
              then do
                -- eta-expand function call with fresh variables so that one
                -- can check non-fail conditions with a greater arity:
                let etatypes = argTypes (dropArgTypes (length args) ftype)
                fvars <- getFreshVarsForTypes (take moreargs etatypes)
                rt    <- applyFunc fd (args ++ fvars) >>= pred2SMT
                return (fvars,rt)
              else if moreargs < 0
                     then error $ "Operation '" ++ snd qf ++
                                  "': nonfail condition has too few arguments!"
                     else do rt <- applyFunc fd args >>= pred2SMT
                             return ([],rt) )
    (find (\fd -> decodeContractQName (funcName fd) == toNonFailQName qf)
          (nfConds ti))
 where
  predefs qn | qn `elem` [pre "failed", pre "=:="] ||
               (qn == pre "error" && optError (toolOpts ti))
             = return ([], tFalse)
             | otherwise
             = return ([], tTrue)

-- Returns the precondition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding the `freshvar` index to them.
preCondExpOf :: VerifyInfo -> QName -> [(Int,TypeExpr)] -> TransStateM Term
preCondExpOf ti qf args =
  maybe (return tTrue)
        (\fd -> applyFunc fd args >>= pred2SMT)
        (find (\fd -> funcName fd == toPreCondQName qf) (preConds ti))

-- Returns the postcondition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding `freshvar` to them and
-- return the new freshvar value.
postCondExpOf :: VerifyInfo -> QName -> [(Int,TypeExpr)] -> TransStateM Term
postCondExpOf ti qf args =
  maybe (return tTrue)
        (\fd -> applyFunc fd args >>= pred2SMT)
        (find (\fd -> funcName fd == toPostCondQName qf) (postConds ti))


-- Applies a function declaration on a list of arguments,
-- which are assumed to be variable indices, and returns
-- the renamed body of the function declaration.
-- All local variables are renamed by adding `freshvar` to them.
-- Also the new fresh variable index is returned.
applyFunc :: TAFuncDecl -> [(Int,TypeExpr)] -> TransStateM TAExpr
applyFunc fdecl targs = do
  fv <- getFreshVarIndex
  let tsub = maybe (error $ "applyFunc: types\n" ++
                            show (argTypes (funcType fdecl)) ++ "\n" ++
                            show (map snd targs) ++ "\ndo not match!")
                   id
                   (matchTypes (argTypes (funcType fdecl)) (map snd targs))
      (ARule _ orgargs orgexp) = substRule tsub (funcRule fdecl)
      exp = rnmAllVars (renameRuleVar fv orgargs) orgexp
  setFreshVarIndex (max fv (maximum (0 : args ++ allVars exp) + 1))
  return $ simpExpr $ applyArgs exp (drop (length orgargs) args)
 where
  args = map fst targs
  -- renaming function for variables in original rule:
  renameRuleVar fv orgargs r = maybe (r + fv)
                                     (args!!)
                                     (elemIndex r (map fst orgargs))

  applyArgs e [] = e
  applyArgs e (v:vs) =
    -- simple hack for eta-expansion since the type annotations are not used:
    -- TODO: compute correct type annotations!!! (required for overloaded nils)
    let e_v =  AComb failed FuncCall
                     (pre "apply", failed) [e, AVar failed v]
    in applyArgs e_v vs

-- Translates a Boolean FlatCurry expression into a Boolean formula.
-- Calls to user-defined functions are replaced by the first argument
-- (which might be true or false).
pred2SMT :: TAExpr -> TransStateM Term
pred2SMT exp = case simpExpr exp of
  AVar  _ i                  -> return (TSVar i)
  ALit  _ l                  -> return (lit2SMT l)
  AComb _ ct (qf,ftype) args -> comb2bool qf ftype ct (length args) args
  _                          -> return (tComb (show exp) []) -- TODO!
 where
  comb2bool qf ftype ct ar args
    | qf == pre "[]" && ar == 0
    = return (sortedConst "nil" (polytype2sort (annExpr exp)))
    | qf == pre "not" && ar == 1
    = do barg <- pred2SMT (head args)
         return (tNot barg)
    | qf == pre "null" && ar == 1
    = do let arg = head args
         barg    <- pred2SMT arg
         vartype <- typeOfVar arg
         return (tEqu barg (sortedConst "nil" (polytype2sort vartype)))
    | qf == pre "apply"
    = do -- cannot translate h.o. apply: replace it by new variable
         fvar <- getFreshVar
         addVarTypes [(fvar,annExpr exp)]
         return (TSVar fvar)
    | qf == pre "/="
    = do be <- comb2bool (pre "==") ftype ct ar args
         return (tNot be)
    | otherwise
    = do bargs <- mapM pred2SMT args
         return (TComb (cons2SMT (ct /= ConsCall || not (null bargs))
                                 False qf ftype)
                       bargs)

  typeOfVar e = do
    vartypes <- getVarTypes
    case e of
      AVar _ i -> maybe
                    (error $ "pred2SMT: variable " ++ show i ++ " not found")
                    return
                    (lookup i vartypes)
      _        -> return $ annExpr e -- might not be correct due to applyFunc!
 
normalizeArgs :: [TAExpr] -> TransStateM ([(Int,TAExpr)],[TAExpr])
normalizeArgs [] = return ([],[])
normalizeArgs (e:es) = case e of
  AVar _ i -> do (bs,nes) <- normalizeArgs es
                 return ((i,e):bs, e:nes)
  _        -> do fvar <- getFreshVar
                 addVarTypes [(fvar,annExpr e)]
                 (bs,nes) <- normalizeArgs es
                 return ((fvar,e):bs, AVar (annExpr e) fvar : nes)


-- Get for the types (given in the first argument) fresh typed variables.
getFreshVarsForTypes :: [TypeExpr] -> TransStateM [(VarIndex, TypeExpr)]
getFreshVarsForTypes types = do
  fv <- getFreshVarIndex
  let n     = length types
      vars  = take n [fv ..]
      tvars = zip vars types
  setFreshVarIndex (fv + n)
  addVarTypes tvars
  return tvars


-- Rename let-bound variables in a let expression.
renameLetVars :: [((VarIndex, TypeExpr), TAExpr)] -> TAExpr
              -> TransStateM ([((VarIndex, TypeExpr), TAExpr)], TAExpr)
renameLetVars bindings exp = do
  fv <- getFreshVarIndex
  let args = map (fst . fst) bindings
      minarg = minimum (0 : args)
      maxarg = maximum (0 : args)
      rnm i = if i `elem` args then i - minarg + fv else i
      nargs = map (\ ((v,t),_) -> (rnm v,t)) bindings
  setFreshVarIndex (fv + maxarg - minarg + 1)
  addVarTypes nargs
  return (map (\ ((v,t),be) -> ((rnm v,t), rnmAllVars rnm be)) bindings,
          rnmAllVars rnm exp)


-- Rename free variables introduced in an expression.
renameFreeVars :: [(VarIndex, TypeExpr)] -> TAExpr
               -> TransStateM ([(VarIndex, TypeExpr)], TAExpr)
renameFreeVars freevars exp = do
  fv <- getFreshVarIndex
  let args = map fst freevars
      minarg = minimum (0 : args)
      maxarg = maximum (0 : args)
      rnm i = if i `elem` args then i - minarg + fv else i
      nargs = map (\ (v,t) -> (rnm v,t)) freevars
  setFreshVarIndex (fv + maxarg - minarg + 1)
  addVarTypes nargs
  return (map (\ (v,t) -> (rnm v,t)) freevars, rnmAllVars rnm exp)


-- Rename argument variables of constructor pattern
renamePatternVars :: TABranchExpr -> TransStateM TABranchExpr
renamePatternVars (ABranch p e) = do
  if isConsPattern p
    then do fv <- getFreshVarIndex
            let args = map fst (patArgs p)
                minarg = minimum (0 : args)
                maxarg = maximum (0 : args)
                rnm i = if i `elem` args then i - minarg + fv else i
                nargs = map (\ (v,t) -> (rnm v,t)) (patArgs p)
            setFreshVarIndex (fv + maxarg - minarg + 1)
            addVarTypes nargs
            return $ ABranch (updPatArgs (map (\ (v,t) -> (rnm v,t))) p)
                             (rnmAllVars rnm e)
    else return $ ABranch p e

---------------------------------------------------------------------------
-- Calls the SMT solver to check whether an assertion implies some
-- property.
checkImplicationWithSMT :: Options -> IORef VState -> String -> [(Int,TypeExpr)]
                        -> Term -> Term -> Term -> IO (Maybe Bool)
checkImplicationWithSMT opts vstref scripttitle vartypes
                        assertion impbindings imp = do
  let (pretypes,usertypes) =
         partition ((== "Prelude") . fst)
                   (foldr union [] (map (tconsOfTypeExpr . snd) vartypes))
  vst <- readIORef vstref
  let allsyms = catMaybes
                  (map (\n -> maybe Nothing Just (untransOpName n))
                       (map qidName
                         (allQIdsOfTerm (tConj [assertion, impbindings, imp]))))
  unless (null allsyms) $ printWhenIntermediate opts $
    "Translating operations into SMT: " ++
    unwords (map showQName allsyms)
  smtfuncs <- funcs2SMT vstref allsyms
  let decls = map (maybe (error "Internal error: some datatype not found!") id)
                  (map (tdeclOf vst) usertypes)
      smt   = concatMap preludeType2SMT (map snd pretypes) ++
              [ EmptyLine ] ++
              (if null decls
                 then []
                 else [ Comment "User-defined datatypes:" ] ++
                      map tdecl2SMT decls) ++
              [ EmptyLine, smtfuncs, EmptyLine
              , Comment "Free variables:" ] ++
              map typedVar2SMT vartypes ++
              [ EmptyLine
              , Comment "Boolean formula of assertion (known properties):"
              , sAssert assertion, EmptyLine
              , Comment "Bindings of implication:"
              , sAssert impbindings, EmptyLine
              , Comment "Assert negated implication:"
              , sAssert (tNot imp), EmptyLine
              , Comment "check satisfiability:"
              , CheckSat
              , Comment "if unsat, the implication is valid"
              ]
  --putStrLn $ "SMT commands as Curry term:\n" ++ show smt
  smtprelude <- readFile (packagePath </> "include" </> "Prelude.smt")
  let smtinput = "; " ++ scripttitle ++ "\n\n" ++ smtprelude ++ showSMT smt
  printWhenAll opts $ "SMT SCRIPT:\n" ++ showWithLineNums smtinput
  printWhenAll opts $ "CALLING Z3 (with options: -smt2 -T:5)..."
  (ecode,out,err) <- evalCmd "z3" ["-smt2", "-in", "-T:5"] smtinput
  when (ecode>0) $ do printWhenAll opts $ "EXIT CODE: " ++ show ecode
                      writeFile "error.smt" smtinput
  printWhenAll opts $ "RESULT:\n" ++ out
  unless (null err) $ printWhenAll opts $ "ERROR:\n" ++ err
  let pcvalid = let ls = lines out in not (null ls) && head ls == "unsat"
  return (if ecode>0 then Nothing else Just pcvalid)


-- Operations axiomatized by specific smt scripts (no longer necessary
-- since these scripts are now automatically generated by Curry2SMT.funcs2SMT).
-- However, for future work, it might be reasonable to cache these scripts
-- for faster contract checking.
axiomatizedOps :: [String]
axiomatizedOps = ["Prelude_null","Prelude_take","Prelude_length"]

---------------------------------------------------------------------------
-- Translate a typed variables to an SMT declaration:
typedVar2SMT :: (Int,TypeExpr) -> Command
typedVar2SMT (i,te) = DeclareVar (SV i (polytype2sort te))

-- Gets all type constructors of a type expression.
tconsOfTypeExpr :: TypeExpr -> [QName]
tconsOfTypeExpr (TVar _) = []
tconsOfTypeExpr (FuncType a b) =  union (tconsOfTypeExpr a) (tconsOfTypeExpr b)
tconsOfTypeExpr (TCons qName texps) =
  foldr union [qName] (map tconsOfTypeExpr texps)
tconsOfTypeExpr (ForallType _ te) =  tconsOfTypeExpr te

---------------------------------------------------------------------------
-- Auxiliaries:

--- Tests whether the given branches of a case expressions
--- are a Boolean case distinction.
--- If yes, the expressions of the `False` and `True` branch
--- are returned.
testBoolCase :: [TABranchExpr] -> Maybe (TAExpr,TAExpr)
testBoolCase brs =
  if length brs /= 2 then Nothing
                     else case (brs!!0, brs!!1) of
    (ABranch (APattern _ (c1,_) _) e1, ABranch (APattern _ (c2,_) _) e2) ->
      if c1 == pre "False" && c2 == pre "True"  then Just (e1,e2) else
      if c1 == pre "True"  && c2 == pre "False" then Just (e2,e1) else Nothing
    _ -> Nothing

--- Shows a text with line numbers prefixed:
showWithLineNums :: String -> String
showWithLineNums txt =
  let txtlines  = lines txt
      maxlog    = ilog (length txtlines + 1)
      showNum n = (take (maxlog - ilog n) (repeat ' ')) ++ show n ++ ": "
  in unlines . map (uncurry (++)) . zip (map showNum [1..]) $ txtlines

--- The value of `ilog n` is the floor of the logarithm
--- in the base 10 of `n`.
--- Fails if `n &lt;= 0`.
--- For positive integers, the returned value is
--- 1 less the number of digits in the decimal representation of `n`.
---
--- @param n - The argument.
--- @return the floor of the logarithm in the base 10 of `n`.
ilog :: Int -> Int
ilog n | n>0 = if n<10 then 0 else 1 + ilog (n `div` 10)

---------------------------------------------------------------------------

{-

Still to be done:

- consider encapsulated search


Verified system libraries:

- Prelude
- Char
- Either
- ErrorState
- Integer
- Maybe
- State
- ShowS

 Prelude Char Either ErrorState Integer Maybe State ShowS

-}
