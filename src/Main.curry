-----------------------------------------------------------------------------
--- A tool to verify non-failure properties of Curry operations.
---
--- @author  Michael Hanus
--- @version April 2019
---------------------------------------------------------------------------

module Main where

import Directory    ( doesFileExist )
import FilePath     ( (</>) )
import Integer      ( ilog )
import IOExts
import List         ( (\\), elemIndex, find, isPrefixOf, isSuffixOf
                    , maximum, minimum, partition, splitOn, union )
import Maybe        ( catMaybes )
import State
import System

-- Imports from dependencies:
import Analysis.ProgInfo
import Analysis.TotallyDefined ( siblingCons )
import Analysis.Types
import Contract.Names
import Contract.Usage          ( checkContractUsage )
import CASS.Server             ( analyzeGeneric, analyzePublic )
import Debug.Profile
import FlatCurry.Annotated.TypeSubst ( substRule )
import FlatCurry.Files               ( readFlatCurryInt )
import FlatCurry.Types
import FlatCurry.Annotated.Goodies
import ShowFlatCurry                 ( showCurryModule )
import System.Path                   ( fileInPath )

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
   bannerText = "Fail-Free Verification Tool for Curry (Version of 29/04/19)"
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
verifyNonFailingModules _ _ [] = done
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
  impprogs <- mapIO (readSimpTypedFlatCurryWithSpec opts) (progImports prog)
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
loadAnalysisWithImports :: Analysis a -> TAProg -> IO (ProgInfo a)
loadAnalysisWithImports analysis prog = do
  maininfo <- analyzeGeneric analysis (progName prog)
                >>= return . either id error
  impinfos <- mapIO (\m -> analyzePublic analysis m >>=
                                                     return . either id error)
                    (progImports prog)
  return $ foldr combineProgInfo maininfo impinfos

---------------------------------------------------------------------------
-- The state of the transformation process contains
-- * the current assertion
-- * a fresh variable index
-- * a list of all introduced variables and their types:
data TransState = TransState
  { preCond    :: Term
  , freshVar   :: Int
  , varTypes   :: [(Int,TypeExpr)]
  }

makeTransState :: Int -> [(Int,TypeExpr)] -> TransState
makeTransState = TransState tTrue

-- Increments fresh variable index.
incFreshVarIndex :: TransState -> TransState
incFreshVarIndex st = st { freshVar = freshVar st + 1 }

-- Adds variables to the state.
addVarTypes :: [(Int,TypeExpr)] -> TransState -> TransState
addVarTypes vts st = st { varTypes = vts ++ varTypes st }

---------------------------------------------------------------------------
-- Prove that a list of defined functions is fail free (w.r.t. their
-- non-fail conditions).
proveNonFailingFuncs :: Options -> ProgInfo [(QName,Int)] -> IORef VState
                     -> [TAFuncDecl] -> IO ()
proveNonFailingFuncs opts siblingconsinfo vstref =
  mapIO_ (proveNonFailingFunc opts siblingconsinfo vstref)

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
      (nfcond,_)  = nonfailPreCondExpOf ti qn ftype args (makeTransState 0 [])
  unless (nfcond == tTrue) $ modifyIORef vstref incNumNFCInStats
proveNonFailingRule opts siblingconsinfo vstref qn@(_,fn) ftype
                    (ARule _ rargs rhs) = do
  ti <- readVerifyInfoRef vstref
  let -- compute non-fail precondition of operation:
      s0 = makeTransState (maximum (0 : map fst rargs ++ allVars rhs) + 1) rargs
      (precondformula,s1)  = nonfailPreCondExpOf ti qn ftype rargs s0
      s2 = s1 { preCond = precondformula }
  unless (precondformula == tTrue)  $ modifyIORef vstref incNumNFCInStats
  -- verify only if the precondition is different from always failing:
  unless (precondformula == tFalse) $ proveNonFailExp ti s2 rhs
 where
  proveNonFailExp ti pts exp = case simpExpr exp of
    AComb _ ct (qf,qfty) args -> do
      mapIO_ (proveNonFailExp ti pts) args
      when (isCombTypeFuncPartCall ct) $
        let qnnonfail = toNonFailQName qf
        in maybe done -- h.o. call nonfailing if op. has no non-fail cond.
             (\_ -> do
               let reason = "due to call '" ++ ppTAExpr exp ++ "'"
               modifyIORef vstref (addFailedFuncToStats fn reason)
               printWhenIntermediate opts $
                 fn ++ ": POSSIBLY FAILING CALL OF '" ++ snd qf ++ "'")
             (find (\fd -> funcName fd == qnnonfail) (nfConds ti))
      when (ct==FuncCall) $ do
        printWhenIntermediate opts $ "Analyzing call to " ++ snd qf
        let ((bs,_)    ,pts1) = normalizeArgs args pts
            (bindexps  ,pts2) = mapS (binding2SMT True ti) bs pts1
            callargs = zip (map fst bs) (map annExpr args)
            (nfcondcall,pts3) = nonfailPreCondExpOf ti qf qfty callargs pts2
        -- TODO: select from 'bindexps' only demanded argument positions
        valid <- if nfcondcall == tTrue
                   then return (Just True) -- true non-fail cond. is valid
                   else do
                     modifyIORef vstref incFailTestInStats
                     let title = "SMT script to verify non-failing call of '" ++
                                 snd qf ++ "' in function '" ++ fn ++ "'"
                     checkImplicationWithSMT opts vstref title (varTypes pts3)
                          (preCond pts) (tConj bindexps) nfcondcall
        if valid == Just True
          then do
            printWhenIntermediate opts $
              fn ++ ": NON-FAILING CALL OF '" ++ snd qf ++ "'"
          else do
            let reason = if valid == Nothing
                           then "due to SMT error"
                           else "due to call '" ++ ppTAExpr exp ++ "'"
            modifyIORef vstref (addFailedFuncToStats fn reason)
            printWhenIntermediate opts $
              fn ++ ": POSSIBLY FAILING CALL OF '" ++ snd qf ++ "'"
    ACase _ _ e brs -> do
      proveNonFailExp ti pts e
      maybe
       (-- check a case expression for missing constructors:
        let freshvar = freshVar pts
            freshtypedvar = (freshvar, annExpr e)
            (be,pts1) = binding2SMT True ti (freshvar,e) (incFreshVarIndex pts)
            pts2 = pts1 { preCond = tConj [preCond pts, be]
                        , varTypes = freshtypedvar : varTypes pts1 }
            misscons = missingConsInBranch siblingconsinfo brs
        in do mapIO_ (verifyMissingCons pts2 freshtypedvar exp) misscons
              mapIO_ (proveNonFailBranch ti pts2 freshtypedvar) brs
       )
       (\ (fe,te) ->
           -- check a Boolean case with True/False branch:
           let (be,pts1) = pred2SMT e pts
               ptsf = pts1 { preCond = tConj [preCond pts, tNot be] }
               ptst = pts1 { preCond = tConj [preCond pts, be] }
           in do proveNonFailExp ti ptsf fe
                 proveNonFailExp ti ptst te
       )
       (testBoolCase brs)
    AOr _ e1 e2 -> do proveNonFailExp ti pts e1
                      proveNonFailExp ti pts e2
    ALet _ bs e -> do let ((rbs,re), pts1) = renameLetVars pts bs e
                      mapIO_ (proveNonFailExp ti pts1) (map snd rbs)
                      proveNonFailExp ti pts1 re
    AFree _ fvs e -> do let ((_,re), pts1) = renameFreeVars pts fvs e
                        proveNonFailExp ti pts1 re
    ATyped _ e _ -> proveNonFailExp ti pts e
    AVar _ _ -> done
    ALit _ _ -> done

  -- verify whether a variable (2. argument) can have the constructor (3. arg.)
  -- as a value w.r.t. the collected assertions
  verifyMissingCons pts (var,vartype) exp (cons,_) = do
    let title = "check missing constructor case '" ++ snd cons ++
                "' in function '" ++ fn ++ "'"
    printWhenIntermediate opts $
      title ++ "\nVAR: " ++ show (var,vartype) ++ "\nCASE:: " ++
      show (unAnnExpr (simpExpr exp))
    modifyIORef vstref incPatTestInStats
    
    valid <- checkImplicationWithSMT opts vstref ("SMT script to " ++ title)
               (varTypes pts) (preCond pts) tTrue
               (tNot (constructorTest False cons (TSVar var) vartype))
    unless (valid == Just True) $ do
      let reason = if valid == Nothing
                     then "due to SMT error"
                     else "maybe not defined on constructor '" ++
                          showQName cons ++ "'"
      modifyIORef vstref (addFailedFuncToStats fn reason)
      printWhenIntermediate opts $
        "POSSIBLY FAILING BRANCH in function '" ++ fn ++
        "' with constructor " ++ snd cons

  proveNonFailBranch ti pts (var,vartype) branch = do
    let (ABranch p e, pts1) = renamePatternVars pts branch
        -- set pattern type correctly (important for [] pattern)
        bpat = pat2smt (setAnnPattern vartype p)
        npts = pts1 { preCond = tConj [preCond pts1, tEquVar var bpat] }
    proveNonFailExp ti npts e

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
binding2SMT :: Bool -> VerifyInfo -> (Int,TAExpr) -> State TransState Term
binding2SMT demanded ti (resvar,exp) =
 case simpExpr exp of
  AVar _ i -> returnS $ if resvar==i then tTrue
                                     else tEquVar resvar (TSVar i)
  ALit _ l -> returnS (tEquVar resvar (lit2smt l))
  AComb rtype ct (qf,_) args ->
    normalizeArgs args `bindS` \ (bs,nargs) ->
    -- TODO: select from 'bindexps' only demanded argument positions
    mapS (binding2SMT (isPrimOp qf || optStrict (toolOpts ti)) ti) bs
         `bindS` \bindexps ->
    comb2bool qf rtype ct nargs bs bindexps
  ALet _ bs e ->
    mapS (binding2SMT False ti)
         (map (\ ((i,_),ae) -> (i,ae)) bs) `bindS` \bindexps ->
    binding2SMT demanded ti (resvar,e) `bindS` \bexp ->
    returnS (tConj (bindexps ++ [bexp]))
  AOr _ e1 e2  ->
    binding2SMT demanded ti (resvar,e1) `bindS` \bexp1 ->
    binding2SMT demanded ti (resvar,e2) `bindS` \bexp2 ->
    returnS (tDisj [bexp1, bexp2])
  ACase _ _ e brs   ->
    getS `bindS` \ts ->
    let freshvar = freshVar ts
    in putS (addVarTypes [(freshvar, annExpr e)] (incFreshVarIndex ts)) `bindS_`
       binding2SMT demanded ti (freshvar,e) `bindS` \argbexp ->
       mapS branch2bool (map (\b->(freshvar,b)) brs) `bindS` \bbrs ->
       returnS (tConj [argbexp, tDisj bbrs])
  ATyped _ e _ -> binding2SMT demanded ti (resvar,e)
  AFree _ _ _ -> error "Free variables not yet supported!"
 where
   comb2bool qf rtype ct nargs bs bindexps
    | qf == pre "otherwise"
      -- specific handling for the moment since the front end inserts it
      -- as the last alternative of guarded rules...
    = returnS (tEquVar resvar tTrue)
    | ct == ConsCall
    = returnS (tConj (bindexps ++
                     [tEquVar resvar
                              (TComb (cons2SMT (null nargs) False qf rtype)
                                     (map arg2bool nargs))]))
    | qf == pre "apply"
    = -- cannot translate h.o. apply: ignore it
      returnS tTrue
    | isPrimOp qf
    = returnS (tConj (bindexps ++
                     [tEquVar resvar
                              (TComb (cons2SMT True False qf rtype)
                                     (map arg2bool nargs))]))
    | otherwise -- non-primitive operation: add contract only if demanded
    = let targs = zip (map fst bs) (map annExpr nargs) in
      preCondExpOf ti qf targs `bindS` \precond ->
      postCondExpOf ti qf (targs ++ [(resvar,rtype)]) `bindS` \postcond ->
      returnS (tConj (bindexps ++
                     if demanded && optContract (toolOpts ti)
                       then [precond,postcond]
                       else []))
   
   branch2bool (cvar, ABranch p e) =
     binding2SMT demanded ti (resvar,e) `bindS` \branchbexp ->
     getS `bindS` \ts ->
     putS ts { varTypes = patvars ++ varTypes ts} `bindS_`
     returnS (tConj [ tEquVar cvar (pat2smt p), branchbexp])
    where
     patvars = if isConsPattern p
                 then patArgs p
                 else []

   arg2bool e = case e of AVar _ i -> TSVar i
                          ALit _ l -> lit2smt l
                          _ -> error $ "Not normalized: " ++ show e

-- Returns the conjunction of the non-failure condition and precondition
-- (if the tool option `contract` is set) expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding the `freshvar` index to them.
nonfailPreCondExpOf :: VerifyInfo -> QName -> TypeExpr -> [(Int,TypeExpr)]
                    -> State TransState Term
nonfailPreCondExpOf ti qf ftype args =
  if optContract (toolOpts ti)
    then nonfailCondExpOf ti qf ftype args `bindS` \ (fvars,nfcond) ->
         preCondExpOf     ti qf (args ++ fvars) `bindS` \precond ->
         -- simplify term in order to check later for trivial precondition
         returnS (simpTerm (tConj [nfcond,precond]))
    else nonfailCondExpOf ti qf ftype args `bindS` \ (_,rt) -> returnS rt

-- Returns the non-failure condition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- All local variables are renamed by adding the `freshvar` index to them.
-- If the non-failure condition requires more arguments (due to a
-- higher-order call), fresh arguments are added which are also returned.
nonfailCondExpOf :: VerifyInfo -> QName -> TypeExpr -> [(Int,TypeExpr)]
                 -> State TransState ([(Int,TypeExpr)], Term)
nonfailCondExpOf ti qf ftype args =
  maybe
    (predefs qf)
    (\fd -> let moreargs = funcArity fd - length args in
            if moreargs > 0
              then -- eta-expand function call with fresh variables so that one
                   -- can check non-fail conditions with a greater arity:
                let etatypes = argTypes (dropArgTypes (length args) ftype) in
                getFreshVarsForTypes (take moreargs etatypes) `bindS` \fvars ->
                applyFunc fd (args ++ fvars) `bindS` pred2SMT `bindS` \rt ->
                returnS (fvars,rt)
              else if moreargs < 0
                     then error $ "Operation '" ++ snd qf ++
                                  "': nonfail condition has too few arguments!"
                     else applyFunc fd args `bindS` pred2SMT `bindS` \rt ->
                          returnS ([],rt) )
    (find (\fd -> decodeContractQName (funcName fd) == toNonFailQName qf)
          (nfConds ti))
 where
  predefs qn | qn `elem` [pre "failed", pre "=:="] ||
               (qn == pre "error" && optError (toolOpts ti))
             = returnS ([],tFalse)
             | otherwise = returnS ([],tTrue)

-- Returns the precondition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding the `freshvar` index to them.
preCondExpOf :: VerifyInfo -> QName -> [(Int,TypeExpr)] -> State TransState Term
preCondExpOf ti qf args =
  maybe (returnS tTrue)
        (\fd -> applyFunc fd args `bindS` pred2SMT)
        (find (\fd -> funcName fd == toPreCondQName qf) (preConds ti))

-- Returns the postcondition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding `freshvar` to them and
-- return the new freshvar value.
postCondExpOf :: VerifyInfo -> QName -> [(Int,TypeExpr)]
              -> State TransState Term
postCondExpOf ti qf args =
  maybe (returnS tTrue)
        (\fd -> applyFunc fd args `bindS` pred2SMT)
        (find (\fd -> funcName fd == toPostCondQName qf) (postConds ti))


-- Applies a function declaration on a list of arguments,
-- which are assumed to be variable indices, and returns
-- the renamed body of the function declaration.
-- All local variables are renamed by adding `freshvar` to them.
-- Also the new fresh variable index is returned.
applyFunc :: TAFuncDecl -> [(Int,TypeExpr)] -> State TransState TAExpr
applyFunc fdecl targs s0 =
  let tsub = maybe (error $ "applyFunc: types\n" ++
                            show (argTypes (funcType fdecl)) ++ "\n" ++
                            show (map snd targs) ++ "\ndo not match!")
                   id
                   (matchTypes (argTypes (funcType fdecl)) (map snd targs))
      (ARule _ orgargs orgexp) = substRule tsub (funcRule fdecl)
      exp = rnmAllVars (renameRuleVar orgargs) orgexp
      s1  = s0 { freshVar = max (freshVar s0)
                                (maximum (0 : args ++ allVars exp) + 1) }
  in (simpExpr $ applyArgs exp (drop (length orgargs) args), s1)
 where
  args = map fst targs
  -- renaming function for variables in original rule:
  renameRuleVar orgargs r = maybe (r + freshVar s0)
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
pred2SMT :: TAExpr -> State TransState Term
pred2SMT exp = case simpExpr exp of
  AVar _ i              -> returnS (TSVar i)
  ALit _ l              -> returnS (lit2smt l)
  AComb _ ct (qf,ftype) args -> comb2bool qf ftype ct (length args) args
  _                          -> returnS (tComb (show exp) []) -- TODO!
 where
  comb2bool qf ftype ct ar args
    | qf == pre "[]" && ar == 0
    = returnS (sortedConst "nil" (polytype2sort (annExpr exp)))
    | qf == pre "not" && ar == 1
    = pred2SMT (head args) `bindS` \barg -> returnS (tNot barg)
    | qf == pre "null" && ar == 1
    = let arg = head args
      in pred2SMT arg `bindS` \barg ->
         getS `bindS` \tstate ->
         returnS (tEqu barg
                       (sortedConst "nil"
                                    (polytype2sort (typeOfVar tstate arg))))
    | qf == pre "apply"
    = -- cannot translate h.o. apply: replace it by new variable
      getS `bindS` \ts ->
      let fvar = freshVar ts
          nts  = addVarTypes [(fvar,annExpr exp)] (incFreshVarIndex ts)
      in putS nts `bindS_`
         returnS (TSVar fvar)
    | qf == pre "/="
    = comb2bool (pre "==") ftype ct ar args `bindS` \be ->
      returnS (tNot be)
    | otherwise
    = mapS pred2SMT args `bindS` \bargs ->
      returnS (TComb (cons2SMT (ct /= ConsCall || not (null bargs))
                               False qf ftype)
                     bargs)

  typeOfVar tstate e = case e of
    AVar _ i -> maybe (error $ "pred2SMT: variable " ++ show i ++ " not found")
                      id
                      (lookup i (varTypes tstate))
    _        -> annExpr e -- might not be correct due to applyFunc!
 
normalizeArgs :: [TAExpr] -> State TransState ([(Int,TAExpr)],[TAExpr])
normalizeArgs [] = returnS ([],[])
normalizeArgs (e:es) = case e of
  AVar _ i -> normalizeArgs es `bindS` \ (bs,nes) ->
              returnS ((i,e):bs, e:nes)
  _        -> getS `bindS` \ts ->
              let fvar = freshVar ts
                  nts  = addVarTypes [(fvar,annExpr e)] (incFreshVarIndex ts)
              in putS nts `bindS_`
                 normalizeArgs es `bindS` \ (bs,nes) ->
                 returnS ((fvar,e):bs, AVar (annExpr e) fvar : nes)


-- Get for the types (given in the first argument) fresh typed variables.
getFreshVarsForTypes :: [TypeExpr] -> State TransState [(VarIndex, TypeExpr)]
getFreshVarsForTypes types pts =
  let n     = length types
      fv    = freshVar pts
      vars  = take n [fv ..]
      tvars = zip vars types
  in (tvars, pts { freshVar = fv + n, varTypes = tvars ++ varTypes pts })


-- Rename let-bound variables in a let expression.
renameLetVars :: TransState -> [((VarIndex, TypeExpr), TAExpr)] -> TAExpr
              -> (([((VarIndex, TypeExpr), TAExpr)], TAExpr),TransState)
renameLetVars pts bindings exp =
  let args = map (fst . fst) bindings
      minarg = minimum (0 : args)
      maxarg = maximum (0 : args)
      fv     = freshVar pts
      rnm i = if i `elem` args then i - minarg + fv else i
      nargs = map (\ ((v,t),_) -> (rnm v,t)) bindings
  in ((map (\ ((v,t),be) -> ((rnm v,t), rnmAllVars rnm be)) bindings,
       rnmAllVars rnm exp),
      pts { freshVar = fv + maxarg - minarg + 1
          , varTypes = nargs ++ varTypes pts })


-- Rename free variables introduced in an expression.
renameFreeVars :: TransState -> [(VarIndex, TypeExpr)] -> TAExpr
              -> (([(VarIndex, TypeExpr)], TAExpr),TransState)
renameFreeVars pts freevars exp =
  let args = map fst freevars
      minarg = minimum (0 : args)
      maxarg = maximum (0 : args)
      fv     = freshVar pts
      rnm i = if i `elem` args then i - minarg + fv else i
      nargs = map (\ (v,t) -> (rnm v,t)) freevars
  in ((map (\ (v,t) -> (rnm v,t)) freevars, rnmAllVars rnm exp),
      pts { freshVar = fv + maxarg - minarg + 1
          , varTypes = nargs ++ varTypes pts })


-- Rename argument variables of constructor pattern
renamePatternVars :: TransState -> TABranchExpr -> (TABranchExpr,TransState)
renamePatternVars pts (ABranch p e) =
  if isConsPattern p
    then let args = map fst (patArgs p)
             minarg = minimum (0 : args)
             maxarg = maximum (0 : args)
             fv = freshVar pts
             rnm i = if i `elem` args then i - minarg + fv else i
             nargs = map (\ (v,t) -> (rnm v,t)) (patArgs p)
         in (ABranch (updPatArgs (map (\ (v,t) -> (rnm v,t))) p)
                     (rnmAllVars rnm e),
             pts { freshVar = fv + maxarg - minarg + 1
                 , varTypes = nargs ++ varTypes pts })
    else (ABranch p e, pts)


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
 where
  line = take 78 (repeat '-')

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
