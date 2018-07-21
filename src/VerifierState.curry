module VerifierState where

import Data.List ( find )

import FlatCurry.Annotated.Types
import FlatCurry.Annotated.Goodies

---------------------------------------------------------------------------
-- The global state of the verification process keeps some
-- statistical information and the programs that are already read (to
-- avoid multiple readings).
data VState = VState
  { failedFuncs  :: [(String,String)] -- partially defined operations
                                      -- and their failing reason
  , numAllFuncs  :: Int               -- number of analyzed operations
  , numNFCFuncs  :: Int               -- number of operations with non-trivial
                                      -- non-failing conditions
  , numPatTests  :: Int               -- number of missing pattern tests
  , numFailTests :: Int               -- number of tests of failure calls
  , currTAProgs  :: [AProg TypeExpr]  -- already read typed FlatCurry programs
  }

initVState :: VState
initVState = VState [] 0 0 0 0 []

--- Shows the statistics in human-readable format.
showStats :: VState -> String
showStats vstate = unlines $
  [ "TESTED OPERATIONS        : " ++ show (numAllFuncs vstate)
  , "NONFAIL CONDITIONS       : " ++ show (numNFCFuncs vstate)
  , "TESTS OF MISSING PATTERNS: " ++ show (numPatTests vstate)
  , "TESTS OF NON-FAIL CALLS  : " ++ show (numFailTests vstate) ] ++
  showStat "POSSIBLY FAILING OPERATIONS" (failedFuncs vstate) ++
  if isVerified vstate then ["NON-FAILURE VERIFICATION SUCCESSFUL!"] else []
 where
  showStat t fs =
    if null fs
      then []
      else (t ++ ":") :
           map (\ (fn,reason) -> fn ++ " (" ++ reason ++ ")")
               (reverse fs)

--- Are all non-failing properties verified?
isVerified :: VState -> Bool
isVerified vstate = null (failedFuncs vstate)

--- Adds a possibly failing call in a functions and the called function.
addFailedFuncToStats :: String -> String -> VState -> VState
addFailedFuncToStats fn qfun vstate =
  vstate { failedFuncs = (fn,qfun) : failedFuncs vstate }

--- Increments the number of all tested functions.
incNumAllInStats :: VState -> VState
incNumAllInStats vstate = vstate { numAllFuncs = numAllFuncs vstate + 1 }

--- Increments the number of operations with nonfail conditions.
incNumNFCInStats :: VState -> VState
incNumNFCInStats vstate = vstate { numNFCFuncs = numNFCFuncs vstate + 1 }

--- Increments the number of missing pattern tests.
incPatTestInStats :: VState -> VState
incPatTestInStats vstate = vstate { numPatTests = numPatTests vstate + 1 }

--- Increments the number of test of posibble failure calls.
incFailTestInStats :: VState -> VState
incFailTestInStats vstate = vstate { numFailTests = numFailTests vstate + 1 }

--- Adds a new typed FlatCurry program to the state.
addProgToState :: AProg TypeExpr -> VState -> VState
addProgToState prog vstate = vstate { currTAProgs = prog : currTAProgs vstate }

---------------------------------------------------------------------------
--- Selects the type declaration of a type constructor from the state.
tdeclOf :: VState -> QName -> Maybe TypeDecl
tdeclOf vst tcons@(mn,tc) =
  maybe Nothing
        (\p -> find (\td -> typeName td == tcons) (progTypes p))
        (find (\p -> progName p == mn) (currTAProgs vst))

---------------------------------------------------------------------------
