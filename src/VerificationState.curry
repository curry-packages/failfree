module VerificationState where

import FlatCurry.Annotated.Types

---------------------------------------------------------------------------
-- The global state of the verification process keeps some
-- statistical information and the programs that are already read (to
-- avoid multiple readings).
data VState = VState
  { failedFuncs :: [(String,String)] -- partially defined operations
                                     -- and their failing reason
  , numAllFuncs :: Int               -- number of analyzed operations
  , currTAProgs :: [AProg TypeExpr]  -- already read typed FlatCurry programs
  }

initVState :: VState
initVState = VState [] 0 []

--- Shows the statistics in human-readable format.
showStats :: VState -> String
showStats vstate =
  "\n\nNUMBER OF TESTED OPERATIONS: " ++ show (numAllFuncs vstate) ++ "\n" ++
  showStat "POSSIBLY FAILING OPERATIONS" (failedFuncs vstate) ++
  (if isVerified vstate then "\nNON-FAILURE VERIFICATION SUCCESSFUL!" else "")
 where
  showStat t fs =
    if null fs
      then ""
      else "\n" ++ t ++ ":\n" ++
           unlines (map (\ (fn,reason) -> fn ++ " (" ++ reason ++ ")")
                        (reverse fs))

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

--- Adds a new typed FlatCurry program to the state.
addProgToState :: AProg TypeExpr -> VState -> VState
addProgToState prog vstate = vstate { currTAProgs = prog : currTAProgs vstate }

---------------------------------------------------------------------------
