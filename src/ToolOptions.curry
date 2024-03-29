-------------------------------------------------------------------------
--- The options of the contract verification tool together with some
--- related operations.
---
--- @author Michael Hanus
--- @version May 2021
-------------------------------------------------------------------------

module ToolOptions
  ( Options(..), defaultOptions, processOptions
  , whenStatus, printWhenStatus, printWhenIntermediate, printWhenAll
  )
 where

import Control.Monad         ( when, unless )
import Data.Char             ( toUpper )
import System.Console.GetOpt
import Numeric               ( readNat )
import System.Process        ( exitWith )

import System.CurryPath      ( stripCurrySuffix )

data Options = Options
  { optVerb    :: Int    -- verbosity (0: quiet, 1: status, 2: interm, 3: all)
  , optHelp    :: Bool   -- if help info should be printed
  , optName    :: String -- show only the name of a nonfail condition
  , optError   :: Bool   -- should `error` be considered as a failing function?
  , optRec     :: Bool   -- recursive, i.e., verify imported modules first?
  , optContract:: Bool   -- consider pre/postconditions for verification?
  , optStrict  :: Bool   -- verify precondition w.r.t. strict evaluation?
                         -- in this case, we assume that all operations are
                         -- strictly evaluated which might give better results
                         -- but not not be correct if some argument is not
                         -- demanded (TODO: add demand analysis to make it
                         -- safe and powerful)
  , optTime    :: Bool   -- show elapsed verification time?
  }

defaultOptions :: Options
defaultOptions = Options 1 False "" False False False False False

--- Process the actual command line argument and return the options
--- and the name of the main program.
processOptions :: String -> [String] -> IO (Options,[String])
processOptions banner argv = do
  let (funopts, args, opterrors) = getOpt Permute options argv
      opts = foldl (flip id) defaultOptions funopts
  unless (null opterrors)
         (putStr (unlines opterrors) >> printUsage >> exitWith 1)
  when (optHelp opts) (printUsage >> exitWith 0)
  return (opts, map stripCurrySuffix args)
 where
  printUsage = putStrLn (banner ++ "\n" ++ usageText)

-- Help text
usageText :: String
usageText =
  usageInfo ("Usage: curry-failfree [options] <module names>\n") options

-- Definition of actual command line options.
options :: [OptDescr (Options -> Options)]
options =
  [ Option "h?" ["help"]
           (NoArg (\opts -> opts { optHelp = True }))
           "print help and exit"
  , Option "n" ["name"]
            (ReqArg (\s opts -> opts { optName = s }) "<f>")
            "show only the name of a non-fail condition"
  , Option "q" ["quiet"]
           (NoArg (\opts -> opts { optVerb = 0 }))
           "run quietly (no output, only exit code)"
  , Option "v" ["verbosity"]
            (OptArg (maybe (checkVerb 2) (safeReadNat checkVerb)) "<n>")
            "verbosity level:\n0: quiet (same as `-q')\n1: show status messages (default)\n2: show intermediate results (same as `-v')\n3: show all details (e.g., SMT scripts)"
  , Option "e" ["error"]
           (NoArg (\opts -> opts { optError = True }))
           "consider 'Prelude.error' as a failing operation"
  , Option "r" ["recursive"]
           (NoArg (\opts -> opts { optRec = True }))
           "recursive, i.e., verify imported modules first"
  , Option "c" ["contract"]
            (NoArg (\opts -> opts { optContract = True }))
           "consider contracts (pre/postcondition) for verification"
  , Option "s" ["strict"]
           (NoArg (\opts -> opts { optStrict = True }))
           "check contracts w.r.t. strict evaluation strategy"
  , Option "t" ["time"]
           (NoArg (\opts -> opts { optTime = True }))
           "show total verification time for each module"
  ]
 where
  safeReadNat opttrans s opts = case readNat s of
    [(n,"")] -> opttrans n opts
    _        -> error "Illegal number argument (try `-h' for help)"

  checkVerb n opts = if n>=0 && n<4
                       then opts { optVerb = n }
                       else error "Illegal verbosity level (try `-h' for help)"

-------------------------------------------------------------------------

whenStatus :: Options -> IO () -> IO ()
whenStatus opts = when (optVerb opts > 0)

printWhenStatus :: Options -> String -> IO ()
printWhenStatus opts s = whenStatus opts (printWT s)

printWhenIntermediate :: Options -> String -> IO ()
printWhenIntermediate opts s =
  when (optVerb opts > 1) (printWT s)

printWhenAll :: Options -> String -> IO ()
printWhenAll opts s =
 when (optVerb opts > 2) (printWT s)

printWT :: String -> IO ()
printWT s = putStrLn $ s --"NON-FAILING ANALYSIS: " ++ s

---------------------------------------------------------------------------
