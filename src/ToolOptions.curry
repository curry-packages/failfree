-------------------------------------------------------------------------
--- The options of the non-failing analysis tool.
---
--- @author Michael Hanus
--- @version April 2018
-------------------------------------------------------------------------

module ToolOptions
  ( Options(..), defaultOptions, processOptions
  , whenStatus, printWhenStatus, printWhenIntermediate, printWhenAll
  )
 where

import Distribution      ( stripCurrySuffix )
import GetOpt
import ReadNumeric       ( readNat )
import System            ( exitWith )

data Options = Options
  { optVerb    :: Int    -- verbosity (0: quiet, 1: status, 2: interm, 3: all)
  , optHelp    :: Bool   -- if help info should be printed
  , optError   :: Bool   -- should `error` be considered as a failing function?
  , optStrict  :: Bool   -- verify precondition w.r.t. strict evaluation?
                         -- in this case, we assume that all operations are
                         -- strictly evaluated which might give better results
                         -- but not not be correct if some argument is not
                         -- demanded (TODO: add demand analysis to make it
                         -- safe and powerful)
  }

defaultOptions :: Options
defaultOptions = Options 1 False False False

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
usageText = usageInfo ("Usage: curry-ctopt [options] <module names>\n") options
  
-- Definition of actual command line options.
options :: [OptDescr (Options -> Options)]
options =
  [ Option "h?" ["help"]  (NoArg (\opts -> opts { optHelp = True }))
           "print help and exit"
  , Option "q" ["quiet"] (NoArg (\opts -> opts { optVerb = 0 }))
           "run quietly (no output, only exit code)"
  , Option "v" ["verbosity"]
            (OptArg (maybe (checkVerb 2) (safeReadNat checkVerb)) "<n>")
            "verbosity level:\n0: quiet (same as `-q')\n1: show status messages (default)\n2: show intermediate results (same as `-v')\n3: show all intermediate results and more details"
  , Option "e" ["error"] (NoArg (\opts -> opts { optError = True }))
           "consider 'Prelude.error' as a failing operation"
  , Option "s" ["strict"] (NoArg (\opts -> opts { optStrict = True }))
           "check contracts w.r.t. strict evaluation strategy"
  ]
 where
  safeReadNat opttrans s opts =
   let numError = error "Illegal number argument (try `-h' for help)"
   in maybe numError
            (\ (n,rs) -> if null rs then opttrans n opts else numError)
            (readNat s)

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
