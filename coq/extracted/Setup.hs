import Distribution.Simple
import Distribution.Simple.Setup
import Distribution.Simple.Utils
import Distribution.PackageDescription
import Distribution.Verbosity

import Control.Exception
import System.Directory

main = defaultMainWithHooks simpleUserHooks
       { preConf = doConf
       , postClean = doClean
       }

doConf :: Args -> ConfigFlags -> IO HookedBuildInfo
doConf args f = do
   let v = fromFlag $ configVerbosity f
   coqcPath <- findExecutable "coqc"
   case coqcPath of
     Just coqc -> do
       putStrLn "Extracting implementation from Coq sources" 
       bracket_ (setCurrentDirectory "ext")
                (setCurrentDirectory "..")
                (rawSystemExit v coqc ["-I", "../..", "SF_extract.v"])
     Nothing -> do
       putStrLn "Warning! 'coqc' not found, not extracting from Coq sources" 
   preConf simpleUserHooks args f

doClean :: Args -> CleanFlags -> PackageDescription -> () -> IO ()
doClean args f pdesc u = do
   mapM_ removeFile =<< matchFileGlob "ext/*.hs"
   mapM_ removeFile =<< matchFileGlob "ext/*.vo"
   mapM_ removeFile =<< matchFileGlob "ext/*.glob"
   postClean simpleUserHooks args f pdesc u
