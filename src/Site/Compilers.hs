{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Site.Compilers where

import           Control.Monad
import           Data.ByteString (ByteString)
import qualified Data.ByteString as B
import           Data.IORef
import Data.Char (toUpper, isLetter)
import Data.List (intercalate)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (insert)
import           Data.String.Conv
import Data.String.Here
import           Hakyll
import           System.Directory
import           System.FilePath
import           System.IO
import System.IO.Unsafe (unsafeInterleaveIO)
import           System.IO.Temp (withSystemTempDirectory)
import           System.Process
import qualified Text.Pandoc as P
import           Text.Pandoc.Options
import           Text.Pandoc.Walk (walkM)


contentCompiler :: String -> Identifier -> Context String -> Compiler (Item String)
contentCompiler prefix t c =
    makeItem ""
    >>= loadAndApplyTemplate t c
    >>= loadAndApplyTemplate (fromFilePath $ prefix ++ "templates/default.html") c
    >>= relativizeUrls

pandocMathCompiler :: Compiler (Item String)
pandocMathCompiler = do
    let mathExtensions =
            [ Ext_tex_math_dollars
            , Ext_tex_math_double_backslash
            , Ext_latex_macros
            ]
        defaultExtensions = writerExtensions defaultHakyllWriterOptions
        newExtensions = foldr insert defaultExtensions mathExtensions
        writerOptions = defaultHakyllWriterOptions
            { writerExtensions = newExtensions
            , writerHTMLMathMethod = MathJax ""
            }
    ref <- unsafeCompiler $ newIORef M.empty
    pandocCompilerWithTransformM defaultHakyllReaderOptions writerOptions (transform ref)

findBlock :: IORef (Map String String) -> P.Block -> IO P.Block
findBlock ref cb@(P.CodeBlock (name, classes, vs) contents)
  | name /= "" = do
      modifyIORef ref $ M.insert name contents
      return cb
  | otherwise = return cb
findBlock _ x = return x

evalBlock :: P.Block -> IO P.Block
evalBlock cb@(P.CodeBlock (name, classes, vs) contents)
  | name /= "" = do
      contents' :: String <- toS <$> runProgram "/home/bootstrap" (circId name)
      return $ P.Para . return $ P.Image (name, "circuit" : classes, vs) [] (contents', "")
  | otherwise = return cb
evalBlock x = return x

transform :: IORef (Map String String) -> P.Pandoc -> Compiler P.Pandoc
transform ref doc = unsafeCompiler $ do
    x <- walkM (findBlock ref) doc
    m <- readIORef ref
    unless (M.null m) $ void $ compileExistingSource m
    walkM evalBlock doc

runProgram :: FilePath -> String -> IO ByteString
runProgram dir circ = do
    (Just inh, Just outh, Just errh, pid) <-
        createProcess (proc (dir </> "done") [circ]) {
            cwd       = Just dir,
            std_in    = CreatePipe,
            std_out   = CreatePipe,
            std_err   = CreatePipe,
            close_fds = True }

    hClose inh
    result <- B.hGetContents outh
    hClose errh

    terminateProcess pid
    _ <- waitForProcess pid

    return result

runCompiler :: FilePath -> [String] -> IO ByteString
runCompiler dir args = do
    (Just inh, Just outh, Just errh, pid) <-
        createProcess (proc "stack" args) {
            cwd       = Just dir,
            std_in    = CreatePipe,
            std_out   = CreatePipe,
            std_err   = CreatePipe,
            close_fds = True }

    hClose inh
    result <- B.hGetContents errh
    hClose outh

    terminateProcess pid
    _ <- waitForProcess pid

    B.putStrLn result
    return result

compileExistingSource :: Map String String -> IO Bool
compileExistingSource sources =
    withSystemTempDirectory "codeworld" $ \tmpdir' -> do
        let tmpdir = "/home/bootstrap/"
        B.writeFile (tmpdir </> "program.hs") $ toS $ mkSrc sources
        let ghcArgs = [ "exec", "ghc", tmpdir </> "program.hs", "--", "-o", "/home/bootstrap/done", "-package", "circuitry", "-package", "diagrams" ]
        runCompiler "/home/bootstrap/Projects/blog" ghcArgs -- >>= \output -> do
        return True

circId :: String -> String
circId = fmap toUpper . filter isLetter

mkCirc :: (String, String) -> String
mkCirc (name, src) = [iTrim|
circuits ${circId name} = circuit
  where
${unlines . fmap ("    " ++) $ lines src}|]

mkSrc :: Map String String -> String
mkSrc circs = [iTrim|
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Main where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as C8
import Data.Typeable
import Control.Arrow (first, second)
import Control.Monad
import Diagrams.TwoD.Arrow
import Diagrams.TwoD.Arrowheads
import Diagrams.Prelude hiding (anon)
import Diagrams.TwoD.Shapes
import Diagrams.TwoD.Layout.Constrained ((=.=), constrainWith, xOf, yOf, along)
import Diagrams.TwoD.Vector

import Circuitry
import Circuitry.Backend
import Circuitry.Gates
import Circuitry.Machinery
import Circuitry.Misc
import Circuitry.Types

import System.Environment

data MyDiagrams = ${intercalate "|" . fmap circId $ M.keys circs} deriving Read

circuits :: MyDiagrams -> Diagram B
${intercalate "\n" . fmap mkCirc $ M.assocs circs }

main :: IO ()
main = do
  diagram <- read . head <$> getArgs
  C8.putStrLn $ toDataURL $ frame 0.25 $ circuits diagram
|]

