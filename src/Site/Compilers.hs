{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Site.Compilers where

import           Control.Monad
import           Data.ByteString (ByteString)
import qualified Data.ByteString as B
import           Data.Set (insert)
import           Data.String.Conv
import           Hakyll
import           System.Directory
import           System.FilePath
import           System.IO
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
pandocMathCompiler =
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
    in pandocCompilerWithTransformM defaultHakyllReaderOptions writerOptions transform

evalBlock :: P.Block -> IO P.Block
evalBlock cb@(P.CodeBlock (name, classes, vs) contents)
  | elem "circuit" classes = do
      compileExistingSource $ toS contents
      contents' :: String <- toS <$> runProgram "/home/bootstrap"
      return $ P.Para . return $ P.Image (name, classes, vs) [] (contents', "")
  | otherwise = return cb
evalBlock x = return x

transform :: P.Pandoc -> Compiler P.Pandoc
transform doc = unsafeCompiler $ walkM evalBlock doc

runProgram :: FilePath -> IO ByteString
runProgram dir = do
    (Just inh, Just outh, Just errh, pid) <-
        createProcess (proc (dir </> "done") []) {
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

compileExistingSource :: ByteString -> IO Bool
compileExistingSource source =
    withSystemTempDirectory "codeworld" $ \tmpdir -> do
        B.writeFile (tmpdir </> "program.hs") source
        let ghcArgs = [ "exec", "ghc", tmpdir </> "program.hs", "--", "-o", "/home/bootstrap/done", "-package", "circuitry", "-package", "diagrams" ]
        runCompiler "/home/bootstrap/Projects/blog" ghcArgs -- >>= \output -> do
        return True
            -- B.writeFile (programId) output
            -- let target = tmpdir </> "program.jsexe" </> "all.js"
            -- hasTarget <- doesFileExist target
            -- when hasTarget $
            --     copyFile target (programId)
            -- return hasTarget

