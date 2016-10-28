{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Site.Compilers where

import           Data.Set (insert)
import           Hakyll
import           Language.Haskell.Interpreter
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

evalBlock :: P.Block -> Interpreter P.Block
evalBlock cb@(P.CodeBlock (name, classes, vs) contents)
  | elem "circuit" classes = do
      r <- eval contents
      let contents' = contents ++ " => " ++ r
      return $ P.CodeBlock (name, classes, vs) contents'
  | otherwise = return cb
evalBlock x = return x

transform :: P.Pandoc -> Compiler P.Pandoc
transform doc = do
    Right x <- unsafeCompiler . runInterpreter $ do
        let modules = []
        let imports = [ "*" ++ m | m <- modules]
        loadModules imports

        getLoadedModules >>= setTopLevelModules
        setImports ["Prelude"]
        walkM evalBlock doc
    return x

