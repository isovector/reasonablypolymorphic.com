{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
module Site.Compilers where

import Data.Set (insert)
import Text.Pandoc.Options

import Hakyll


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
    in pandocCompilerWith defaultHakyllReaderOptions writerOptions

