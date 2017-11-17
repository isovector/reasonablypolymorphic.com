{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
module Main where

import Hakyll
import Hakyll.Web.Tags
import Site.Compilers
import Site.Constants
import Site.Contexts
import Site.Rules

poly = "reasonably-polymorphic/"

feedConfiguration = FeedConfiguration
    { feedTitle       = "Reasonably Polymorphic"
    , feedDescription = "Haskell"
    , feedAuthorName  = "Sandy Maguire"
    , feedAuthorEmail = "sandy@sandymaguire.me"
    , feedRoot        = "http://reasonablypolymorphic.com/"
    }

main :: IO ()
main = do
    hakyll $ do
        tags     <- buildTags (postsDir poly) (fromCapture . fromGlob $ poly ++ "tags/*.html")
        -- booktags <- buildTags (bookDir poly) (fromCapture . fromGlob $ poly ++ "book/tags/*.html")
        let postCtxTags = postCtxWithTags tags
            -- bookCtxTags = postCtxWithTags booktags
        templateRules poly
        imageRules    poly
        staticRules   poly
        jsRules       poly
        cssRules      poly
        postRules     poly postsDir "posts/" "blog/" postCtxTags
        archiveRules  poly postsDir "blog/archives/" postCtxTags
        postRules     poly miscDir "misc/" "" postCtx
        -- postRules     poly bookDir "httw/" "book/" bookCtxTags
        -- archiveRules  poly bookDir "book/" bookCtxTags
        -- indexRules    poly bookDir "book/" postCtxTags
        indexRules    poly postsDir "" postCtxTags
        feedRules     poly feedConfiguration
        tagRules      poly tags
        -- tagRules      poly booktags

