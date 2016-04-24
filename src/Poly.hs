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
        tags <- buildTags (postsDir poly) (fromCapture . fromGlob $ poly ++ "tags/*.html")
        let postCtxTags = postCtxWithTags tags
        templateRules
        imageRules   poly
        jsRules      poly
        cssRules     poly
        postRules    poly postCtxTags
        archiveRules poly postCtxTags
        indexRules   poly postCtxTags
        feedRules    poly feedConfiguration
        tagRules     poly tags

