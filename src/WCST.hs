{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
module Main where

import Control.Applicative ((<$>))
import Control.Monad (forM_, liftM2)
import Data.Function (on)
import Data.List (isPrefixOf, sortBy, groupBy, nubBy)
import Data.Monoid (mconcat, (<>))
import Data.Ord (comparing)
import System.IO.Unsafe (unsafePerformIO)

import ClipIt (Clipping (..), getClippings, canonicalName)
import Hakyll
import Hakyll.Web.Tags
import Site.Compilers
import Site.Constants
import Site.Contexts
import Site.Rules
import Utils

wcst = "we-can-solve-this/"

feedConfiguration = FeedConfiguration
    { feedTitle       = "We Can Solve This"
    , feedDescription = "Musings on effective life strategies"
    , feedAuthorName  = "Sandy Maguire"
    , feedAuthorEmail = "sandy@sandymaguire.me"
    , feedRoot        = "http://sandymaguire.me/"
    }

main :: IO ()
main = do
    hakyll $ do
        tags <- buildTags (postsDir wcst) (fromCapture . fromGlob $ wcst ++ "tags/*.html")
        clipFiles <- fmap toFilePath <$> getMatches "clippings/*"

        let clippings = unsafePerformIO $ getClippings clipFiles
            clipBooks = sortAndGroup bookName clippings
            postCtxTags = postCtxWithTags tags

        templateRules wcst
        imageRules    wcst
        jsRules       wcst
        cssRules      wcst
        postRules     wcst postsDir "posts/" "blog/" postCtxTags
        archiveRules  wcst postsDir "blog/archives/" postCtxTags
        indexRules    wcst postCtxTags
        feedRules     wcst feedConfiguration
        tagRules      wcst tags

        forM_ clipBooks $ \book -> do
            let clipItems = sortBy (comparing added) book
                curBook = head clipItems
                name = canonicalName curBook
            create [fromFilePath $ wcst ++ "books/" ++ name] $ do
                route $ stripPrefix wcst <+> setExtension "html"
                compile $ do
                    let timeField name book = optionalConstField name
                                            . fmap showTime
                                            $ added book
                        ctx = mconcat
                            [ constField "title"    $ bookName curBook
                            , constField "author"   $ author curBook
                            , timeField "started"   $ curBook
                            , timeField "finished"  $ last clipItems
                            , listField "clippings"   clippingCtx (mapM makeItem clipItems)
                            , defaultContext
                            ]
                    contentCompiler wcst (fromFilePath $ wcst ++ "templates/book.html") ctx

        create [fromFilePath $ wcst ++ "books/index.html"] $ do
            route $ stripPrefix wcst
            compile $ do
                let ctx = mconcat
                        [ listField "books" clippingCtx
                            . mapM makeItem
                            . nubBy ((==) `on` liftM2 (,) bookName author)
                            . sortBy (comparing $ titleCompare . bookName)
                            $ map head clipBooks
                        , constField "title" "Index of Book Quotes"
                        , defaultContext
                        ]
                contentCompiler wcst (fromFilePath $ wcst ++ "templates/book-index.html") ctx

