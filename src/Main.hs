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

(<+>) :: Routes -> Routes -> Routes
(<+>) = composeRoutes

main :: IO ()
main = hakyll $ do
    tags <- buildTags postsDir (fromCapture "tags/*.html")
    clipFiles <- fmap toFilePath <$> getMatches "clippings/*"

    let clippings = unsafePerformIO $ getClippings clipFiles
        clipBooks = groupBy ((==) `on` bookName) clippings
        postCtxTags = postCtxWithTags tags


    -- ROUTES BEGIN HERE --


    match "images/**" $ do
        route   idRoute
        compile copyFileCompiler


    match "js/*" $ do
        route   idRoute
        compile copyFileCompiler


    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler


    match postsDir $ do
        postMatches <- getMatches postsDir
        route $   gsubRoute "posts/" (const "blog/")
              <+> gsubRoute "/[0-9]{4}-[0-9]{2}-[0-9]{2}-" (const "/")
              <+> cruftlessRoute
        compile $ do
            pandocMathCompiler
                >>= loadAndApplyTemplate "templates/post.html"
                    (setNextPrev postMatches postCtxTags)
                >>= saveSnapshot "content"
                >>= loadAndApplyTemplate "templates/default.html" postCtxTags
                >>= relativizeUrls


    create ["blog/archives/index.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll postsDir
            let archiveCtx = mconcat
                    [ listField "posts" postCtxTags (return posts)
                    , constField "title" "Archives"
                    , defaultContext
                    ]
            contentCompiler "templates/archive.html" archiveCtx


    create ["index.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll postsDir
            let indexCtx = mconcat
                    [ listField "posts" postCtxTags (return $ take 1 posts)
                    , constField "title" "Home"
                    , defaultContext
                    ]
            contentCompiler "templates/index.html" indexCtx


    forM_ clipBooks $ \book -> do
        let clipItems = sortBy (comparing added) book
            curBook = head book
            name = canonicalName curBook

        create [fromFilePath $ "books/" ++ name] $ do
            route $ setExtension "html"
            compile $ do
                let timeField name book = optionalConstField name
                                        . fmap showTime
                                        $ added book
                    ctx = mconcat
                        [ constField "title"    $ bookName curBook
                        , constField "author"   $ author curBook
                        , timeField "started"   $ curBook
                        , timeField "finished"  $ last book
                        , listField "clippings"   clippingCtx (mapM makeItem clipItems)
                        , defaultContext
                        ]
                contentCompiler "templates/book.html" ctx


    create ["books/index.html"] $ do
        route $ idRoute
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
            contentCompiler "templates/book-index.html" ctx


    create ["atom.xml"] $ feedRoute renderAtom
    create ["feed.rss"] $ feedRoute renderRss


    -- ROUTES END HERE --


    match "templates/*" $ compile templateCompiler

    tagsRules tags $ \tag pattern -> do
        let title = "Posts tagged \"" ++ tag ++ "\""
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll pattern
            let ctx = mconcat
                    [ constField "title" title
                    , listField "posts" postCtx (return posts)
                    , defaultContext
                    ]
            contentCompiler "templates/tag.html" ctx

feedRoute render = do
    route idRoute
    compile $ do
        let feedCtx = postCtx <> bodyField "description"
        posts <- fmap (take 10) . recentFirst =<<
            loadAllSnapshots postsDir "content"
        render feedConfiguration feedCtx posts


--------------------------------------------------------------------------------

cruftlessRoute :: Routes
cruftlessRoute = setExtension ""

titleCompare :: String -> String
titleCompare s =
    if isPrefixOf "The " s
       then drop 4 s
       else s

