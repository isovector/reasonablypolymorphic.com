{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
module Site.Rules where

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
import Utils

(<+>) :: Routes -> Routes -> Routes
(<+>) = composeRoutes

imageRules :: String -> Rules ()
imageRules prefix =
    match (fromGlob $ prefix ++ "images/**") $ do
        route   idRoute
        compile copyFileCompiler

jsRules :: String -> Rules ()
jsRules prefix =
    match (fromGlob $ prefix ++ "js/*") $ do
        route   idRoute
        compile copyFileCompiler

cssRules :: String -> Rules ()
cssRules prefix =
    match (fromGlob $ prefix ++ "css/*") $ do
        route   idRoute
        compile compressCssCompiler

postRules :: String -> Context String -> Rules ()
postRules prefix postCtxTags =
    match (postsDir prefix) $ do
        postMatches <- getMatches $ postsDir prefix
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

archiveRules :: String -> Context String -> Rules ()
archiveRules prefix postCtxTags =
    create [fromFilePath $ prefix ++ "blog/archives/index.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll (postsDir prefix)
            let archiveCtx = mconcat
                    [ listField "posts" postCtxTags (return posts)
                    , constField "title" "Archives"
                    , defaultContext
                    ]
            contentCompiler "templates/archive.html" archiveCtx

indexRules :: String -> Context String -> Rules ()
indexRules prefix postCtxTags =
    create [fromFilePath $ prefix ++ "index.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll (postsDir prefix)
            let indexCtx = mconcat
                    [ listField "posts" postCtxTags (return $ take 1 posts)
                    , constField "title" "Home"
                    , defaultContext
                    ]
            contentCompiler "templates/index.html" indexCtx

feedRules :: String -> Rules ()
feedRules prefix = do
    create [fromFilePath $ prefix ++ "atom.xml"] $ feedRoute renderAtom prefix
    create [fromFilePath $ prefix ++ "feed.rss"] $ feedRoute renderRss prefix

tagRules :: String -> Tags -> Rules ()
tagRules prefix tags =
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

templateRules :: Rules ()
templateRules = match "templates/*" $ compile templateCompiler

feedRoute render prefix = do
    route idRoute
    compile $ do
        let feedCtx = postCtx <> bodyField "description"
        posts <- fmap (take 10) . recentFirst =<<
            loadAllSnapshots (postsDir prefix) "content"
        render feedConfiguration feedCtx posts

cruftlessRoute :: Routes
cruftlessRoute = setExtension ""

titleCompare :: String -> String
titleCompare s =
    if isPrefixOf "The " s
       then drop 4 s
       else s

