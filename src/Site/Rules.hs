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
        route   $ stripPrefix prefix
        compile copyFileCompiler

jsRules :: String -> Rules ()
jsRules prefix =
    match (fromGlob $ prefix ++ "js/*") $ do
        route   $ stripPrefix prefix
        compile copyFileCompiler

cssRules :: String -> Rules ()
cssRules prefix =
    match (fromGlob $ prefix ++ "css/*") $ do
        route   $ stripPrefix prefix
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
                >>= loadAndApplyTemplate (fromFilePath $ prefix ++ "templates/post.html")
                    (setNextPrev postMatches postCtxTags)
                >>= saveSnapshot "content"
                >>= loadAndApplyTemplate (fromFilePath $ prefix ++ "templates/default.html") postCtxTags
                >>= relativizeUrls

archiveRules :: String -> Context String -> Rules ()
archiveRules prefix postCtxTags =
    create [fromFilePath $ prefix ++ "blog/archives/index.html"] $ do
        route $ stripPrefix prefix
        compile $ do
            posts <- recentFirst =<< loadAll (postsDir prefix)
            let archiveCtx = mconcat
                    [ listField "posts" postCtxTags (return posts)
                    , constField "title" "Archives"
                    , defaultContext
                    ]
            contentCompiler prefix (fromFilePath $ prefix ++ "templates/archive.html") archiveCtx

indexRules :: String -> Context String -> Rules ()
indexRules prefix postCtxTags =
    create [fromFilePath $ prefix ++ "index.html"] $ do
        route $ stripPrefix prefix
        compile $ do
            posts <- recentFirst =<< loadAll (postsDir prefix)
            let indexCtx = mconcat
                    [ listField "posts" postCtxTags (return $ take 1 posts)
                    , constField "title" "Home"
                    , defaultContext
                    ]
            contentCompiler prefix (fromFilePath $ prefix ++ "templates/index.html") indexCtx

feedRules :: String -> FeedConfiguration -> Rules ()
feedRules prefix feedConfiguration = do
    create [fromFilePath $ prefix ++ "atom.xml"] $ feedRoute renderAtom prefix feedConfiguration
    create [fromFilePath $ prefix ++ "feed.rss"] $ feedRoute renderRss prefix feedConfiguration

tagRules :: String -> Tags -> Rules ()
tagRules prefix tags =
    tagsRules tags $ \tag pattern -> do
        let title = "Posts tagged \"" ++ tag ++ "\""
        route $ stripPrefix prefix
        compile $ do
            posts <- recentFirst =<< loadAll pattern
            let ctx = mconcat
                    [ constField "title" title
                    , listField "posts" postCtx (return posts)
                    , defaultContext
                    ]
            contentCompiler prefix (fromFilePath $ prefix ++ "templates/tag.html") ctx

templateRules :: String -> Rules ()
templateRules prefix =
    match (fromGlob $ prefix ++ "templates/*") $ compile templateCompiler

feedRoute render prefix feedConfiguration = do
    route $ stripPrefix prefix
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

stripPrefix prefix = gsubRoute prefix (const "")

