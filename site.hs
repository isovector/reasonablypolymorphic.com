{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
import           Data.Monoid (mappend, mconcat)
import           Hakyll.Web.Tags
import qualified Data.Set as S
import           Hakyll
import           Text.Pandoc.Options
import          Control.Applicative ((<$>))
import          Debug.Trace (trace)
import Control.Applicative (Alternative (..))
import Debug.Trace (trace, traceM)

import Control.Monad (forM, mapM_)
import System.IO.Unsafe (unsafePerformIO)

import Data.Function (on)
import Data.List (isPrefixOf, tails, findIndex, intercalate, sortBy, groupBy)
import System.FilePath (takeFileName)

import Data.Time.Format (parseTime)
import System.Locale (defaultTimeLocale)
import Data.Time.Clock (UTCTime)

import ClipIt (Clipping (..), getClippings)


(<+>) :: Routes -> Routes -> Routes
(<+>) = composeRoutes

postsDir = "posts/*"

postCtxWithTags :: Tags -> Context String
postCtxWithTags tags = tagsField "tags" tags `mappend` postCtx

getPrev :: [Identifier] -> ([Identifier] -> [Identifier] -> [(Identifier,Identifier)]) -> Item String -> Compiler String
getPrev posts f me = do
    let ids = sortIdentifiersByDate posts
    case lookup (itemIdentifier me) $ f ids (tail ids) of
      Just i  -> (fmap (maybe empty $ toUrl) . getRoute) i
      Nothing -> empty

sortIdentifiersByDate :: [Identifier] -> [Identifier]
sortIdentifiersByDate identifiers =
    reverse $ sortBy byDate identifiers
        where
            byDate id1 id2 =
                let fn1 = takeFileName $ toFilePath id1
                    fn2 = takeFileName $ toFilePath id2
                    parseTime' fn = parseTime defaultTimeLocale "%Y-%m-%d" $ intercalate "-" $ take 3 $ splitAll "-" fn
                in compare ((parseTime' fn1) :: Maybe UTCTime) ((parseTime' fn2) :: Maybe UTCTime)


setNextPrev :: [Identifier] -> Context String -> Context String
setNextPrev posts ctx =
    mconcat
        [ field "prev" $ getPrev posts zip
        , field "next" $ getPrev posts (flip zip)
        , ctx
        ]




headMay :: [a] -> Maybe a
headMay []    = Nothing
headMay (a:_) = Just a

showTrace :: (Show a) => a -> a
showTrace = trace =<< show

main :: IO ()
main = hakyll $ do
    tags <- buildTags postsDir (fromCapture "tags/*.html")
    clipFiles <- fmap toFilePath <$> getMatches "clippings/*"
    mapM_ traceM clipFiles
    let clippings = unsafePerformIO $ getClippings clipFiles
        clipBooks = groupBy ((==) `on` book) clippings

        postCtxTags = postCtxWithTags tags

    match "images/**" $ do
        route   idRoute
        compile copyFileCompiler

    match "js/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    forM clipBooks $ \books ->
        create [fromFilePath $ "book/" ++ (book $ head books)] $ do
            route $ setExtension "html"
            compile $ do
                makeItem . show $ length books

    match postsDir $ do
        postMatches <- getMatches postsDir
        route $ gsubRoute (show postsDir) (const "blog/")
            <+> gsubRoute "/[0-9]{4}-[0-9]{2}-[0-9]{2}-" (const "/")
            <+> cruftlessRoute
        compile $ do
            pandocMathCompiler
                >>= loadAndApplyTemplate "templates/post.html" (setNextPrev postMatches postCtxTags)
                >>= saveSnapshot "content"
                >>= loadAndApplyTemplate "templates/default.html" postCtxTags
                >>= relativizeUrls

    create ["blog/archive.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll postsDir
            let archiveCtx =
                    listField "posts" postCtxTags (return posts) `mappend`
                    constField "title" "Archives"            `mappend`
                    defaultContext

            makeItem ""
                >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
                >>= loadAndApplyTemplate "templates/default.html" archiveCtx
                >>= relativizeUrls

    create ["index.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll postsDir
            let indexCtx = mconcat
                    [ listField "posts" postCtxTags (return $ take 1 posts)
                    , constField "title" "Home"
                    , defaultContext
                    ]

            makeItem ""
                >>= loadAndApplyTemplate "templates/index.html" indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls


    match "templates/*" $ compile templateCompiler

    tagsRules tags $ \tag pattern -> do
        let title = "Posts tagged \"" ++ tag ++ "\""
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll pattern
            let ctx = constField "title" title
                        `mappend` listField "posts" postCtx (return posts)
                        `mappend` defaultContext

            makeItem ""
                >>= loadAndApplyTemplate "templates/tag.html" ctx
                >>= loadAndApplyTemplate "templates/default.html" ctx
                >>= relativizeUrls

    create ["atom.xml"] $ feedRoute renderAtom
    create ["feed.rss"] $ feedRoute renderRss


feedRoute render = do
    route idRoute
    compile $ do
        let feedCtx = postCtx `mappend` bodyField "description"
        posts <- fmap (take 10) . recentFirst =<<
            loadAllSnapshots postsDir "content"
        render feedConfiguration feedCtx posts


feedConfiguration :: FeedConfiguration
feedConfiguration = FeedConfiguration
    { feedTitle       = "We Can Solve This"
    , feedDescription = "Musings on effective life strategies"
    , feedAuthorName  = "Sandy Maguire"
    , feedAuthorEmail = "sandy@sandymaguire.me"
    , feedRoot        = "http://sandymaguire.me/"
    }


pandocMathCompiler =
    let mathExtensions = [Ext_tex_math_dollars, Ext_tex_math_double_backslash,
                          Ext_latex_macros]
        defaultExtensions = writerExtensions defaultHakyllWriterOptions
        newExtensions = foldr S.insert defaultExtensions mathExtensions
        writerOptions = defaultHakyllWriterOptions
                          { writerExtensions = newExtensions
                          , writerHTMLMathMethod = MathJax ""
                          }
    in pandocCompilerWith defaultHakyllReaderOptions writerOptions


----

cruftlessRoute :: Routes
cruftlessRoute = setExtension ""

--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext

