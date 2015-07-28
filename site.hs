{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
import Data.Monoid (mappend, mconcat, (<>))
import Hakyll.Web.Tags
import qualified Data.Set as S
import qualified Data.Map as M
import Hakyll
import Text.Pandoc.Options
import Control.Applicative ((<$>))
import Control.Applicative (Alternative (..))
import Debug.Trace (trace, traceM)

import Control.Monad (forM, forM_, mapM_, liftM, liftM2)
import System.IO.Unsafe (unsafePerformIO)

import Data.Ord (comparing)
import Data.Function (on)
import Data.List (isPrefixOf, tails, findIndex, intercalate, sortBy, groupBy, nubBy)
import Data.Sequence (dropWhileR)
import System.FilePath (takeFileName)

import Data.Time.Format (parseTime, formatTime)
import System.Locale (defaultTimeLocale)

import Data.Time.Clock (UTCTime)

import ClipIt (Clipping (..), getClippings, canonicalName)


dateFormat = "%B %e, %Y"
postsDir = "posts/*"

postCtxWithTags :: Tags -> Context String
postCtxWithTags tags = tagsField "tags" tags `mappend` postCtx

getPrev :: [Identifier]
        -> ([Identifier] -> [Identifier] -> [(Identifier,Identifier)])
        -> Item String
        -> Compiler String
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
                    parseTime' fn = parseTime defaultTimeLocale "%Y-%m-%d"
                                  . intercalate "-"
                                  . take 3
                                  $ splitAll "-" fn
                in compare ((parseTime' fn1) :: Maybe UTCTime) ((parseTime' fn2) :: Maybe UTCTime)


setNextPrev :: [Identifier] -> Context String -> Context String
setNextPrev posts ctx =
    mconcat
        [ field "prev" $ getPrev posts zip
        , field "next" $ getPrev posts (flip zip)
        , ctx
        ]


showTrace :: (Show a) => a -> a
showTrace = trace =<< show

main :: IO ()
main = hakyll $ do
    tags <- buildTags postsDir (fromCapture "tags/*.html")
    clipFiles <- fmap toFilePath <$> getMatches "clippings/*"
    let clippings = unsafePerformIO $ getClippings clipFiles
        clipBooks = groupBy ((==) `on` bookName) clippings

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

    match postsDir $ do
        postMatches <- getMatches postsDir
        route $ gsubRoute (show postsDir) (const "blog/")
            <> gsubRoute "/[0-9]{4}-[0-9]{2}-[0-9]{2}-" (const "/")
            <> cruftlessRoute
        compile $ do
            pandocMathCompiler
                >>= loadAndApplyTemplate "templates/post.html"
                    (setNextPrev postMatches postCtxTags)
                >>= saveSnapshot "content"
                >>= loadAndApplyTemplate "templates/default.html" postCtxTags
                >>= relativizeUrls

    create ["blog/archive.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll postsDir
            let archiveCtx = mconcat
                    [ listField "posts" postCtxTags (return posts)
                    , constField "title" "Archives"
                    , defaultContext
                    ]

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

    forM_ clipBooks $ \book -> do
        let clipItems = sortBy (comparing added) book
            curBook = head book
            name = canonicalName curBook

        create [fromFilePath $ "books/" ++ name] $ do
            route $ setExtension "html"
            compile $ do
                let ctx = mconcat
                        [ constField "title" $ bookName curBook
                        , optionalConstField "started" . fmap showTime $ added curBook
                        , optionalConstField "finished" . fmap showTime . added $ last book
                        , constField "author" $ author curBook
                        , listField "clippings" clippingCtx (mapM makeItem clipItems)
                        , defaultContext
                        ]

                makeItem ""
                    >>= loadAndApplyTemplate "templates/book.html" ctx
                    >>= loadAndApplyTemplate "templates/default.html" ctx
                    >>= relativizeUrls

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

            makeItem ""
                >>= loadAndApplyTemplate "templates/book-index.html" ctx
                >>= loadAndApplyTemplate "templates/default.html" ctx
                >>= relativizeUrls


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
    let mathExtensions = [ Ext_tex_math_dollars
                         , Ext_tex_math_double_backslash
                         , Ext_latex_macros
                         ]
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

optionalConstField :: String -> Maybe String -> Context a
optionalConstField key Nothing =  field key $ return empty
optionalConstField key (Just x) = field key . const $ return x

optionalField
    :: String
    -> (Item a -> Maybe (Compiler String))
    -> Context a
optionalField key f = field key $ \i ->
    case f i of
    Nothing    -> empty
    Just value -> value

liftClip :: (Clipping -> String) -> Item Clipping -> Compiler String
liftClip f = return . f . itemBody

clippingCtx :: Context Clipping
clippingCtx = mconcat
    [ field "body" $ liftClip contents
    , field "url"  $ liftClip canonicalName
    , field "author"  $ liftClip author
    , field "bookName"  $ liftClip bookName
    ]

postCtx :: Context String
postCtx = mconcat
    [ dateField "date" dateFormat
    , defaultContext
    ]

showTime ::  UTCTime -> String
showTime = formatTime defaultTimeLocale dateFormat

titleCompare :: String -> String
titleCompare s =
    if isPrefixOf "The " s
       then drop 4 s
       else s

