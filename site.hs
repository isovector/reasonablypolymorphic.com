{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
import           Data.Monoid (mappend, mconcat)
import           Hakyll.Web.Tags
import qualified Data.Set as S
import           Hakyll
import           Text.Pandoc.Options
import          Control.Applicative ((<$>))
import          Debug.Trace (trace)
import Control.Applicative (Alternative (..))


import Data.List (isPrefixOf, tails, findIndex, intercalate, sortBy)
import System.FilePath (takeFileName)

import Data.Time.Format (parseTime)
import System.Locale (defaultTimeLocale)
import Data.Time.Clock (UTCTime)

import ClipIt (Clipping (..), parseClippings)


(<+>) :: Routes -> Routes -> Routes
(<+>) = composeRoutes


postCtxWithTags :: Tags -> Context String
postCtxWithTags tags = tagsField "tags" tags `mappend` postCtx

getPrev :: ([Identifier] -> [Identifier] -> [(Identifier,Identifier)]) -> Item String -> Compiler String
getPrev f me = do
    posts <- getMatches "posts/*"
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


setNextPrev :: Context String -> Context String
setNextPrev ctx =
    mconcat
        [ field "prev" $ getPrev zip
        , field "next" $ getPrev (flip zip)
        , ctx
        ]




headMay :: [a] -> Maybe a
headMay []    = Nothing
headMay (a:_) = Just a

showTrace :: (Show a) => a -> a
showTrace = trace =<< show

main :: IO ()
main = putStrLn
     $ show
     $ parseClippings
     $ unlines
        [ "I Will Teach You to Be Rich (Sethi Ramit)"
        , "- Highlight on Page 10 | Loc. 153-54  | Added on Sunday, March 29, 2015, 04:11 PM"
        , ""
        , "Who wins at the end of the day? The self-satisfied people who heatedly debate some obscure details? Or the people who sidestep the entire debate and get started?"
        , "=========="
        , "I Will Teach You to Be Rich (Sethi Ramit)"
        , "- Highlight on Page 13 | Loc. 188-89  | Added on Sunday, March 29, 2015, 04:13 PM"
        , ""
        , "“Our education system doesn’t teach this,” people whine. It’s easy for people in their twenties to wish that their colleges had offered some personal-finance training. Guess what? Most colleges do offer those classes. You just didn’t attend!"
        , "=========="
        , "I Will Teach You to Be Rich (Sethi Ramit)"
        , "- Highlight on Page 14 | Loc. 204-5  | Added on Sunday, March 29, 2015, 04:14 PM"
        , ""
        , "Listen up, crybabies: This isn’t your grandma’s house and I’m not going to bake you cookies and coddle you. A lot of your financial problems are caused by one person: you."
        , "=========="
        , "I Will Teach You to Be Rich (Sethi Ramit)"
        , "- Highlight on Page 15 | Loc. 229-30  | Added on Sunday, March 29, 2015, 04:16 PM"
        , ""
        , "Getting started is more important than becoming an expert."
        , "=========="
        ]
        {-hakyll $ do
    tags <- buildTags "posts/*" (fromCapture "tags/*.html")
    let postCtxTags = postCtxWithTags tags

    match "images/**" $ do
        route   idRoute
        compile copyFileCompiler

    match "js/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    match "posts/*" $ do
        route $ gsubRoute "posts/" (const "blog/")
            <+> gsubRoute "/[0-9]{4}-[0-9]{2}-[0-9]{2}-" (const "/")
            <+> cruftlessRoute
        compile $ do
            pandocMathCompiler
                >>= loadAndApplyTemplate "templates/post.html" (setNextPrev postCtxTags)
                >>= saveSnapshot "content"
                >>= loadAndApplyTemplate "templates/default.html" postCtxTags
                >>= relativizeUrls

    -- TODO: make this run octo-clip-it
    match "books/*.markdown" $ do
        route $ setExtension "html"
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/post.html"    defaultContext
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    create ["blog/archive.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll "posts/*"
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
            posts <- recentFirst =<< loadAll "posts/*"
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
    -- -}

feedRoute render = do
    route idRoute
    compile $ do
        let feedCtx = postCtx `mappend` bodyField "description"
        posts <- fmap (take 10) . recentFirst =<<
            loadAllSnapshots "posts/*" "content"
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
