{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}

module Main (main) where

import           Blagda
import           Blagda.Diagrams
import           Blagda.Markdown
import           Blagda.Utils
import           Control.Monad.IO.Class
import           Control.Monad.Writer
import           Data.Aeson
import           Data.List
import qualified Data.Map as Map
import           Data.Maybe (catMaybes)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import           Data.Time (UTCTime, defaultTimeLocale, parseTimeM)
import           Data.Time.Format (formatTime)
import           Development.Shake
import           Development.Shake.FilePath
import           Development.Shake.Forward (shakeArgsForward, forwardOptions)
import           GHC.Generics (Generic)
import qualified System.Directory as Dir
import           Text.HTML.TagSoup
import           Text.Pandoc (Meta (Meta))
import           Utils

parseHeader :: Meta -> Maybe Article
parseHeader (Meta m) =
  Article
    <$> (parseMetaString =<< Map.lookup "title" m)
    <*> ( parseTimeM True defaultTimeLocale "%Y-%m-%d %H:%M"
          . Text.unpack =<< parseMetaString
                        =<< Map.lookup "date" m)
    <*> (fmap (splitTags . T.unpack) . parseMetaString =<< Map.lookup "tags" m)

data Article = Article
  { a_title    :: Text
  , a_datetime :: UTCTime
  , a_tags     :: [String]
  }
  deriving (Eq, Ord, Show, Generic)

instance ToJSON Article where
  toJSON (Article txt ut tags) =
    object
      [ "a_title" .= txt
      , "a_datetime" .= formatTime defaultTimeLocale "%Y-%m-%d" ut
      , "a_tags" .= tags
      ]


main :: IO ()
main =
  shakeArgsForward
    (forwardOptions $ shakeOptions
      { shakeFiles="_build"
      , shakeLintInside=["site"]
      , shakeChange=ChangeDigest
      , shakeVersion = "0"
      }) $ do

  liftIO $ Dir.createDirectoryIfMissing True "_build/html"
  liftIO $ Dir.createDirectoryIfMissing True "_build/html1"
  liftIO $ Dir.createDirectoryIfMissing True "_build/html1/agda"

  agda_files <- agdaHTML "site"
  fileIdents <- liftIO $ newCacheIO parseFileIdents
  fileTypes <- liftIO $ newCacheIO parseFileTypes

  md_files' <- getDirectoryFiles "site" ["**/*.md"]
  let md_files = Set.toList $ Set.fromList md_files' Set.\\ Set.fromList agda_files

  commit <- gitCommit

  md0   <- sort . fmap ("_build/html0" </>) <$> getDirectoryFiles "_build/html0" ["*.md"]
  html0 <- sort . fmap ("_build/html0" </>) <$> getDirectoryFiles "_build/html0" ["*.html"]

  raw_articles <-
    forP (fmap ("site" </>) md_files) $ \input ->
      loadMarkdown parseHeader commit input
  raw_md <-
    forP md0 $ fmap (\s -> s { p_path = dropDirectory1 $ p_path s } ) . loadMarkdown parseHeader commit

  void $ forP html0 $ \html ->
    -- liftIO $ Dir.copyFile html $ getBuildPath "html1/agda" "html" html
    liftIO $ Dir.copyFile html $ getBuildPath "html1" "html" html

  let renamed_articles = rename doMyRename $ raw_articles <> raw_md
  articles <- forP renamed_articles $ renderPost fileIdents defaultWriterOptions

  writeTemplate "template.html" articles

  let posts = reverse $ sortOn (a_datetime . p_meta) $ catMaybes $ fmap sequenceA articles
  writeTemplate "index.html" $ pure $ Post "index.html" mempty $ object
    [ "a_title" .= id @Text "Home"
    , "posts" .= posts
    ]

  let feed = object
        [ "last_updated" .= maximum (fmap (fmap a_datetime . p_meta) articles)
        , "posts" .= take 10 posts
        ]
  writeTemplate "templates/atom.xml" $ pure $ Post "atom.xml" mempty feed
  writeTemplate "templates/rss.xml" $ pure $ Post "feed.rss" mempty feed

  buildDiagrams

  html1 <- getDirectoryFiles "_build/html1" ["**/*.html"]
  void $ forP html1 $ \input -> do
    let out = "_build/html" </> input
    text <- liftIO $ Text.readFile $ "_build/html1" </> input
    tags <- traverse (addLinkType fileIdents fileTypes) $ parseTags text
    writeFile' out $ Text.unpack $ renderHTML5 tags

  xml1 <- getDirectoryFiles "_build/html1" ["*.xml"]
  void $ forP (fmap ("_build/html1" </>) xml1) $ \input ->
    liftIO $ Dir.copyFile input $ getBuildPath "html" "xml" input
  rss1 <- getDirectoryFiles "_build/html1" ["*.rss"]
  void $ forP (fmap ("_build/html1" </>) rss1) $ \input ->
    liftIO $ Dir.copyFile input $ getBuildPath "html" "rss" input

  statics <- getDirectoryFiles "support/static" ["**/*"]
  void $ forP statics $ \filepath ->
    copyFileChanged ("support/static" </> filepath) ("_build/html" </> filepath)


doMyRename :: FilePath -> FilePath
doMyRename s
  | isPrefixOf "blog/20" s = dropExtension ("blog" </> drop (length @[] "Blog/2000-00-00-") s) </> "index.html"
  | isPrefixOf "blog" s = dropExtension ("blog" </> drop 5 s) </> "index.html"
  | isPrefixOf "misc/" s = dropExtension (drop 5 s) </> "index.html"
  -- | Just (c, _) <- uncons s
  -- , isUpper c = "agda" </> s
  | otherwise = s


gitCommit :: Action String
gitCommit = do
  Stdout t <- command [] "git" ["rev-parse", "--verify", "HEAD"]
  pure (head (lines t))

