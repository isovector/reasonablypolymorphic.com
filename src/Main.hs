{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE ViewPatterns              #-}
{-# language DuplicateRecordFields     #-}
{-# language OverloadedStrings         #-}

module Main where

import           Control.Arrow ((&&&))
import           Control.Monad (join)
import           Data.List (sortBy)
import qualified Data.Map as M
import           Data.Maybe (isJust)
import           Data.Monoid ((<>))
import           Data.Ord (comparing)
import           Data.Set (insert)
import           Data.Text (pack, unpack)
import           Data.Text.Lens (_Text)
import           Data.Time.Format (formatTime, defaultTimeLocale)
import           Data.Time.Parse (strptime)
import           Data.Traversable (for)
import           GHC.Exts (fromList)
import           SitePipe hiding (getTags)
import           SitePipe.Readers
import           Text.Pandoc
import           Text.Pandoc.Highlighting
import           Text.Pandoc.Options
import           Utils


postFormat :: String
postFormat = "/[0-9]{4}-[0-9]{2}-[0-9]{2}-"


toSlug :: String -> String
toSlug = replaceAll ("/posts" <> postFormat) (const "")
       . replaceAll ("/misc/") (const "")
       . replaceAll "\\.html"  (const "")

main :: IO ()
main = site $ do
  let l = _Object . at "url" . _Just . _String . _Text

  rawMisc <- resourceLoader sandyReader ["misc/*.markdown"]
  let misc =
        flip fmap rawMisc $
          \x ->
            let url  = x ^?! l
                slug = toSlug url
             in x & l                            .~ slug <> "/index.html"
                  & _Object . at "page_title"    .~ x ^?! _Object . at "title"
                  & _Object . at "canonical_url" ?~ _String . _Text # slug
                  & _Object . at "slug"          ?~ _String . _Text # slug
                  & _Object . at "has_prev"      ?~ _Bool # False
                  & _Object . at "has_next"      ?~ _Bool # False
                  & _Object . at "has_related"   ?~ _Bool # False
                  & _Object . at "html_tags"     .~ Nothing
                  & _Object . at "zulu"          ?~ _String . _Text # ""
                  & _Object . at "date"          ?~ _String . _Text # ""

  rawPosts <- sortBy (comparing (^?! l))
          <$> resourceLoader sandyReader ["posts/*.markdown"]

  let urls = fmap (^?! l) rawPosts
      getEm' = getNextAndPrev urls
      posts' =
        flip fmap rawPosts $
          \x ->
            let url  = x ^?! l
                (fmap toSlug -> prev, fmap toSlug -> next) = getEm' url
                tagsOf = x ^? _Object . at "tags" . _Just . _String . _Text
                related = x ^? _Object . at "related" . _Just
                date = fst . (^?! _Just) . strptime "%Y-%m-%d %H:%M"
                     $ x ^?! _Object . at "date" . _Just . _String . _Text
                slug = toSlug url

             in x & l                         .~ "blog/" <> slug <> "/index.html"
                  & _Object . at "page_title" .~ x ^?! _Object . at "title"
                  & _Object . at "canonical_url" ?~ _String . _Text # ("blog/" <> slug)
                  & _Object . at "slug"       ?~ _String . _Text # slug
                  & _Object . at "has_prev"   ?~ _Bool # isJust prev
                  & _Object . at "has_next"   ?~ _Bool # isJust next
                  & _Object . at "has_related" ?~ _Bool # isJust related
                  & _Object . at "related"    ?~ (maybe (Array $ fromList []) id related :: Value)
                  & _Object . at "html_tags"  .~
                      fmap (\y -> _String . _Text # makeTags y) tagsOf
                  & _Object . at "prev"       .~
                      fmap (review $ _String . _Text) prev
                  & _Object . at "next"       .~
                      fmap (review $ _String . _Text) next
                  & _Object . at "zulu"       ?~ _String . _Text #
                      formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%SZ" date
                  & _Object . at "date"       ?~ _String . _Text #
                      formatTime defaultTimeLocale "%B %e, %Y" date
      slugList = M.fromList
               $ fmap ((^?! _Object . at "slug" . _Just . _String) &&& id) posts
      posts = flip fmap posts' $ \post ->
        post & _Object . at "related" . _Just . _Array
                %~ fmap (\x -> maybe (error $ "bad related slug: " <> x ^?! _String . _Text) id
                             $ M.lookup (x ^?! _String) slugList)

  let tags   = getTags makeTagUrl $ reverse posts
      newest = last posts

      feed :: String -> Value
      feed url = object
        [ "posts"        .= take 10 (reverse posts)
        , "domain"       .= ("http://reasonablypolymorphic.com" :: String)
        , "url"          .= url
        , "last_updated" .= (newest ^?! _Object . at "zulu" . _Just . _String)
        ]

  writeTemplate' "post.html" . pure
    $ newest
      & _Object . at "url"        ?~ _String # "/index.html"
      & _Object . at "page_title" ?~ _String # "Home"

  let byYear = reverse
              . flip groupOnKey (reverse posts)
              $ \x -> reverse
                    . take 4
                    . reverse
                    $ x ^?! _Object . at "date" . _Just . _String . _Text

  writeTemplate' "archive.html" . pure
    $ object
      [ "url" .= ("/blog/archives/index.html" :: String)
      , "page_title" .= ("Archives" :: String)
      , "years" .= (flip fmap byYear $ \(year, ps) ->
          object
            [ "posts" .= ps
            , "year"  .= year
            ]
        )
      ]

  writeTemplate' "post.html" $ posts ++ misc
  writeTemplate' "tag.html"  tags

  writeTemplate' "rss.xml"  . pure $ feed "feed.rss"
  writeTemplate' "atom.xml" . pure $ feed "atom.xml"

  copyFiles
    [ "css"
    , "js"
    , "images"
    ]

  copyFilesWith (drop 7) [ "static/*" ]

  pure ()


writeTemplate' :: ToJSON a => String -> [a] -> SiteM ()
writeTemplate' a = writeTemplate ("templates/" <> a)


sandyReader :: String -> IO String
sandyReader =
  mkPandocReaderWith
    (\ro -> readMarkdown ro { readerExtensions = foldr enableExtension
                                                       pandocExtensions
                                                       extensions
                            } . pack)
    pure
    (fmap unpack . writeHtml5String pandocMathCompiler)

extensions :: [Extension]
extensions =
  [ Ext_tex_math_dollars
  -- , Ext_latex_macros
  , Ext_footnotes
  ]

pandocMathCompiler :: WriterOptions
pandocMathCompiler =
  let mathExtensions = extensions
      newExtensions = foldr enableExtension pandocExtensions mathExtensions
      writerOptions = def
          { writerExtensions = newExtensions
          , writerHTMLMathMethod = MathJax ""
          , writerHighlightStyle = Just haddock
          }
   in writerOptions

