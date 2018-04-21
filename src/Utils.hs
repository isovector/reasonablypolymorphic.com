{-# LANGUAGE OverloadedStrings #-}

module Utils where

import           Control.Arrow ((&&&))
import           Control.Lens (view, review)
import           Data.Aeson (Value, (.=))
import           Data.List (intercalate, isPrefixOf)
import qualified Data.Map as M
import           Data.Maybe (listToMaybe, fromJust)
import           Data.Monoid ((<>))
import           Data.Text (split, Text)
import           Data.Text.Lens (_Text, unpacked)
import           SitePipe
import           Text.Regex.TDFA ((=~~))



--------------------------------------------------------------------------------
-- | A simple (but inefficient) regex replace funcion
replaceAll :: String              -- ^ Pattern
           -> (String -> String)  -- ^ Replacement (called on capture)
           -> String              -- ^ Source string
           -> String              -- ^ Result
replaceAll pattern f source = replaceAll' source
  where
    replaceAll' src = case listToMaybe (src =~~ pattern) of
        Nothing     -> src
        Just (o, l) ->
            let (before, tmp) = splitAt o src
                (capture, after) = splitAt l tmp
            in before ++ f capture ++ replaceAll' after

splitTags :: String -> [String]
splitTags = filter (/= "")
          . fmap ( dropWhile (== ' ')
                 . view unpacked
                 )
          . split (== ',')
          . review _Text

makeTags :: String -> String
makeTags = intercalate ", "
         . fmap (\x -> "<a href=\"" <> makeTagUrl x <> "\">" <> x <> "</a>")
         . splitTags

makeTagUrl :: String -> String
makeTagUrl tagName = "/tags/" ++ tagName ++ ".html"


getNextAndPrev :: Eq a => [a] -> a -> (Maybe a, Maybe a)
getNextAndPrev as a =
  let mas = fmap Just as
   in fromJust . lookup a
               $ zipWith3 (\b c d -> (b, (c, d)))
                          as
                          (Nothing : mas)
                          (tail mas ++ [Nothing])


getTags :: (String -> String) -- ^ Accept a tagname and create a url
        -> [Value] -- ^ List of posts
        -> [Value]
getTags makeUrl postList = uncurry (makeTag makeUrl) <$> M.toList tagMap
  where
    tagMap = M.unionsWith mappend $ fmap toMap postList
    toMap post = M.fromList
               . zip (splitTags $ post ^. key "tags"
                                        . _String
                                        . _Text)
               $ repeat [post]

-- | Makes a single tag
makeTag :: (String -> String) -> String -> [Value] -> Value
makeTag makeUrl tagname posts = object
  [ "tag"   .= tagname
  , "url"   .= makeUrl tagname
  , "posts" .= posts
  , "page_title" .= ("Posts tagged \"" <> (_Text # tagname) <> "\"" :: Text)
  ]


groupOnKey :: Ord k => (v -> k) -> [v] -> [(k, [v])]
groupOnKey f = M.toAscList
             . M.fromListWith (flip mappend)
             . fmap (f &&& pure)


titleCompare :: String -> String
titleCompare s =
    if isPrefixOf "The " s
       then drop 4 s
       else s

