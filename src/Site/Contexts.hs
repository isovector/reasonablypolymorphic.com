module Site.Contexts
    ( postCtxWithTags
    , postCtx
    , setNextPrev
    , optionalConstField
    , clippingCtx
    , showTime
    ) where

import Control.Applicative (Alternative (..))
import Data.List (intercalate, sortBy)
import Data.Monoid (mconcat, (<>))
import Data.Time.Clock (UTCTime)
import Data.Time.Format (parseTimeM, formatTime, defaultTimeLocale)
import System.FilePath (takeFileName)

import ClipIt
import Hakyll
import Hakyll.Web.Tags
import Site.Constants


postCtxWithTags :: Tags -> Context String
postCtxWithTags tags = tagsField "tags" tags <> postCtx

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
            parseTime' fn = parseTimeM True defaultTimeLocale "%Y-%m-%d"
                          . intercalate "-"
                          . take 3
                          $ splitAll "-" fn
         in compare
            ((parseTime' fn1) :: Maybe UTCTime)
            ((parseTime' fn2) :: Maybe UTCTime)

setNextPrev :: [Identifier] -> Context String -> Context String
setNextPrev posts ctx =
    mconcat
        [ field "prev" $ getPrev posts zip
        , field "next" $ getPrev posts (flip zip)
        , ctx
        ]

optionalConstField :: String -> Maybe String -> Context a
optionalConstField key Nothing =  field key $ return empty
optionalConstField key (Just x) = field key . const $ return x

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

