{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
module Site.Constants where

import Hakyll (Pattern, FeedConfiguration (..), fromGlob)


dateFormat = "%B %e, %Y"

postsDir :: String -> Pattern
postsDir = fromGlob . (++ "posts/*")

bookDir :: String -> Pattern
bookDir = fromGlob . (++ "httw/*")

miscDir :: String -> Pattern
miscDir = fromGlob . (++ "misc/*")
