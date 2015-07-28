{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
module Site.Constants where

import Hakyll (Pattern, FeedConfiguration (..))


dateFormat = "%B %e, %Y"

postsDir :: Pattern
postsDir = "posts/*"

feedConfiguration = FeedConfiguration
    { feedTitle       = "We Can Solve This"
    , feedDescription = "Musings on effective life strategies"
    , feedAuthorName  = "Sandy Maguire"
    , feedAuthorEmail = "sandy@sandymaguire.me"
    , feedRoot        = "http://sandymaguire.me/"
    }
