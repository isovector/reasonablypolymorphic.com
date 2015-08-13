module Utils ( sortAndGroup
             ) where

import Data.Map (fromListWith, toList)

sortAndGroup :: Ord k => (a -> k) -> [a] -> [[a]]
sortAndGroup key as = map snd
                    . toList
                    $ fromListWith (++)
                        [(key a, [a]) | a <- as]

