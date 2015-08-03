module Utils ( sortAndGroup
             ) where

import Data.Map (fromListWith, toList)

sortAndGroup :: Ord k => (a -> k) -> [a] -> [[a]]
sortAndGroup key as = map snd
                    . toList
                    $ fromListWith
                        (++)
                        [(k, [v]) | (k, v) <- zip =<< map key $ as]

