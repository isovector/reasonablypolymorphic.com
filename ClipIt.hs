module ClipIt
    ( Clipping (..)
    , getClippings
    , parseClippings
    ) where

import Control.Arrow ((***))
import Control.Applicative ((<$>))
import Data.DateTime
import Data.Either (rights)
import Data.Time.Clock
import Data.Time.LocalTime (localTimeToUTC, utc)
import Text.ParserCombinators.Parsec
import Debug.Trace (trace, traceM)
import Control.Monad (liftM, join)
import Data.Time.Parse (strptime)

data Clipping =
    Clipping
    { book     :: String
    , author   :: String
    , page     :: Int
    , location :: (Int, Int)
    , added    :: Maybe DateTime
    , contents :: String
    } deriving Show

-- I Will Teach You to Be Rich (Sethi Ramit)
-- - Highlight on Page 10 | Loc. 153-54  | Added on Sunday, March 29, 2015, 04:11 PM

-- Who wins at the end of the day? The self-satisfied people who heatedly
-- debate some obscure details? Or the people who sidestep the entire debate
-- and get started?
-- ==========


titleWord :: GenParser Char st String
titleWord =
    do
        many (noneOf "()")

typeof :: GenParser Char st String
typeof =
    do
        let types = ["Highlight", "Note", "Bookmark"]
        choice $ map string types

showTrace :: (Show a) => a -> a
showTrace t = trace (show t) t

getClippings :: [FilePath] -> IO [Clipping]
getClippings = fmap (join . rights) . sequence . map (fmap parseClippings . readFile)


-- Each line contains 1 or more cells, separated by a comma
clipping :: GenParser Char st Clipping
clipping =
    do
        bookName <- titleWord
        char '('
        authorName <- titleWord
        char ')'
        traceM bookName
        eol
        string "- "
        ctype <- typeof
        string " on Page "
        cPage <- read <$> many digit
        string " | "
        cLoc <- loc
        string "|"
        string " Added on "
        time <- parseTime <$> many (noneOf "\n")
        many eol                       -- end of line
        cContents <- many (noneOf "\n")
        eol
        many $ char '='
        eol
        return Clipping
            { book = bookName
            , author = authorName
            -- , typeof
            , page = cPage
            , location = cLoc
            , added = time
            , contents = cContents
            }

parseTime :: String -> Maybe UTCTime
parseTime = fmap (localTimeToUTC utc . fst) . strptime "%A, %B %e, %Y, %I:%M %p"

loc :: GenParser Char st (Int, Int)
loc =
    do
        string "Loc. "
        start <- many digit
        endMaybe <- optionMaybe $
            do
                char '-'
                many digit
        many space
        return . join (***) read $ case endMaybe of
            Just end ->
                let prefix = take (length start - length end) start
                 in (start, prefix ++ end)
            Nothing  -> (start, start)


-- The end of line character is \n
eol :: GenParser Char st Char
eol = char '\n'

parseClippings :: String -> Either ParseError [Clipping]
parseClippings input = parse (many clipping) "(unknown)" input
