module ClipIt
    ( Clipping (..)
    , getClippings
    , parseClippings
    , getBooks
    , canonicalName
    ) where

import Control.Arrow ((***))
import Control.Applicative ((<$>))
import Data.Char (toLower, isAlphaNum, isSpace)
import Data.DateTime
import Data.Either (rights)
import Data.List (nub)
import Text.Regex
import Data.Time.Clock
import Data.Time.LocalTime (localTimeToUTC, utc)
import Text.ParserCombinators.Parsec
import Debug.Trace (trace, traceM)
import Control.Monad (liftM, liftM2, join)
import Data.Time.Parse (strptime)

data Clipping =
    Clipping
    { bookName :: String
    , subtitle :: Maybe String
    , author   :: String
    , page     :: Maybe Int
    , location :: (Int, Int)
    , added    :: Maybe DateTime
    , contents :: String
    } deriving (Show, Eq)

-- I Will Teach You to Be Rich (Sethi Ramit)
-- - Highlight on Page 10 | Loc. 153-54  | Added on Sunday, March 29, 2015, 04:11 PM

-- Who wins at the end of the day? The self-satisfied people who heatedly
-- debate some obscure details? Or the people who sidestep the entire debate
-- and get started?
-- ==========

authorWord :: GenParser Char st String
authorWord =
    do
        spaces
        result <- choice
            [ do
                char '('
                result <- many $ noneOf ")"
                char ')'
                return result
            , do
                char '-'
                spaces
                line
            ]
        eol
        return result


titleWord :: GenParser Char st String
titleWord =
    do
        manyTill anyChar (try $ lookAhead authorWord)

typeof :: GenParser Char st String
typeof =
    do
        let types = ["Highlight", "Note", "Bookmark"]
        choice $ map string types

showTrace :: (Show a) => a -> a
showTrace t = trace (show t) t

getClippings :: [FilePath] -> IO [Clipping]
getClippings = fmap (filter (("" /=) . author))
             . fmap (join . rights)
             . sequence
             . map (fmap parseClippings . readFile)


onPage :: GenParser Char st (Maybe Int)
onPage = optionMaybe $ do
    string "on Page "
    cPage <- read <$> many digit
    string " |"
    spaces
    return cPage

parseSubtitle :: String -> (String, Maybe String)
parseSubtitle l =
    case matchRegex regex l of
        Just xs -> (xs !! 0, Nothing)
        Nothing -> (l, Nothing)
  where
      regex = mkRegex "^([^:(]*)"


clipping :: GenParser Char st Clipping
clipping =
    do
        meta <- line
        let regex = mkRegex "^(.*?) \\(([^)]*)\\)$|^(.*?) \\- (.*)$"
            matches = matchRegex regex meta
            ((book, cSub), authorName) =
                case matches of
                    Just xs -> case xs !! 0 of
                        ""    -> (parseSubtitle $ xs !! 2, xs !! 3)
                        name  -> (parseSubtitle name, xs !! 1)
                    Nothing -> (("", Nothing), "")

        eol
        string "- "
        typeof
        spaces
        cPage <- onPage
        cLoc <- loc
        string "|"
        string " Added on "
        time <- parseTime <$> line
        many eol                       -- end of line
        cContents <- line
        eol
        many $ char '='
        eol
        return Clipping
            { bookName = book
            , subtitle = cSub
            , author = authorName
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
        spaces
        return . join (***) read $ case endMaybe of
            Just end ->
                let prefix = take (length start - length end) start
                 in (start, prefix ++ end)
            Nothing  -> (start, start)


-- The end of line character is \n
eol :: GenParser Char st Char
eol = oneOf "\n"

line :: GenParser Char st String
line = many $ noneOf "\n"

parseFile :: GenParser Char st [Clipping]
parseFile = do
    optional $ string "\xBB\xEF"
    many clipping


parseClippings :: String -> Either ParseError [Clipping]
parseClippings input = parse parseFile "(unknown)" input

getBooks :: Either ParseError [Clipping] -> [(String, String)]
getBooks (Left _) = []
getBooks (Right bs) = nub $ map (liftM2 (,) bookName author) bs

canonicalName :: Clipping -> String
canonicalName = replace ' ' '-'
              . reverse . dropWhile (== ' ') . reverse
              . filter (liftM2 (||) isAlphaNum isSpace)
              . fmap toLower
              . liftM2 spaceConcat author bookName
  where spaceConcat a b = a ++ " " ++ b
        replace a b = map $ \c -> if (c == a) then b else c


