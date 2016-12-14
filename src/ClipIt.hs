module ClipIt
    ( Clipping (..)
    , getClippings
    , parseClippings
    , getBooks
    , canonicalName
    ) where

import Control.Arrow ((***))
import Control.Applicative ((<$>), (<|>))
import Data.Char (toLower, isAlphaNum, isSpace)
import Data.DateTime
import Data.Either (rights)
import Data.List (nub, sort)
import Text.Regex
import Data.Time.Clock
import Data.Time.LocalTime (localTimeToUTC, utc)
import Text.ParserCombinators.Parsec hiding ((<|>))
import Debug.Trace (trace, traceM)
import Control.Monad (liftM, liftM2, join)
import Data.Time.Parse (strptime)

data Clipping =
    Clipping
    { bookName :: String
    , subtitle :: Maybe String
    , author   :: String
    , added    :: DateTime
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
titleWord = manyTill anyChar . try $ lookAhead authorWord

typeof :: GenParser Char st String
typeof = do
  optional $ string "Your "
  choice $ map string ["Highlight", "Note", "Bookmark"]

showTrace :: (Show a) => a -> a
showTrace = trace =<< show

getClippings :: [FilePath] -> IO [Clipping]
getClippings = fmap (filter (("" /=) . author))
             . fmap (join . fmap (either (error . show) id))
             . sequence
             . map (\f -> fmap (parseClippings f) $ readFile f)
             . sort


onPage :: GenParser Char st ()
onPage = do
    choice [ string "Page"
           , string "page"
           ]
    spaces
    many digit
    optional $ do
      spaces
      string "|"
      spaces

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
        optional $ do
          string "on"
          spaces
        optional onPage
        cLoc <- loc
        string "|"
        string " Added on "
        Just time <- timeParser <$> line
        many eol                       -- end of line
        cContents <- line
        eol
        many $ char '='
        eol
        return Clipping
            { bookName = book
            , subtitle = cSub
            , author = authorName
            , added = time
            , contents = cContents
            }

timeParser :: String -> Maybe UTCTime
timeParser s = parseTime s <|> parseTime2 s

parseTime :: String -> Maybe UTCTime
parseTime = fmap (localTimeToUTC utc . fst) . strptime "%A, %B %e, %Y, %I:%M %p"

parseTime2 :: String -> Maybe UTCTime
parseTime2 = fmap (localTimeToUTC utc . fst) . strptime "%A, %B %e, %Y %I:%M:%s %p"

loc :: GenParser Char st (Int, Int)
loc = do
  string "Loc"
  choice [ string "."
         , string "ation"
         ]
  spaces
  start <- many digit
  endMaybe <- optionMaybe $ do
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


parseClippings :: FilePath -> String -> Either ParseError [Clipping]
parseClippings path input = parse parseFile path input

getBooks :: Either ParseError [Clipping] -> [(String, String)]
getBooks (Left s) = error $ show s
getBooks (Right bs) = nub $ map (liftM2 (,) bookName author) bs

canonicalName :: Clipping -> String
canonicalName = replace ' ' '-'
              . reverse . dropWhile (== ' ') . reverse
              . filter (liftM2 (||) isAlphaNum isSpace)
              . fmap toLower
              . liftM2 spaceConcat author bookName
  where spaceConcat a b = a ++ " " ++ b
        replace a b = map $ \c -> if (c == a) then b else c

files = [ "clippings/age-of-em-daily-rituals.txt"
        , "clippings/ai-to-zombies.txt"
        , "clippings/atlas-shrugged-ending.txt"
        , "clippings/believer-lightness-clock.txt"
        , "clippings/dennet-ikigai.txt"
        , "clippings/fail-everything-room.txt"
        , "clippings/feynman-solitude.txt"
        , "clippings/hpmor-silver-gatto.txt"
        , "clippings/influence-atlas-shrugged.txt"
        , "clippings/initial-commit.txt"
        , "clippings/kegan-feynman.txt"
        , "clippings/metaphors-rising-intelligence.txt"
        , "clippings/misc-diamond-age.txt"
        ]



oldStyle :: String
oldStyle = unlines
  [ "Atlas Shrugged: (Centennial Edition) (Ayn Rand)"
  , "- Highlight on Page 1121 | Loc. 17178-79  | Added on Wednesday, November 04, 2015, 07:47 AM"
  , ""
  , "She heard the words; she understood the meaning; she was unable to make it real—to grant the respect of anger, concern, opposition to a nightmare piece of insanity that rested on nothing but people's willingness to pretend to believe that it was sane."
  , "=========="
  ]

newStyle :: String
newStyle = unlines
  [ "The Age of Em: Work, Love and Life when Robots Rule the Earth (Hanson, Robin)"
  , "- Your Highlight on Location 2837-2839 | Added on Sunday, June 19, 2016 3:43:11 PM"
  , ""
  , "give stronger incentives for overall performance, compared with rewarding the best performers (Drouvelis and Jamison 2015; Kubanek et al. 2015)."
  , "=========="
  ]
