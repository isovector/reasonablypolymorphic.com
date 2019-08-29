{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Erdos where

import Data.Functor
import GHC.Generics
import Data.Time.Calendar
import Data.Aeson
import Data.Function
import Data.List

buildCitySpan :: [ErdosMeta] -> [CitySpan]
buildCitySpan v =
  groupBy ((==) `on` emCity) v <&>
    \ems@(ErdosMeta{emCity,emCountry,emDepartureDate}:_) ->
        CitySpan
          { csArrivalDate   = emArrivalDate $ last ems
          , csDepartureDate = emDepartureDate
          , csCity          = emCity
          , csCountry       = emCountry
          , csErdos         = ems
          }

data CitySpan = CitySpan
  { csArrivalDate   :: Day
  , csDepartureDate :: Day
  , csCity          :: String
  , csCountry       :: String
  , csErdos         :: [ErdosMeta]
  } deriving (Generic)

instance ToJSON CitySpan where
  toJSON =
    genericToJSON defaultOptions
      { fieldLabelModifier = camelTo2 '-' . drop 2 }

data ErdosMeta = ErdosMeta
  { emUrl           :: String
  , emHost          :: String
  , emGithubUser    :: String
  , emCity          :: String
  , emCountry       :: String
  , emProject       :: String
  , emProjectUrl    :: Maybe String
  , emArrivalDate  :: Day
  , emDepartureDate :: Day
  , emContent       :: String
  } deriving (Generic)


instance FromJSON ErdosMeta where
  parseJSON =
    genericParseJSON defaultOptions
      { fieldLabelModifier = camelTo2 '-' . drop 2
      }

instance ToJSON ErdosMeta where
  toJSON =
    genericToJSON defaultOptions
      { fieldLabelModifier = camelTo2 '-' . drop 2 }

