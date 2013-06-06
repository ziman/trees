module Evenness where

data Evenness : Set where
  even uneven : Evenness

other : Evenness → Evenness
other   even = uneven
other uneven =   even
