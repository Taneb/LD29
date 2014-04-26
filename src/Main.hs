{-# LANGUAGE Arrows #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module Main (main) where

import Control.Lens
import Control.Monad.State
import Control.Wire
import Data.Fixed
import Linear
import FreeGame
import FRP.Netwire
import System.Random
import Prelude hiding ((.), id)

data Item =
  Treasure | Fuel | Upgrade UpgradeType
  deriving Eq

data UpgradeType =
  Ballast | Rotor | Tank
  deriving Eq

newtype Space = Space {getItem :: Maybe (V2 Double, Item)}
makeWrapped ''Space

data Stream a = a :- Stream a
              deriving Functor

data LZipper a = LZipper {_leftZ :: Stream a, _hereZ :: a, _rightZ :: Stream a}
               deriving Functor

makeLenses ''LZipper

zleft :: LZipper a -> LZipper a
zleft LZipper{_leftZ = ls, _hereZ = l, _rightZ = (r :- rs)} =
  LZipper{_leftZ = l :- ls, _hereZ = r, _rightZ = rs}

zright :: LZipper a -> LZipper a
zright LZipper{_leftZ = (l :- ls), _hereZ = r, _rightZ = rs} =
  LZipper{_leftZ = ls, _hereZ = l, _rightZ = r :- rs}

type MapM = State (Int, StdGen)

newtype Map = Map {getMap :: LZipper (LZipper (Either (MapM Space) Space))}
makeWrapped ''Map

initialMap :: Map
initialMap = Map $ allZ (allZ initialTile)
  where
    allS x = x :- allS x
    allZ x = LZipper {_leftZ = allS x, _hereZ = x, _rightZ = allS x}
    initialTile :: Either (MapM Space) Space
    initialTile = Left $ do
      _1 +~ 1
      x <- _2 %%= randomR (0, 2::Int)
      (Space . Just . (,) (V2 120 90)) <$> case x of
        0 -> return Treasure
        1 -> return Fuel
        2 -> Upgrade <$> do
          y <- _2 %%= randomR (0, 2::Int)
          case y of
            0 -> return Ballast
            1 -> return Rotor
            2 -> return Tank

normalize :: Map -> MapM Map
normalize m0 = do
  m1 <- normalize1 (mapUp m0)
  m2 <- normalize1 (mapLeft m1)
  m3 <- normalize1 (mapDown m2)
  m4 <- normalize1 (mapDown m3)
  m5 <- normalize1 (mapRight m4)
  m6 <- normalize1 (mapRight m5)
  m7 <- normalize1 (mapUp m6)
  m8 <- normalize1 (mapUp m7)
  normalize1 (mapLeft . mapDown $ m8)
  where normalize1 m = do
          case m^._Wrapped.hereZ.hereZ of
            Left a -> do
              r <- a
              return $ m & _Wrapped.hereZ.hereZ .~ Right r
            Right{} -> return m

mapRight :: Map -> Map
mapRight Map{getMap = m} = Map{getMap = fmap zright m}

mapLeft :: Map -> Map
mapLeft Map{getMap = m} = Map{getMap = fmap zleft m}

mapUp :: Map -> Map
mapUp Map{getMap = m} = Map{getMap = zleft m}

mapDown :: Map -> Map
mapDown Map{getMap = m} = Map{getMap = zright m}

computeVVel :: Int -> Double -> Int -> Double
computeVVel dir fuel upgradeLevel 
  | nearZero fuel = 0
  | otherwise = fromIntegral (signum dir) * speed
  where
    speed = log . (+exp 1) . fromIntegral $ upgradeLevel

computeVPos :: SimpleWire Double Double
computeVPos = integral 0

normalizeVPos :: Double -> (Double, Ordering)
normalizeVPos c = let adjusted = c `mod'` 180
                  in (adjusted, adjusted `compare` c)

computeHAcc :: Int -> Double -> Double -> Int -> Double
computeHAcc dir fuel vel upgradeLevel
  | dir == 0 || nearZero fuel = -0.25 * vel
  | otherwise = fromIntegral (signum dir) * accel
  where
    accel = log . (+exp 1) . fromIntegral $ upgradeLevel

computeHVel :: SimpleWire Double Double
computeHVel = integralWith correct 0 . arr (flip (,) ())
  where
    correct _ n | n >= 50 = 50
                | otherwise = n

computeHPos :: SimpleWire Double Double
computeHPos = integral 0

normalizeHPos :: Double -> (Double, Ordering)
normalizeHPos c = let adjusted = c `mod'` 240
                  in (adjusted, adjusted `compare` c)

itemCollision :: SimpleWire (Map, V2 (Double, Ordering)) (Event Item, Map)
itemCollision = proc (m0, V2 (xpos, xoff) (ypos, yoff)) ->
  let m = case (yoff, xoff) of
        (EQ, EQ) -> m0
        (EQ, GT) -> mapUp m0
        (GT, GT) -> mapUp $ mapRight m0
        (GT, EQ) -> mapRight m0
        (GT, LT) -> mapDown $ mapRight m0
        (EQ, LT) -> mapDown m0
        (LT, LT) -> mapDown $ mapLeft m0
        (LT, EQ) -> mapLeft m0
        (LT, GT) -> mapUp $ mapLeft m0
      t = preview (_Wrapped.hereZ.hereZ._Right._Wrapped._Just) m
  in case t of
    Just (p,i) | distance p (V2 xpos ypos) <= 5 -> 
      let n = m & _Wrapped.hereZ.hereZ._Right._Wrapped .~ Nothing
      in do
        ei <- now -< i
        ns <- id -< n
        returnA -< (ei, ns)
    _ -> do
      ei <- never -< ()
      ms <- id -< m
      returnA -< (ei, ms)

countItem :: Item -> SimpleWire (Event Item) Int
countItem item =
  krSwitch (pure 0) .
  second adjustWire .
  (pure () &&& filterE (== item))
  where
    adjustWire = arr ((arr (+1) .) <$)

computeScore :: SimpleWire (Event Item) Int
computeScore = countItem Treasure * 100

computeBallastUpgrade :: SimpleWire (Event Item) Int
computeBallastUpgrade = countItem $ Upgrade Ballast

computeRotorUpgrade :: SimpleWire (Event Item) Int
computeRotorUpgrade = countItem $ Upgrade Rotor
  
computeTankUpgrade :: SimpleWire (Event Item) Int
computeTankUpgrade = countItem $ Upgrade Tank

rateOfFuelDecrease :: Bool -> Bool -> Double
rateOfFuelDecrease True True = 1
rateOfFuelDecrease False False = 0.2
rateOfFuelDecrease _ _ = 0.6

fuelRegenEvent :: SimpleWire (Int, Event Item) (Event Double)
fuelRegenEvent = 
  undefined

maxFuel :: Int -> Double
maxFuel = (*100) . log . (+exp 1) . fromIntegral

computeFuel :: SimpleWire (Double, Event Double) Double
computeFuel = 
  krSwitch (stopAtZero .integral 100 . arr negate) .
  second adjustWire
  where
    adjustWire = arr $ fmap (\i _ -> integral i . arr negate)
    stopAtZero = arr $ \r -> if r < 0 then 0 else r

mainWire :: SimpleWire (Int, Int, Map) (Int, Map, Bool)
mainWire = proc (x,y,m0) -> do
  rec {
    vinf <- arr normalizeVPos . computeVPos -< computeVVel y fuel ballastUpgrade;
    hvel <- computeHVel -< computeHAcc y fuel hvel rotorUpgrade;
    hinf <- arr normalizeHPos . computeHPos -< hvel;
    (ei, m1) <- itemCollision -< (m0, V2 hinf vinf);
    ballastUpgrade <- computeBallastUpgrade -< ei;
    rotorUpgrade <- computeRotorUpgrade -< ei;
    tankUpgrade <- computeTankUpgrade -< ei;
    ef <- fuelRegenEvent -< (tankUpgrade, ei);
    fuel <- computeFuel -< (maxFuel tankUpgrade, ef);
  }
  score <- computeScore -< ei
  returnA -< (score, m1, nearZero fuel)

main :: IO ()
main = do
  Just _ <- runGame Windowed (BoundingBox 0 0 480 360) $ do
    setTitle "Submarine game!"
    setFPS 60
    clearColor blue
    sessiin <- liftIO clockSession_
  return ()
  where
    gameLoop m0 g0 c0 w0 = do
      let (m, (g, c)) = runState (normalize m) (g, c)
      ks <- keyStates_
      u <- ks ^?! ix KeyUp
      d <- ks ^?! ix KeyDown
      l <- ks ^?! ix KeyLeft
      r <- ks ^?! ix KeyRight
      let v = case (u, d) of
            (Down, Up) -> (-1)
            (Up, Down) -> 1
            (_, _) -> 0
          h = case (l, r) of
            (Down, Up) -> (-1)
            (Up, Down) -> 1
            (_, _) -> 0
      let Identity (Left (s, m1, e), w1) = stepWire w0 