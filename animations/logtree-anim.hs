import Control.Monad
import Control.Applicative

import System.Environment

import Diagrams.Coordinates
import Diagrams.Prelude
import Diagrams.Path
import Diagrams.Backend.Cairo
import Diagrams.Backend.Cairo.Internal

type Pic = Diagram Cairo R2

data State = Empty | Visited | Current deriving Eq
data Dir = L | R

data Tree = Leaf State | Branch State Dir Tree Tree

renderTree :: Tree -> Pic
renderTree (Leaf Empty) = square 1 # (fc white . lc white)
renderTree (Leaf Visited) = square 1 # fc black
renderTree (Leaf Current) = square 1 # fc red

renderTree (Branch s d l r) =
    parentFrame
    ===
    strutY 1
    ===
    centerX (leftChild ||| rightChild)
  where
    arrow = stroke (fromOffsets [0 & 0, case d of { L -> 0.7; R -> -0.7} & (-0.7)])
    parentFrame = parent `atop` (circle 0.6 # lc white)
    parent = (circle 0.6 `atop` arrow) # (case s of
        Empty -> fc white . lc white
        Visited -> fc black
        Current -> fc red)
    leftChild = renderTree l
    rightChild = renderTree r

tree :: Int -> Tree
tree 0 = Leaf Empty
tree n = let t = tree (n-1) in Branch Empty L t t

whichChild :: State -> Dir -> Dir
whichChild Current L = L
whichChild Current R = R
whichChild Visited L = R
whichChild Visited R = L

flip' :: State -> Dir -> Dir
flip' Current L = R
flip' Current R = L
flip' Visited L = L
flip' Visited R = R

-- Branch ballPresent direction l r
step :: (Tree, Bool) -> (Tree, Bool)
step (Leaf Empty,  _) = (Leaf Visited, True)
step (Branch Empty d l r, True) = (Branch Visited d l r, True)
step (Branch s d l r, True) = (Branch Current d l r, False)
step (Branch s d l r, False) = case flip' s d of
    L -> let (l', restart) = step (l, s == Current) in (Branch Visited (flip' s d) l' r , restart)
    R -> let (r', restart) = step (r, s == Current) in (Branch Visited (flip' s d) l  r', restart)

diagram :: Int -> Pic
diagram fno = bg white (renderTree $ fst iterated) # lw 0.03
  where
    iterated = iterate step (tree 4, True) !! fno

main :: IO ()
main = do
    [fno] <- map read <$> getArgs
    fst $ renderDia Cairo (CairoOptions "frame.png" (Width 300) PNG False) (diagram fno)

