import Control.Monad
import Control.Applicative

import System.Environment

import Diagrams.Coordinates
import Diagrams.Prelude
import Diagrams.Path
import Diagrams.Backend.Cairo
import Diagrams.Backend.Cairo.Internal

type Pic = Diagram Cairo R2

data Tree = Leaf Bool | Branch Bool Bool Tree Tree

renderTree :: Tree -> Pic
renderTree (Leaf False) = square 1
renderTree (Leaf True ) = square 1 # fc black

renderTree (Branch b e l r) =
    parent `atop` arrow
    ===
    strutY 1
    ===
    centerX (leftChild ||| rightChild)
  where
    arrow = stroke (fromOffsets [0 & 0, (if e then 0.7 else -0.7) & (-0.7)])
    parent
        | b = circle 0.6 # fc black
        | otherwise = circle 0.1 `atop` (circle 0.6 # lc white)
    leftChild = renderTree l
    rightChild = renderTree r

tree :: Int -> Tree
tree 0 = Leaf False
tree n = let t = tree (n-1) in Branch False False t t

-- Branch ballPresent direction l r
step :: (Tree, Bool) -> (Tree, Bool)
step (Leaf _,  _) = (Leaf True, True)
step (Branch False True  l r, False) = case step (l, False) of
    (l', restart) -> (Branch False True  l' r , restart)
step (Branch False False l r, False) = case step (r, False) of
    (r', restart) -> (Branch False False l  r', restart)
step (Branch True  False l r, False) = case step (l, True) of
    (l', restart) -> (Branch False True  l' r , restart)
step (Branch True  True  l r, False) = case step (r, True) of
    (r', restart) -> (Branch False False l  r', restart)
step (Branch _ d l r, True) = (Branch True d l r, False)

diagram :: Int -> Pic
diagram fno = bg white (renderTree $ fst iterated) # lw 0.03
  where
    iterated = iterate step (tree 4, True) !! fno

main :: IO ()
main = do
    [fno] <- map read <$> getArgs
    fst $ renderDia Cairo (CairoOptions "frame.png" (Width 300) PNG False) (diagram fno)

