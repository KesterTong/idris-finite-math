module Finmath.Vector

import Finite

--------------------------------------------------------------------------------
-- Equivalence of vectors and maps on finite sets
--------------------------------------------------------------------------------

||| Map from a vector to a function on a finite set
||| Note that this is the Prelude.Vect.index with the arguments reversed.
vectToMap : Vect n a -> Fin n -> a
vectToMap (x :: xs) fZ     = x
vectToMap (x :: xs) (fS k) = vectToMap xs k

||| The inverse of vectToMap
mapToVect : (Fin n -> a) -> Vect n a
mapToVect {n=Z} f     = []
mapToVect {n=(S k)} f = (f fZ) :: (mapToVect (f . fS))

--------------------------------------------------------------------------------
-- Operations on vectors derived from operations on finite sets by duality
--------------------------------------------------------------------------------

||| Concatenates two vectors
concat : Vect n a -> Vect m a -> Vect (n + m) a
concat v w = mapToVect ((either (vectToMap v) (vectToMap w)) . fSetSumInv)

||| Splits a vector
split : Vect (n + m) a -> (Vect n a, Vect m a)
split {n}{m} v = let f = (vectToMap v) . (fSetSum {m=m}{n=n}) in
  (mapToVect (f . Left), mapToVect (f . Right))

||| Unflattens a vector
unFlatten : Vect (n * m) a -> Vect n (Vect m a)
unFlatten v = let f = \x => \y => (vectToMap v) (fSetProduct (x,y)) in
  mapToVect (mapToVect . f)


