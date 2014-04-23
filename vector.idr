module FinMath.Vector

import FinMath.Finite
--------------------------------------------------------------------------------
-- Equivalence of vectors and maps on finite sets
--------------------------------------------------------------------------------

||| Map from a vector to a function on a finite set
||| Note that this is the Prelude.Vect.index with the arguments reversed.
vectToMap : Vect n a -> Fin n -> a
vectToMap (x :: xs) fZ = x
vectToMap (x :: xs) (fS k) = vectToMap xs k

||| The inverse of vectToMap
mapToVect : (Fin n -> a) -> Vect n a
mapToVect {n=Z} f = []
mapToVect {n=(S k)} f = (f fZ) :: (mapToVect (f . fS))

--------------------------------------------------------------------------------
-- Operations on vectors derived from operations on finite sets by duality
--------------------------------------------------------------------------------

||| Combines two vectors
vectCombine : Vect n a -> Vect m a -> Vect (n + m)  a
vectCombine v w = mapToVect ((either (vectToMap v) (vectToMap w)) . fSetSumInv)