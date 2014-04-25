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

--------------------------------------------------------------------------------
-- Misc vector operations
--------------------------------------------------------------------------------

||| like Prelude.Vect.findIndices but using Fin, not Nat
findIndices' : (a -> Bool) -> Vect m a -> (p ** Vect p (Fin m))
findIndices' p [] = (_ ** [])
findIndices' p (x::xs) with (findIndices' p xs)
      | (_ ** tail) =
       if p x then
        (_ ** fZ::(map fS tail))
       else
        (_ ** (map fS tail))



-- Heterogeneous (Mixed) Tuples

--Mixed tuple of order k
MixedTuple : (Fin k -> Type) -> Type
MixedTuple sig = (i : Fin _) -> sig i

--Pullback of dependent function
pullback : (a -> b) -> (b -> c) -> (a -> c)
pullback f = \g => g . f

pullback' : (s : a -> Type) -> (s' : b -> Type) -> (f : a -> b) -> s = s' . f -> ((y : b) -> s' y) -> ((x : a) -> s x)
pullback' s s' f p = \g => \x => rewrite p in (g (f x)) 

--(Unknown name) mapping from mixed tuples induced by mapping on signatures
myMap : (s : Fin k -> Type) -> (s' : Fin k' -> Type) -> (f : Fin k -> Fin k') -> s = s' . f -> MixedTuple s' -> MixedTuple s
myMap s s' f p g = pullback' s s' f p g


NDVector : (Fin k -> Nat) -> Type -> Type
NDVector s a = (MixedTuple (Fin . s)) -> a

