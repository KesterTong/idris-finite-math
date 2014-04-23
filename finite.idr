module Finmath.Finite

--------------------------------------------------------------------------------
-- Cartesian sums and products of finite sets
--------------------------------------------------------------------------------

||| Map an element of either of two sets, into their Cartesian sum
fSetSum : Either (Fin n) (Fin m) -> Fin (n + m)
fSetSum (Left fZ)               = fZ
fSetSum (Left (fS k))           = fS (fSetSum (Left k))
fSetSum {n=Z} (Right right)     = right
fSetSum {n=(S k)} (Right right) = fS (fSetSum {n=k} (Right right))

||| Map a pair of elements from each of two sets, into their Cartesian product
fSetProduct : (Fin n, Fin m) -> Fin (n * m)
fSetProduct (fZ, right) = fSetSum (Left right)
fSetProduct {n=(S k)} ((fS left), right) = fSetSum (Right (fSetProduct (left, right)))

||| The inverse map of fSetSum
fSetSumInv : Fin (n + m) -> Either (Fin n) (Fin m)
fSetSumInv {n=Z} x      = Right x
fSetSumInv {n=(S k)} fZ = Left fZ
fSetSumInv {n=(S k)} (fS c) with (fSetSumInv {n=k} c)
                                 | Left a = Left (fS a)
                                 | Right b = Right b

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

||| Functions respect equality
fEq : (f : a -> b) -> (left : a) -> (right : a) -> (p : left = right) -> f left = f right
fEq f left _ refl = refl

--------------------------------------------------------------------------------
-- Proofs about inequality
--------------------------------------------------------------------------------

||| Proof that LTE respects adding a constant to both sides
ltePlus : LTE m l -> (n : Nat) -> LTE (n + m) (n + l)
ltePlus p Z     = p
ltePlus p (S k) = lteSucc (ltePlus p k)

||| Proof that n <= n
lteN : (n : Nat) -> LTE n n
lteN n = (rewrite (fEq (\k => LTE n k) _ _ (plusCommutative 0 n)) in 
  (rewrite (fEq (\k => LTE k (n + 0)) _ _ (plusCommutative 0 n)) in 
    (ltePlus (lteZero {right=Z}) n)))


