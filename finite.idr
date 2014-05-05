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
cong2 : {f : t -> u -> v} -> (a = b) -> (a' = b') -> f a a' = f b b'
cong2 refl refl = refl

--------------------------------------------------------------------------------
-- Theorems about inequality
--------------------------------------------------------------------------------

||| Proof that if n <=m then n + (m - n) = m
|||
||| This is useful for showing that if n <=m then there is a k such that
||| n + k = m.
minusCancel : LTE n m -> n + (m - n) = m
minusCancel lteZero     = minusZeroRight _
minusCancel (lteSucc p) = eqSucc _ _ (minusCancel p)

||| Proof that LTE respects adding a constant to both sides
ltePlus : LTE m l -> (n : Nat) -> LTE (n + m) (n + l)
ltePlus p Z     = p
ltePlus p (S k) = lteSucc (ltePlus p k)

||| Proof that n <= n
lteN : (n : Nat) -> LTE n n
lteN n ?= ltePlus (lteZero {right=Z}) n

||| Proof that if n <= m and m <= l then n <= l
lteTrans : LTE n m -> LTE m l -> LTE n l
lteTrans lteZero _                = lteZero
lteTrans (lteSucc w) (lteSucc w') = lteSucc (lteTrans w w')

||| Dichotomy for lte
lteDichotomy : LTE n m -> Either (n = m) (LT n m)
lteDichotomy (lteZero {right=Z})     = Left refl
lteDichotomy (lteZero {right=(S k)}) = Right (lteSucc lteZero)
lteDichotomy (lteSucc p)             = f (lteDichotomy p)
  where f : Either (l = k) (LT l k) -> Either ((S l) = (S k)) (LT (S l) (S k))
        f (Left p) = Left (eqSucc _ _ p)
        f (Right p) = Right (lteSucc p)

||| Dichotomy
dichotomy : (n : Nat) -> (m : Nat) -> Either (LTE n m) (LT m n)
dichotomy Z _ = Left lteZero
dichotomy (S k) Z = Right (lteSucc lteZero)
dichotomy (S l) (S k) = f (dichotomy l k)
  where f : Either (LTE l k) (LT k l) -> Either (LTE (S l) (S k)) (LT (S k) (S l))
        f (Left p) = Left (lteSucc p)
        f (Right p) = Right (lteSucc p)

||| Trichotomy
trichotomy : (n : Nat) -> (m : Nat) -> Either (Either (n = m) (LT n m)) (LT m n)
trichotomy n m with (dichotomy n m)
                                 | Left a = Left (lteDichotomy a)
                                 | Right b = Right b

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

lteN_lemma_1 = proof {
  intros
  rewrite (cong2 {f=LTE} (plusCommutative n 0) (plusCommutative n 0))
  trivial
}
