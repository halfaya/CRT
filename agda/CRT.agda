module CRT where

open import Data.Integer using (ℤ; -_; +_; _*_; _+_)
open import Data.Integer.DivMod
open import Data.Integer.Properties using (+-comm; +-assoc; pos-*; +-inverseʳ; neg-distribˡ-*)
open import Data.Nat hiding (_+_) renaming (_*_ to _*ℕ_)
open import Data.Nat.GCD
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd) 
open import Relation.Binary.PropositionalEquality

-- All this work is required to prove 1 + xm = yn → 1 = yn - xm
Lemma : (m n x y : ℕ) → suc (x *ℕ m) ≡ y *ℕ n → (+ 1) ≡ (+ y) * (+ n) + (- (+ x)) * (+ m)
Lemma m n x y p =
  let e1 : + (suc (x *ℕ m)) ≡ + (y *ℕ n)
      e1 = cong +_ p
      e2 : + (suc (x *ℕ m)) ≡ (+ y) * (+ n)
      e2 = subst (+ (suc (x *ℕ m)) ≡_) (pos-* y n) e1
      e3 : (+ 1) + ((+ x) * (+ m)) ≡ (+ y) * (+ n)
      e3 = subst (λ z → (+ 1) + z ≡ (+ y) * (+ n)) (pos-* x m) e2
      e4 : (+ 1) + ((+ x) * (+ m)) + (- (+ x)) * (+ m) ≡ (+ y) * (+ n) + (- (+ x)) * (+ m)
      e4 = cong (λ z → z + (- (+ x)) * (+ m)) e3
      e5 : (+ 1) + (((+ x) * (+ m)) + (- (+ x)) * (+ m)) ≡ (+ y) * (+ n) + (- (+ x)) * (+ m)
      e5 = subst (λ z → z ≡ (+ y) * (+ n) + (- (+ x)) * (+ m)) (+-assoc (+ 1) (((+ x) * (+ m))) ((- (+ x)) * (+ m))) e4
      e6 : (+ 1) + (((+ x) * (+ m)) + (- ((+ x) * (+ m)))) ≡ (+ y) * (+ n) + (- (+ x)) * (+ m)
      e6 = subst (λ z → (+ 1) + (((+ x) * (+ m)) + z) ≡ (+ y) * (+ n) + (- (+ x)) * (+ m)) (sym (neg-distribˡ-* (+ x) (+ m))) e5
      e7 : (+ 1) + (+ 0) ≡ (+ y) * (+ n) + (- (+ x)) * (+ m)
      e7 = subst (λ z → (+ 1) + z ≡ (+ y) * (+ n) + (- (+ x)) * (+ m)) (+-inverseʳ (((+ x) * (+ m)))) e6 
  in e7

Bezout : (m n : ℕ) → .{{_ : NonZero m}} → .{{_ : NonZero n}} →
         Bézout.Identity.Identity 1 m n →
         Σ (ℤ × ℤ) (λ ab → (+ 1) ≡ fst ab * (+ m) + snd ab * (+ n))
Bezout m n (Bézout.+- x y eq) =
  let e : + 1 ≡ + x * + m + - (+ y) * + n
      e = Lemma n m y x eq
  in (+ x , - (+ y)) , e
Bezout m n (Bézout.-+ x y eq) =
  let e1 : + 1 ≡ + y * + n + - (+ x) * + m
      e1 = Lemma m n x y eq
      e2 : + 1 ≡ - (+ x) * + m + + y * + n
      e2 = subst (+ 1 ≡_) (+-comm (+ y * + n) (- (+ x) * + m)) e1
  in (- (+ x) , + y) , e2

-- This is a straightforward calculation, but too tedious given the current state
-- of the standard library.
postulate 
  BtoCRT : (m n a b : ℕ) (c d : ℤ) → .{{_ : NonZero m}} → .{{_ : NonZero n}} →
           (+ 1) ≡ c * (+ m) + d * (+ n) →
           Σ ℤ (λ x → x %ℕ m ≡ (+ a) %ℕ m × x %ℕ n ≡ (+ b) %ℕ n)
{-
  BtoCRT m n a b c d p =
    let x = (+ b) * (c * (+ m)) + (+ a) * (d * (+ n)) -- this is the value that works
    in ??
-}

CRT2' : (m n a b : ℕ) → .{{_ : NonZero m}} → .{{_ : NonZero n}} →
        Bézout.Identity.Identity 1 m n →
        Σ ℤ (λ x → x %ℕ m ≡ (+ a) %ℕ m × x %ℕ n ≡ (+ b) %ℕ n)
CRT2' m n a b i =
  let ((c , d) , p) = Bezout m n i
  in BtoCRT m n a b c d p

CRT2 : (m n a b : ℕ) → .{{_ : NonZero m}} → .{{_ : NonZero n}} → gcd m n ≡ 1 →
       Σ ℤ (λ x → x %ℕ m ≡ (+ a) %ℕ m × x %ℕ n ≡ (+ b) %ℕ n)
CRT2 m n a b p =
  let g : GCD m n 1
      g = subst (GCD m n) p (gcd-GCD m n)
      i : Bézout.Identity.Identity 1 m n
      i = Bézout.identity g
  in CRT2' m n a b i

