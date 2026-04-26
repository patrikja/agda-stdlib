------------------------------------------------------------------------
-- The Agda standard library
--
-- Combinatorial operations (Swaps and Johnson-Trotter)
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Fin.Permutation.Lehmer.Combinatorics where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc; inject₁)
open import Data.Bool.Base using (Bool; false; true; not; _xor_)
open import Data.List.Base using (List; []; _∷_; [_]; _++_; map; reverse)
open import Data.List.Scans.Base using (scanl)
open import Function.Base using (_∘_)
open import Data.Fin.Permutation.Lehmer.Base using (Permutation; nil; _:-_; id; _∙_)

private
  variable
    n : ℕ

-- Parity
-- TODO |finParity| is probably aready available - import instead

finParity : Fin n → Bool
finParity zero    = false
finParity (suc i) = not (finParity i)

parity : Permutation n → Bool
parity nil       = false
parity (p :- ps) = (finParity p) xor (parity ps)

data Swap : ℕ → Set where
  swap : Fin n → Swap (suc n)

unswap : Swap (suc n) → Fin n
unswap (swap i) = i

lift : ∀ {n m} → (Fin n → Fin m) → Swap (suc n) → Swap (suc m)
lift f = swap ∘ f ∘ unswap

applySwap : Swap n → Permutation n
applySwap (swap zero)     = suc zero :- id
applySwap (swap (suc i))  = zero :- applySwap (swap i)

_□_ : {A : Set} → List A → List A → List A
[] □ ys       = ys
(x ∷ xs) □ ys = ys ++ [ x ] ++ (xs □ reverse ys)

swaps : {n : ℕ} → List (Swap (suc n))
swaps {zero}   = []
swaps {suc n}  = swap zero ∷ map (lift suc) swaps

bump-even : List (Swap n) → List (Swap (suc n))
bump-even []                   = []
bump-even (swap x ∷ [])        = swap (suc x) ∷ []
bump-even (swap x ∷ swap y ∷ xs) = swap (suc x) ∷ swap (Data.Fin.Base.inject₁ y) ∷ bump-even xs

jcode : (n : ℕ) → List (Swap n)
jcode zero     = []
jcode (suc i)  = (bump-even (jcode i)) □ (reverse swaps)

johnson-trotter : {n : ℕ} → List (Permutation n)
johnson-trotter {zero}   = [ nil ]
johnson-trotter {suc n}  = scanl (λ p s → p ∙ applySwap s) id (jcode (suc n))
