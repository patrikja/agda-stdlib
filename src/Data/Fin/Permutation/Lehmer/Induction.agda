------------------------------------------------------------------------
-- The Agda standard library
--
-- Induction principle and views for Lehmer code permutations
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Fin.Permutation.Lehmer.Induction where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc; punchIn)
open import Data.Fin.Permutation.Lehmer.Base using (Permutation; nil; _:-_; insert; pinch)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- PView

data PView : {n : ℕ} → (i : Fin n) → Set where
  Split : {n : ℕ} {i : Fin (suc n)} → (pᵢ : Fin (suc n)) → (ps : Permutation n) → PView i

-- splitView decomposes a permutation based on where index i is mapped.
splitView : (i : Fin n) → Permutation n → PView i
splitView  zero     (p :- ps) = Split p ps
splitView  (suc i)  (p :- ps) with splitView i ps
... | Split pᵢ ps' = Split (punchIn p pᵢ) (pinch i p :- ps' )

------------------------------------------------------------------------
-- Composition via SplitView

compose : Permutation n → Permutation n → Permutation n
compose {zero}  nil  nil       = nil
compose {suc n} ps   (i :- qs) with splitView i ps
... | Split pᵢ ps' = pᵢ :- compose ps' qs
