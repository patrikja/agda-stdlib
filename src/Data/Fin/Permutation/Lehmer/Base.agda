------------------------------------------------------------------------
-- The Agda standard library
--
-- Core types and operations for permutations as Lehmer codes
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Fin.Permutation.Lehmer.Base where

open import Data.Nat.Base using (ℕ; zero; suc; 2+)
open import Data.Fin.Base using (Fin; zero; suc; punchIn; punchOut)
open import Data.Fin.Patterns using (0F; 1F)
open import Data.Fin.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Function.Base using (_∘_)

private
  variable
    n : ℕ
------------------------------------------------------------------------
-- Types

-- A permutation represented as a Lehmer code.
data Permutation : ℕ → Set where
  nil  : Permutation zero
  _:-_ : Fin (suc n) → Permutation n → Permutation (suc n)

infixr 6 _:-_

------------------------------------------------------------------------
-- Application

-- Semantics of applying a permutation to a finite index.
apply : Permutation n → (Fin n → Fin n)
apply (p₀ :- ps) zero    = p₀
apply (p₀ :- ps) (suc i) = punchIn p₀ (apply ps i)

-- Synonym / alternative notation (see also |_⟨$⟩ˡ_ = unapply| later)
_⟨$⟩ʳ_ = apply

-- Synonym / alternative notation
⟦_⟧ : Permutation n → (Fin n → Fin n)
⟦_⟧ = apply

------------------------------------------------------------------------
-- Base instances

id : Permutation n
id {zero}  = nil
id {suc n} = zero :- id

------------------------------------------------------------------------
-- Helper operations on Fin

-- |pinch| could perhaps be added to Data.Fin.Base if it isn't there now
pinch : Fin n → Fin (suc n) → Fin n
pinch {suc n}  _        zero     = zero
pinch {suc n}  zero     (suc j)  = j
pinch {suc n}  (suc i)  (suc j)  = suc (pinch i j)

------------------------------------------------------------------------
-- Operations: Insertion and Removal

-- Inserts a new mapping i ↦ pᵢ into a permutation of n elements.
insert : (i : Fin (suc n)) → (pᵢ : Fin (suc n)) → Permutation n → Permutation (suc n)
insert zero     pᵢ  ps         = pᵢ :- ps
insert (suc i)  pᵢ  (p₀ :- ps) = punchIn pᵢ p₀ :- insert i (pinch p₀ pᵢ) ps

-- Removes the mapping for index i, resulting in a permutation of n elements.
remove : Fin (suc n) → Permutation (suc n) → Permutation n
remove          zero    (p :- ps) = ps
remove {suc _} (suc i)  (p :- ps) = pinch (apply ps i) p :- remove i ps

------------------------------------------------------------------------
-- Composition

-- This is now (∙; BULLET OPERATOR; \.) but could be (·; MIDDLE DOT; \cdot) or (∘; RING OPERATOR; \o)
infixr 9 _∙_

-- Standard mathematical composition (right-to-left)
_∙_ : Permutation n → Permutation n → Permutation n
nil  ∙ nil        = nil
ps   ∙ (q :- qs)  = apply ps q :- (remove q ps ∙ qs)

-- Forward/diagrammatic composition (left-to-right)
infixl 9 _∘ₚ_
_∘ₚ_ : Permutation n → Permutation n → Permutation n
ps ∘ₚ qs = qs ∙ ps

------------------------------------------------------------------------
-- Inverses

-- unapply finds the index that maps to a given value
unapply : Permutation n → (Fin n → Fin n)
unapply (p :- ps) i with p ≟ i
... | yes p≡i = zero
... | no  p≢i = suc (unapply ps (punchOut p≢i))

_⟨$⟩ˡ_ = unapply

-- Inverse permutation:  inverse p ∙ p  ≡  p ∙ inverse p  ≡  id
inverse : Permutation n → Permutation n
inverse {zero}  nil = nil
inverse {suc n} ps  = j :- inverse (remove j ps)
  where j = unapply ps zero

-- More operations

-- swap the two first positions, "lift" the rest twice
swap : Permutation n → Permutation (2+ n)
swap ps = 1F :- 0F :- ps

-- reverse "maps i to n - i" for i in {0..n-1}
reverse : (n : ℕ) → Permutation n
reverse zero    = nil
reverse (suc n) = Data.Fin.Base.fromℕ n :- reverse n

-- TODO transpose

-- TODO Probably should be just imported from generic Group module somewhere
-- TODO or, using this as a specification, compute/calculate a specialised version not using composition, nor inverse
conjugation : Permutation n → Permutation n → Permutation n
conjugation g x = g ∙ (x ∙ inverse g)
