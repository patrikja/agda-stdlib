------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Lehmer code permutations
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Fin.Permutation.Lehmer.Properties where

open import Data.Fin.Permutation.Lehmer.Base
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc; punchIn; punchOut)
import Function.Base as Fun
open Fun using (_∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Empty using (⊥-elim)
open import Data.Fin.Properties using (punchInᵢ≢i; punchIn-injective; punchIn-punchOut; _≟_)
open import Relation.Nullary using (yes; no)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Application Equalities

infix 6 _≐_
_≐_ : {A B : Set} → (A → B) → (A → B) → Set
_≐_ {A} f g = ∀ (x : A) → f x ≡ g x

id-is-id : apply (id {n}) ≐ Fun.id
id-is-id zero    = refl
id-is-id (suc i) = cong suc (id-is-id i)

------------------------------------------------------------------------
-- Injectivity Lemmas

apply-inj : (ps : Permutation n) (i j : Fin n) → apply ps i ≡ apply ps j → i ≡ j
apply-inj (p :- ps) zero zero eq = refl
apply-inj (p :- ps) zero (suc j) eq = ⊥-elim (punchInᵢ≢i p _ (sym eq))
apply-inj (p :- ps) (suc i) zero eq = ⊥-elim (punchInᵢ≢i p _ eq)
apply-inj (p :- ps) (suc i) (suc j) eq =
  cong suc (apply-inj ps i j (punchIn-injective p _ _ eq))

------------------------------------------------------------------------
-- Structural properties

punchIn-pinch : (i : Fin (suc n)) (j : Fin n) →  i ≡ punchIn (punchIn i j) (pinch j i)
punchIn-pinch {n = suc n} zero     j        = refl
punchIn-pinch {n = suc n} (suc i) zero      = refl
punchIn-pinch {n = suc n} (suc i) (suc j)   = cong suc (punchIn-pinch i j)

punchIn-assoc : (i : Fin n) (j : Fin (suc n)) (k : Fin (suc (suc n))) →
  punchIn k (punchIn j i) ≡ punchIn (punchIn k j) (punchIn (pinch j k) i)
punchIn-assoc i        j        zero     = refl
punchIn-assoc i        zero     (suc k)  = refl
punchIn-assoc zero     (suc j)  (suc k)  = refl
punchIn-assoc (suc i)  (suc j)  (suc k)  = cong suc (punchIn-assoc i j k)

punchIn-apply : (qs : Permutation (suc n)) (j : Fin (suc n)) (i : Fin n) →
  apply qs (punchIn j i) ≡ punchIn (apply qs j) (apply (remove j qs) i)
punchIn-apply (q :- qs) zero     i       = refl
punchIn-apply (q :- qs) (suc j) zero     = punchIn-pinch q (apply qs j)
punchIn-apply (q :- qs) (suc j) (suc i)  = begin
    apply (q :- qs) (punchIn (suc j) (suc i))
  ≡⟨ refl ⟩
    apply (q :- qs) (suc (punchIn j i))
  ≡⟨ refl ⟩
    punchIn q (apply qs (punchIn j i))
  ≡⟨ cong (punchIn q) (punchIn-apply qs j i) ⟩
    punchIn q (punchIn (apply qs (j)) (apply (remove j qs) i))
  ≡⟨ punchIn-assoc (apply (remove j qs) i) (apply qs j) q  ⟩
    punchIn (punchIn q (apply qs j)) (punchIn (pinch (apply qs j) q) (apply (remove j qs) i))
  ≡⟨ refl ⟩
    punchIn (apply (q :- qs) (suc j)) (apply (remove (suc j) (q :- qs)) (suc i))
  ∎

------------------------------------------------------------------------
-- Composition Properties

compose-correct : (ps qs : Permutation n) (i : Fin n) → apply ps (apply qs i) ≡ apply (ps ∙ qs) i
compose-correct {n = suc _} (p :- ps) (q :- qs) zero = refl
compose-correct (p₁ :- ps₁) (q :- qs) (suc i) = begin
    apply (p₁ :- ps₁) (apply (q :- qs) (suc i))
  ≡⟨ refl ⟩
    apply (p₁ :- ps₁) (punchIn q (apply qs i))
  ≡⟨ punchIn-apply (p₁ :- ps₁) q (apply qs i) ⟩
    punchIn (apply (p₁ :- ps₁) q) (apply (remove q (p₁ :- ps₁)) (apply qs i))
  ≡⟨ cong (punchIn _) (compose-correct (remove q (p₁ :- ps₁)) qs i) ⟩
    punchIn (apply (p₁ :- ps₁) q) (apply (remove q (p₁ :- ps₁) ∙ qs) i)
  ≡⟨ refl ⟩
    apply ((p₁ :- ps₁) ∙ (q :- qs)) (suc i)
  ∎

-- TODO
-- open import Data.Fin.Permutation.Lehmer.Induction
-- compose-≡-∙ : (ps qs : Permutation n) → compose ps qs ≡ ps ∙ qs

------------------------------------------------------------------------
-- Inverse Properties

apply-unapply : (ps : Permutation n) (i : Fin n) → apply ps (unapply ps i) ≡ i
apply-unapply {n = suc _} (p :- ps) i with  p ≟ i
... | yes refl = refl
... | no p≢i = begin
      apply (p :- ps) (suc (unapply ps (punchOut p≢i)))
    ≡⟨ refl ⟩
      punchIn p (apply ps (unapply ps (punchOut p≢i)))
    ≡⟨ cong (punchIn p) (apply-unapply ps (punchOut p≢i)) ⟩
      punchIn p (punchOut p≢i)
    ≡⟨ punchIn-punchOut p≢i ⟩
      i
    ∎

inverse-id     : {n : ℕ} → inverse id ≡ id {n}
inverse-id {zero} = refl
inverse-id {suc n} = cong (zero :-_) inverse-id

inverse-prop₁  : {n : ℕ} → (ps : Permutation n) → (ps  ∙  inverse ps) ≡ id
inverse-prop₁ {zero}   nil        = refl
inverse-prop₁ {suc n}  (p :- ps)  =
    ((p :- ps) ∙ (inverse (p :- ps)))
  ≡⟨ refl ⟩
    let  p0 = unapply (p :- ps) zero
         ps' = remove p0 (p :- ps) in
    apply (p :- ps) p0 :- (ps' ∙ inverse ps')
  ≡⟨ cong₂ _:-_ (apply-unapply (p :- ps) zero) (inverse-prop₁ ps') ⟩
    zero :- id
  ≡⟨ refl ⟩
    id
  ∎

{-
-- TODO: inverse-prop₂, etc.
inverse-prop₂  : {n : ℕ} → (ps : Permutation n) → (inverse ps  ∙  ps) ≡ id
inverse-prop₂ {zero}   nil        = refl
inverse-prop₂ {suc n}  (p :- ps)  = {!!}


The inverse proof in the other direction is more work, given that
compose is defined by induction over the second argument.

The proof relies of two main lemmas: invert-head and invert-remove. The
following two lemmas make it a bit easier to do some of the steps in
their proofs.
-}
abstract

  unapply≡ : (i : Fin (suc n)) (ps : Permutation n) →
    unapply (i :- ps) i ≡ zero
  unapply≡ i ps with i ≟ i
  ... | yes i≡i = refl
  ... | no i≢i  = ⊥-elim (i≢i refl)

  unapply≢ : (i p : Fin (suc n)) (ps : Permutation n) → (neq : p ≢ i) →
    unapply (p :- ps) i ≡ suc (unapply ps (punchOut neq))
  unapply≢ i p ps p≢i with p ≟ i
  ... | yes p≡i = ⊥-elim (p≢i p≡i)
  ... | no  p≢i = refl

inverse-suc-step : (p : Fin (suc n)) (ps : Permutation (suc n)) →
  ⟦ inverse (suc p :- ps) ⟧ (suc p) ≡ let p0 = suc (unapply ps zero) in
  punchIn p0 (⟦ inverse (remove p0 (suc p :- ps)) ⟧ p)
inverse-suc-step p ps =
  cong  (λ □ → punchIn □ (⟦ inverse (remove □ (suc p :- ps)) ⟧ p))
        (unapply≢ zero (suc p) ps \())

{-

\begin{code}

inverse-step : (i : Fin (suc n)) (ps : Permutation (suc n)) →
  inverse (remove (suc (unapply ps zero)) (suc i :- ps)) ≡ inverse (i :- remove (unapply ps zero) ps)
inverse-step i ps rewrite apply-unapply ps zero = refl
\end{code}

<<invert-head-type>>
\begin{code}
invert-head : (p : Fin (suc n)) (ps : Permutation n) →
  ⟦ inverse (p :- ps) ⟧ p ≡ zero
\end{code}

<<invert-head-proof>
\begin{code}
invert-head zero ps = unapply≡ zero ps
invert-head {n = suc _} (suc p) ps =
    ⟦ inverse (suc p :- ps) ⟧ (suc p)
  ≡⟨ inverse-suc-step p ps ⟩
    let  j = unapply ps zero in
    punchIn (suc j) (⟦ inverse (remove (suc j) (suc p :- ps)) ⟧ p)
  ≡⟨ refl ⟩
    punchIn (suc j) (⟦ inverse (pinch (⟦ ps ⟧ j) (suc p) :- (remove j ps)) ⟧ p)
  ≡⟨ cong (λ □ → punchIn (suc j) (⟦ inverse (pinch □ (suc p) :- (remove j ps)) ⟧ p)) (apply-unapply ps zero) ⟩
    punchIn (suc j) (⟦ inverse (pinch zero (suc p) :- (remove j ps)) ⟧ p )
  ≡⟨ refl ⟩
    punchIn (suc j) (⟦ inverse (p :- (remove j ps)) ⟧ p )
  ≡⟨ cong (punchIn (suc j)) (invert-head p (remove j ps)) ⟩
    zero
  ∎
\end{code}

This is a tricky lemma to prove... It is used in the inverse-prop₂ proof.
<<invert-remove>>
\begin{code}
invert-remove : (i : Fin (suc n)) (ps : Permutation n) →
  let j = unapply (i :- ps) zero in
  remove i (j :- inverse (split j (i :- ps))) ≡ inverse ps
-- Base case where i is zero
invert-split zero ps =
    let j = unapply (zero :- ps) zero in
    inverse (split j (zero :- ps))
  ≡⟨ cong (λ □ → inverse (split □ (zero :- ps))) (unapply≡ zero ps) ⟩
    inverse (split zero (zero :- ps))
  ≡⟨ refl ⟩
    inverse ps ∎
-- Inductive step where i is suc i
invert-split {n = suc _} (suc i) ps =
    let j   = unapply ps zero in
    let ps' = inverse (split (suc j) (suc i :- ps)) in
    split (suc i) (unapply (suc i :- ps) zero :- inverse (split (unapply (suc i :- ps) zero) (suc i :- ps)))
  ≡⟨ cong (λ □ → split (suc i) (□ :- inverse (split □ (suc i :- ps)))) (unapply≢ zero (suc i) ps (λ())) ⟩
    pinch (⟦ ps' ⟧ i) (suc j) :- split i ps'
  ≡⟨ cong (λ □ → pinch (⟦ □ ⟧ i) (suc j) :- split i □) (inverse-step i ps) ⟩
    pinch (⟦ inverse (i :- split j ps) ⟧ i) (suc j) :- split i (inverse (i :- split j ps))
  ≡⟨ cong₂ (λ □ ■ → pinch □ (suc j) :- ■) (invert-head i _) (invert-split i (split j ps)) ⟩
    pinch zero (suc j) :- inverse (split j ps)
  ≡⟨ refl ⟩
    j :- inverse (split j ps)
  ≡⟨ refl ⟩
    inverse ps
  ∎
\end{code}

<<inverse-prop₂>>
\begin{code}
inverse-prop₂ nil      = refl
inverse-prop₂ (p :- ps) =  cong₂ _:-_ (invert-head p ps)
    let j = unapply (p :- ps) zero in
    (split p (j :- inverse (split j (p :- ps)))) · ps
  ≡⟨ cong (_· ps) (invert-split p ps) ⟩
    (inverse ps) · ps
  ≡⟨ inverse-prop₂ ps ⟩
    idₚ
  ∎
\end{code}


-}

