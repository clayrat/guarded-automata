{-# OPTIONS --guarded #-}
module DA where

import Prelude as P hiding (Tactic-bishop-finite ; ord→is-discrete)
open P
open import Data.Unit
open import Data.Bool hiding (_⊕_)
open import Data.Dec
open import Data.List

open import Later
open import Clocked.Moore
open import Lang

private variable
  ℓ : Level
  A S : 𝒰 ℓ
  κ : Cl

record DA (A : 𝒰 ℓ) (S : 𝒰 ℓ) : 𝒰 ℓ where
  constructor mkDA
  field ν : (s : S) → Bool
        δ : (s : S) (a : A) → S

νs : DA A S → List S → Bool
νs da = any (DA.ν da)

δs : DA A S → List S → A → List S
δs da ss a = map (λ s → DA.δ da s a) ss

langᵏ-body : DA A S → ▹ κ (S → gLang κ A) → S → gLang κ A
langᵏ-body da l▹ s = Mreᵏ (DA.ν da s) λ a → l▹ ⊛ next (DA.δ da s a)

langᵏ : DA A S → S → gLang κ A
langᵏ {κ} da = fix {k = κ} (langᵏ-body da)

lang : DA A S → S → Lang A
lang da s κ = langᵏ da s

-- constructions

∅A : DA A ⊤
∅A = mkDA (λ _ → false) λ _ _ → tt

εA : DA A Bool
εA = mkDA id λ _ _ → false

data ST3 : 𝒰 where
  init acc err : ST3

charA : ⦃ dA : is-discrete A ⦄
      → A → DA A ST3
charA {A} a = mkDA cν cδ
  where
  cν : ST3 → Bool
  cν init = false
  cν acc = true
  cν err = false
  cδ : ST3 → A → ST3
  cδ init x = if ⌊ x ≟ a ⌋ then acc else err
  cδ acc  x = err
  cδ err  x = err

complA : DA A S → DA A S
complA da = mkDA (not ∘ DA.ν da) (DA.δ da)

-- product automaton
_⊕_ : ∀ {S₁ S₂ : 𝒰 ℓ}
     → DA A S₁ → DA A S₂ → DA A (S₁ × S₂)
da1 ⊕ da2 = mkDA (λ s → DA.ν da1 (s .fst) or DA.ν da2 (s .snd))
                  λ s a → (DA.δ da1 (s. fst) a) , (DA.δ da2 (s. snd) a)

-- power automaton
powA : DA A S → DA A (List S)
powA da = mkDA (νs da) (δs da)

powA-nilᵏ : (da : DA A S) → langᵏ {κ = κ} (powA da) [] ＝ ∅ᵏ
powA-nilᵏ {κ} da = fix {k = κ} λ ih▹ →
  langᵏ (powA da) []
    ＝⟨ ap (_$ []) (fix-path (langᵏ-body (powA da))) ⟩
  langᵏ-body (powA da) (next (langᵏ (powA da))) []
    ＝⟨ ap (Mreᵏ false) (fun-ext λ _ → ▹-ext ih▹) ⟩
  pureᵏ-body false (next ∅ᵏ)
    ＝˘⟨ fix-path (pureᵏ-body false) ⟩
  ∅ᵏ
    ∎

powA-nil : (da : DA A S) → lang (powA da) [] ＝ ∅
powA-nil da = fun-ext λ κ → powA-nilᵏ da

powA-consᵏ : (da : DA A S) (s : S) (ss : List S)
           → langᵏ {κ = κ} (powA da) (s ∷ ss) ＝ langᵏ da s ⋃ᵏ langᵏ (powA da) ss
powA-consᵏ {κ} da = fix {k = κ} λ ih▹ s ss →
  langᵏ (powA da) (s ∷ ss)
    ＝⟨ ap (_$ s ∷ ss) (fix-path (langᵏ-body (powA da))) ⟩
  langᵏ-body (powA da) (next (langᵏ (powA da))) (s ∷ ss)
    ＝⟨ ap² Mreᵏ refl (fun-ext λ a → ▹-ext (ih▹ ⊛ next (DA.δ da s a) ⊛ next (map (λ s′ → DA.δ da s′ a) ss))) ⟩
  apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (langᵏ-body da (next (langᵏ da)) s)) (langᵏ-body (powA da) (next (langᵏ (powA da))) ss)
    ＝˘⟨ zipWithᵏ-eq {f = _or_} {b = langᵏ-body da (next (langᵏ da)) s} ⟩
  (langᵏ-body da (next (langᵏ da)) s ⋃ᵏ langᵏ-body (powA da) (next (langᵏ (powA da))) ss)
    ＝˘⟨ ap (λ q → langᵏ-body da (next (langᵏ da)) s ⋃ᵏ q ss) (fix-path (langᵏ-body (powA da))) ⟩
  (langᵏ-body da (next (langᵏ da)) s ⋃ᵏ langᵏ (powA da) ss)
    ＝˘⟨ ap (λ q → q s ⋃ᵏ langᵏ (powA da) ss) (fix-path (langᵏ-body da)) ⟩
  langᵏ da s ⋃ᵏ langᵏ (powA da) ss
    ∎

powA-cons : (da : DA A S) (s : S) (ss : List S)
          → lang (powA da) (s ∷ ss) ＝ lang da s ⋃ lang (powA da) ss
powA-cons da s ss = fun-ext λ κ → powA-consᵏ da s ss

-- composition automaton
composeA : ∀ {S₁ S₂ : 𝒰 ℓ}
         → DA A S₁ → S₂ → DA A S₂ → DA A (S₁ × List S₂)
composeA da1 s da2 =
  mkDA (λ s12 → DA.ν da1 (s12 .fst) and DA.ν da2 s or νs da2 (s12 .snd))
       (λ s12 a → (  DA.δ da1 (s12 .fst) a)
                   , δs da2 (if DA.ν da1 (s12 .fst) then s ∷ s12 .snd else s12 .snd) a)
