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

composeA-genᵏ : ∀ {S₁ S₂ : 𝒰 ℓ}
              → (da1 : DA A S₁) (da2 : DA A S₂)
              → (s1 : S₁) → (s2 : S₂) (ss : List S₂)
              → langᵏ {κ = κ} (composeA da1 s2 da2) (s1 , ss)
                  ＝
                (langᵏ da1 s1 ·ᵏ langᵏ da2 s2) ⋃ᵏ langᵏ (powA da2) ss
composeA-genᵏ {A} {κ} {S₁} {S₂} da1 da2 = fix {k = κ} λ ih▹ s1 s2 ss →
  langᵏ (composeA da1 s2 da2) (s1 , ss)
    ＝⟨ ap (_$ (s1 , ss)) (fix-path (langᵏ-body (composeA da1 s2 da2))) ⟩
  Mreᵏ (DA.ν da1 s1 and DA.ν da2 s2 or νs da2 ss)
       (λ a → next (langᵏ (composeA da1 s2 da2) ((DA.δ da1 s1 a) , δs da2 (if DA.ν da1 s1 then s2 ∷ ss else ss) a)))
    ＝⟨ ap² Mreᵏ refl (fun-ext λ a → ▹-ext λ α → go {ih▹ = ih▹}) ⟩
  apᵏ-body (next apᵏ)
   (mapᵏ-body _or_ (next (mapᵏ _or_))
    (·ᵏ-body (next _·ᵏ_) (langᵏ-body da1 (next (langᵏ da1)) s1) (langᵏ-body da2 (next (langᵏ da2)) s2)))
    (langᵏ-body (powA da2) (next (langᵏ (powA da2))) ss)
    ＝⟨ sym (zipWithᵏ-eq {b = (·ᵏ-body (next _·ᵏ_) (langᵏ-body da1 (next (langᵏ da1)) s1) (langᵏ-body da2 (next (langᵏ da2)) s2))}) ⟩
  (·ᵏ-body (next _·ᵏ_) (langᵏ-body da1 (next (langᵏ da1)) s1) (langᵏ-body da2 (next (langᵏ da2)) s2) ⋃ᵏ langᵏ-body (powA da2) (next (langᵏ (powA da2))) ss)
    ＝⟨ ap (λ q → q (langᵏ-body da1 (next (langᵏ da1)) s1) (langᵏ-body da2 (next (langᵏ da2)) s2) ⋃ᵏ langᵏ-body (powA da2) (next (langᵏ (powA da2))) ss)
           (sym $ fix-path ·ᵏ-body) ⟩
  ((langᵏ-body da1 (next (langᵏ da1)) s1 ·ᵏ langᵏ-body da2 (next (langᵏ da2)) s2) ⋃ᵏ langᵏ-body (powA da2) (next (langᵏ (powA da2))) ss)
    ＝⟨ ap (λ q → (q s1 ·ᵏ langᵏ-body da2 (next (langᵏ da2)) s2) ⋃ᵏ langᵏ-body (powA da2) (next (langᵏ (powA da2))) ss) (sym $ fix-path (langᵏ-body da1)) ⟩
  ((langᵏ da1 s1 ·ᵏ langᵏ-body da2 (next (langᵏ da2)) s2) ⋃ᵏ langᵏ-body (powA da2) (next (langᵏ (powA da2))) ss)
    ＝⟨ ap (λ q → (langᵏ da1 s1 ·ᵏ q s2) ⋃ᵏ langᵏ-body (powA da2) (next (langᵏ (powA da2))) ss) (sym $ fix-path (langᵏ-body da2)) ⟩
  ((langᵏ da1 s1 ·ᵏ langᵏ da2 s2) ⋃ᵏ langᵏ-body (powA da2) (next (langᵏ (powA da2))) ss)
    ＝⟨ ap (λ q → (langᵏ da1 s1 ·ᵏ langᵏ da2 s2) ⋃ᵏ q ss) (sym $ fix-path (langᵏ-body (powA da2))) ⟩
  ((langᵏ da1 s1 ·ᵏ langᵏ da2 s2) ⋃ᵏ langᵏ (powA da2) ss)
    ∎
  where
  go : {ih▹ : ▹ κ ((s1 : S₁) (s2 : S₂) (ss : List S₂)
                   → langᵏ {κ = κ} (composeA da1 s2 da2) (s1 , ss) ＝ ((langᵏ da1 s1 ·ᵏ langᵏ da2 s2) ⋃ᵏ langᵏ (powA da2) ss)) }
       {s1 : S₁} {s2 : S₂} {ss : List S₂} {a : A} → {@tick α : Tick κ}
     → (langᵏ (composeA da1 s2 da2) (DA.δ da1 s1 a , δs da2 (if DA.ν da1 s1 then s2 ∷ ss else ss) a))
         ＝
       ((▹map _⋃ᵏ_ (condᵏ (DA.ν da1 s1) (next ((langᵏ da1 (DA.δ da1 s1 a)) ·ᵏ (Mreᵏ (DA.ν da2 s2) (λ a₁ → next (langᵏ da2 (DA.δ da2 s2 a₁))))))
                                        (next (langᵏ da2 (DA.δ da2 s2 a))))
                ⊛ (next (langᵏ (powA da2) (δs da2 ss a)))) α)
  go {ih▹} {s1} {s2} {ss} {a} {α} with DA.ν da1 s1
  ... | true  =
         (langᵏ (composeA da1 s2 da2) (DA.δ da1 s1 a , δs da2 (s2 ∷ ss) a))
           ＝⟨ ih▹ α (DA.δ da1 s1 a) s2 (δs da2 (s2 ∷ ss) a) ⟩
         ((langᵏ da1 (DA.δ da1 s1 a) ·ᵏ langᵏ da2 s2) ⋃ᵏ ⌜ langᵏ (powA da2) (δs da2 (s2 ∷ ss) a) ⌝)
           ＝⟨ ap! (powA-consᵏ da2 (DA.δ da2 s2 a) (δs da2 ss a)) ⟩
         ((langᵏ da1 (DA.δ da1 s1 a) ·ᵏ langᵏ da2 s2) ⋃ᵏ (langᵏ da2 (DA.δ da2 s2 a) ⋃ᵏ langᵏ (powA da2) (δs da2 ss a)))
           ＝⟨ ap (λ q → (langᵏ da1 (DA.δ da1 s1 a) ·ᵏ q s2) ⋃ᵏ (langᵏ da2 (DA.δ da2 s2 a) ⋃ᵏ langᵏ (powA da2) (δs da2 ss a))) (fix-path (langᵏ-body da2)) ⟩
         (langᵏ da1 (DA.δ da1 s1 a) ·ᵏ Mreᵏ (DA.ν da2 s2) (λ a₁ → next (langᵏ da2 (DA.δ da2 s2 a₁)))) ⋃ᵏ (langᵏ da2 (DA.δ da2 s2 a) ⋃ᵏ langᵏ (powA da2) (δs da2 ss a))
           ＝⟨ sym (unionᵏ-assoc {k = langᵏ da1 (DA.δ da1 s1 a) ·ᵏ Mreᵏ (DA.ν da2 s2) (λ a₁ → next (langᵏ da2 (DA.δ da2 s2 a₁)))}) ⟩
         (((langᵏ da1 (DA.δ da1 s1 a) ·ᵏ Mreᵏ (DA.ν da2 s2) (λ a₁ → next (langᵏ da2 (DA.δ da2 s2 a₁)))) ⋃ᵏ langᵏ da2 (DA.δ da2 s2 a)) ⋃ᵏ langᵏ (powA da2) (δs da2 ss a))
            ∎
  ... | false =
         (langᵏ (composeA da1 s2 da2) (DA.δ da1 s1 a , δs da2 ss a))
           ＝⟨ ih▹ α (DA.δ da1 s1 a) s2 (δs da2 ss a) ⟩
         ((langᵏ da1 (DA.δ da1 s1 a) ·ᵏ langᵏ da2 s2) ⋃ᵏ langᵏ (powA da2) (δs da2 ss a))
           ＝⟨ ap (λ q → (langᵏ da1 (DA.δ da1 s1 a) ·ᵏ q s2) ⋃ᵏ langᵏ (powA da2) (δs da2 ss a)) (fix-path (langᵏ-body da2)) ⟩
         ((langᵏ da1 (DA.δ da1 s1 a) ·ᵏ (Mreᵏ (DA.ν da2 s2) (λ a₁ → next (langᵏ da2 (DA.δ da2 s2 a₁))))) ⋃ᵏ (langᵏ (powA da2) (δs da2 ss a)))
           ∎

composeA-gen : ∀ {S₁ S₂ : 𝒰 ℓ}
              → (da1 : DA A S₁) (da2 : DA A S₂)
              → (s1 : S₁) (s2 : S₂) (ss : List S₂)
              → lang (composeA da1 s2 da2) (s1 , ss)
                  ＝
                (lang da1 s1 · lang da2 s2) ⋃ lang (powA da2) ss
composeA-gen da1 da2 s1 s2 ss = fun-ext λ κ → composeA-genᵏ da1 da2 s1 s2 ss

composeA-correct : ∀ {S₁ S₂ : 𝒰 ℓ}
                 → (da1 : DA A S₁) (da2 : DA A S₂)
                 → (s1 : S₁) (s2 : S₂)
                 → lang (composeA da1 s2 da2) (s1 , []) ＝ lang da1 s1 · lang da2 s2
composeA-correct da1 da2 s1 s2 =
    composeA-gen da1 da2 s1 s2 []
  ∙ ap ((lang da1 s1 · lang da2 s2) ⋃_) (powA-nil da2)
  ∙ union-comm {k = lang da1 s1 · lang da2 s2}
  ∙ union-empty-l {l = lang da1 s1 · lang da2 s2}
