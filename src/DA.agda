{-# OPTIONS --guarded #-}
module DA where

import Prelude as P hiding (Tactic-bishop-finite ; ord→is-discrete)
open P
open import Data.Unit
open import Data.Bool hiding (_⊕_)
open import Data.Dec
open import Data.Maybe as Maybe
open import Data.List

open import Later
open import Clocked.Moore
open import Lang

private variable
  ℓ : Level
  A S S₁ S₂ : 𝒰 ℓ
  κ : Cl

record DA (A : 𝒰 ℓ) (S : 𝒰 ℓ) : 𝒰 ℓ where
  constructor mkDA
  field ν : (s : S) → Bool
        δ : (s : S) (a : A) → S

unroll : DA A S → S → Bool × (A → S)
unroll da s = (DA.ν da s , DA.δ da s)

νs : DA A S → List S → Bool
νs da = any (DA.ν da)

δs : DA A S → List S → A → List S
δs da ss a = map (λ s → DA.δ da s a) ss

langᵏ : DA A S → S → gLang κ A
langᵏ = unfoldᵏ ∘ unroll

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
_⊕_ : DA A S₁ → DA A S₂ → DA A (S₁ × S₂)
da1 ⊕ da2 = mkDA (λ s → DA.ν da1 (s .fst) or DA.ν da2 (s .snd))
                  λ s a → (DA.δ da1 (s. fst) a) , (DA.δ da2 (s. snd) a)

-- power automaton
powA : DA A S → DA A (List S)
powA da = mkDA (νs da) (δs da)

powA-nilᵏ : (da : DA A S) → langᵏ {κ = κ} (powA da) [] ＝ ∅ᵏ
powA-nilᵏ {κ} da = fix {k = κ} λ ih▹ →
  langᵏ (powA da) []
    ＝⟨ ap (_$ []) (fix-path (unfoldᵏ-body (unroll $ powA da))) ⟩
  unfoldᵏ-body (unroll $ powA da) (next (langᵏ (powA da))) []
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
    ＝⟨ ap (_$ s ∷ ss) (fix-path (unfoldᵏ-body (unroll $ powA da))) ⟩
  unfoldᵏ-body (unroll $ powA da) (next (langᵏ (powA da))) (s ∷ ss)
    ＝⟨ ap² Mreᵏ refl (fun-ext λ a → ▹-ext (ih▹ ⊛ next (DA.δ da s a) ⊛ next (δs da ss a))) ⟩
  apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (unfoldᵏ-body (unroll da) (next (langᵏ da)) s)) (unfoldᵏ-body (unroll $ powA da) (next (langᵏ (powA da))) ss)
    ＝˘⟨ zipWithᵏ-eq {f = _or_} {b = unfoldᵏ-body (unroll da) (next (langᵏ da)) s} ⟩
  (unfoldᵏ-body (unroll da) (next (langᵏ da)) s ⋃ᵏ unfoldᵏ-body (unroll $ powA da) (next (langᵏ (powA da))) ss)
    ＝˘⟨ ap (λ q → unfoldᵏ-body (unroll da) (next (langᵏ da)) s ⋃ᵏ q ss) (fix-path (unfoldᵏ-body (unroll $ powA da))) ⟩
  (unfoldᵏ-body (unroll da) (next (langᵏ da)) s ⋃ᵏ langᵏ (powA da) ss)
    ＝˘⟨ ap (λ q → q s ⋃ᵏ langᵏ (powA da) ss) (fix-path (unfoldᵏ-body (unroll da))) ⟩
  langᵏ da s ⋃ᵏ langᵏ (powA da) ss
    ∎

powA-cons : (da : DA A S) (s : S) (ss : List S)
          → lang (powA da) (s ∷ ss) ＝ lang da s ⋃ lang (powA da) ss
powA-cons da s ss = fun-ext λ κ → powA-consᵏ da s ss

-- composition automaton
composeA : DA A S₁ → S₂ → DA A S₂ → DA A (S₁ × List S₂)
composeA da1 s da2 =
  mkDA (λ s12 → DA.ν da1 (s12 .fst) and DA.ν da2 s or νs da2 (s12 .snd))
       (λ s12 a → (  DA.δ da1 (s12 .fst) a)
                   , δs da2 (if DA.ν da1 (s12 .fst) then s ∷ s12 .snd else s12 .snd) a)

composeA-genᵏ : (da1 : DA A S₁) (da2 : DA A S₂)
              → (s1 : S₁) → (s2 : S₂) (ss : List S₂)
              → langᵏ {κ = κ} (composeA da1 s2 da2) (s1 , ss)
                  ＝
                (langᵏ da1 s1 ·ᵏ langᵏ da2 s2) ⋃ᵏ langᵏ (powA da2) ss
composeA-genᵏ {A} {S₁} {S₂} {κ} da1 da2 = fix {k = κ} λ ih▹ s1 s2 ss →
  langᵏ (composeA da1 s2 da2) (s1 , ss)
    ＝⟨ ap (_$ (s1 , ss)) (fix-path (unfoldᵏ-body (unroll $ composeA da1 s2 da2))) ⟩
  Mreᵏ (DA.ν da1 s1 and DA.ν da2 s2 or νs da2 ss)
       (λ a → next (langᵏ (composeA da1 s2 da2) ((DA.δ da1 s1 a) , δs da2 (if DA.ν da1 s1 then s2 ∷ ss else ss) a)))
    ＝⟨ ap² Mreᵏ refl (fun-ext λ a → ▹-ext λ α → go {ih▹ = ih▹}) ⟩
  apᵏ-body (next apᵏ)
   (mapᵏ-body _or_ (next (mapᵏ _or_))
    (·ᵏ-body (next _·ᵏ_) (unfoldᵏ-body (unroll da1) (next (langᵏ da1)) s1) (unfoldᵏ-body (unroll da2) (next (langᵏ da2)) s2)))
    (unfoldᵏ-body (unroll $ powA da2) (next (langᵏ (powA da2))) ss)
    ＝⟨ sym (zipWithᵏ-eq {b = (·ᵏ-body (next _·ᵏ_) (unfoldᵏ-body (unroll da1) (next (langᵏ da1)) s1) (unfoldᵏ-body (unroll da2) (next (langᵏ da2)) s2))}) ⟩
  (·ᵏ-body (next _·ᵏ_) (unfoldᵏ-body (unroll da1) (next (langᵏ da1)) s1) (unfoldᵏ-body (unroll da2) (next (langᵏ da2)) s2) ⋃ᵏ unfoldᵏ-body (unroll $ powA da2) (next (langᵏ (powA da2))) ss)
    ＝⟨ ap (λ q → q (unfoldᵏ-body (unroll da1) (next (langᵏ da1)) s1) (unfoldᵏ-body (unroll da2) (next (langᵏ da2)) s2) ⋃ᵏ unfoldᵏ-body (unroll $ powA da2) (next (langᵏ (powA da2))) ss)
           (sym $ fix-path ·ᵏ-body) ⟩
  ((unfoldᵏ-body (unroll da1) (next (langᵏ da1)) s1 ·ᵏ unfoldᵏ-body (unroll da2) (next (langᵏ da2)) s2) ⋃ᵏ unfoldᵏ-body (unroll $ powA da2) (next (langᵏ (powA da2))) ss)
    ＝⟨ ap (λ q → (q s1 ·ᵏ unfoldᵏ-body (unroll da2) (next (langᵏ da2)) s2) ⋃ᵏ unfoldᵏ-body (unroll $ powA da2) (next (langᵏ (powA da2))) ss) (sym $ fix-path (unfoldᵏ-body (unroll da1))) ⟩
  ((langᵏ da1 s1 ·ᵏ unfoldᵏ-body (unroll da2) (next (langᵏ da2)) s2) ⋃ᵏ unfoldᵏ-body (unroll $ powA da2) (next (langᵏ (powA da2))) ss)
    ＝⟨ ap (λ q → (langᵏ da1 s1 ·ᵏ q s2) ⋃ᵏ unfoldᵏ-body (unroll $ powA da2) (next (langᵏ (powA da2))) ss) (sym $ fix-path (unfoldᵏ-body (unroll da2))) ⟩
  ((langᵏ da1 s1 ·ᵏ langᵏ da2 s2) ⋃ᵏ unfoldᵏ-body (unroll $ powA da2) (next (langᵏ (powA da2))) ss)
    ＝⟨ ap (λ q → (langᵏ da1 s1 ·ᵏ langᵏ da2 s2) ⋃ᵏ q ss) (sym $ fix-path (unfoldᵏ-body (unroll $ powA da2))) ⟩
  ((langᵏ da1 s1 ·ᵏ langᵏ da2 s2) ⋃ᵏ langᵏ (powA da2) ss)
    ∎
  where
  go : {ih▹ : ▹ κ ((s1 : S₁) (s2 : S₂) (ss : List S₂)
                   → langᵏ {κ = κ} (composeA da1 s2 da2) (s1 , ss) ＝ ((langᵏ da1 s1 ·ᵏ langᵏ da2 s2) ⋃ᵏ langᵏ (powA da2) ss)) }
       {s1 : S₁} {s2 : S₂} {ss : List S₂} {a : A} {@tick α : Tick κ}
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
           ＝⟨ ap (λ q → (langᵏ da1 (DA.δ da1 s1 a) ·ᵏ q s2) ⋃ᵏ (langᵏ da2 (DA.δ da2 s2 a) ⋃ᵏ langᵏ (powA da2) (δs da2 ss a))) (fix-path (unfoldᵏ-body (unroll da2))) ⟩
         (langᵏ da1 (DA.δ da1 s1 a) ·ᵏ Mreᵏ (DA.ν da2 s2) (λ a₁ → next (langᵏ da2 (DA.δ da2 s2 a₁)))) ⋃ᵏ (langᵏ da2 (DA.δ da2 s2 a) ⋃ᵏ langᵏ (powA da2) (δs da2 ss a))
           ＝⟨ sym (unionᵏ-assoc {k = langᵏ da1 (DA.δ da1 s1 a) ·ᵏ Mreᵏ (DA.ν da2 s2) (λ a₁ → next (langᵏ da2 (DA.δ da2 s2 a₁)))}) ⟩
         (((langᵏ da1 (DA.δ da1 s1 a) ·ᵏ Mreᵏ (DA.ν da2 s2) (λ a₁ → next (langᵏ da2 (DA.δ da2 s2 a₁)))) ⋃ᵏ langᵏ da2 (DA.δ da2 s2 a)) ⋃ᵏ langᵏ (powA da2) (δs da2 ss a))
            ∎
  ... | false =
         (langᵏ (composeA da1 s2 da2) (DA.δ da1 s1 a , δs da2 ss a))
           ＝⟨ ih▹ α (DA.δ da1 s1 a) s2 (δs da2 ss a) ⟩
         ((langᵏ da1 (DA.δ da1 s1 a) ·ᵏ langᵏ da2 s2) ⋃ᵏ langᵏ (powA da2) (δs da2 ss a))
           ＝⟨ ap (λ q → (langᵏ da1 (DA.δ da1 s1 a) ·ᵏ q s2) ⋃ᵏ langᵏ (powA da2) (δs da2 ss a)) (fix-path (unfoldᵏ-body (unroll da2))) ⟩
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
  ∙ union-empty-r {l = lang da1 s1 · lang da2 s2}

-- star automaton

acceptingInitial : S → DA A S → DA A (Maybe S)
acceptingInitial s0 da =
  mkDA (Maybe.rec true (DA.ν da))
       (Maybe.rec (just ∘ DA.δ da s0) (λ s → just ∘ DA.δ da s))

finalToInitial : DA A (Maybe S) → DA A (List (Maybe S))
finalToInitial da =
   mkDA (νs da)
        (λ ss a → let ss′ = δs da ss a in
                  if νs da ss then DA.δ da nothing a ∷ ss′
                              else ss′)

starA : S → DA A S → DA A (List (Maybe S))
starA s0 da = finalToInitial (acceptingInitial s0 da)

acceptingInitial-justᵏ : (s0 : S) (da : DA A S) (s : S)
                       → langᵏ {κ = κ} (acceptingInitial s0 da) (just s) ＝ langᵏ da s
acceptingInitial-justᵏ {κ} s0 da = fix {k = κ} λ ih▹ s →
  langᵏ (acceptingInitial s0 da) (just s)
    ＝⟨ ap (_$ just s) (fix-path (unfoldᵏ-body (unroll (acceptingInitial s0 da)))) ⟩
  Mreᵏ (DA.ν da s) (λ a → next (langᵏ (acceptingInitial s0 da) (just (DA.δ da s a))))
    ＝⟨ ap (Mreᵏ (DA.ν da s)) (fun-ext λ a → ▹-ext (ih▹ ⊛ next (DA.δ da s a))) ⟩
  Mreᵏ (DA.ν da s) (λ a → next (langᵏ da (DA.δ da s a)))
    ＝⟨ ap (_$ s) (sym $ fix-path (unfoldᵏ-body (unroll da))) ⟩
  langᵏ da s
    ∎

acceptingInitial-just : (s0 : S) (da : DA A S) (s : S)
                      → lang (acceptingInitial s0 da) (just s) ＝ lang da s
acceptingInitial-just s0 da s = fun-ext λ κ → acceptingInitial-justᵏ s0 da s

acceptingInitial-nothingᵏ : (s0 : S) (da : DA A S)
                          → langᵏ {κ = κ} (acceptingInitial s0 da) nothing ＝ εᵏ ⋃ᵏ langᵏ da s0
acceptingInitial-nothingᵏ {κ} s0 da = fix {k = κ} λ ih▹ →
  langᵏ (acceptingInitial s0 da) nothing
    ＝⟨ ap (_$ nothing) (fix-path (unfoldᵏ-body (unroll (acceptingInitial s0 da)))) ⟩
  Mreᵏ true (λ a → next (langᵏ (acceptingInitial s0 da) (just (DA.δ da s0 a))))
    ＝⟨ ap (Mreᵏ true) (fun-ext λ a → ▹-ext λ α → acceptingInitial-justᵏ s0 da (DA.δ da s0 a)
                                               ∙ sym union-empty-lᵏ) ⟩
  Mreᵏ true (λ a → next (∅ᵏ ⋃ᵏ langᵏ da (DA.δ da s0 a)))
    ＝⟨ sym (zipWithᵏ-eq {c = unfoldᵏ-body (unroll da) (next (langᵏ da)) s0}) ⟩
  (εᵏ ⋃ᵏ unfoldᵏ-body (unroll da) (next (langᵏ da)) s0)
    ＝⟨ ap (λ q → εᵏ ⋃ᵏ q s0) (sym $ fix-path (unfoldᵏ-body (unroll da))) ⟩
  εᵏ ⋃ᵏ langᵏ da s0
    ∎

acceptingInitial-nothing : (s0 : S) (da : DA A S)
                         → lang (acceptingInitial s0 da) nothing ＝ ε ⋃ lang da s0
acceptingInitial-nothing s0 da = fun-ext λ κ → acceptingInitial-nothingᵏ s0 da

starA-lemmaᵏ : (da : DA A S) (s0 : S) (ss : List (Maybe S))
             → langᵏ {κ = κ} (starA s0 da) ss ＝ langᵏ (powA (acceptingInitial s0 da)) ss ·ᵏ ((langᵏ da s0) ＊ᵏ)
starA-lemmaᵏ {A} {S} {κ} da s0 = fix {k = κ} λ ih▹ ss →
  langᵏ (starA s0 da) ss
    ＝⟨ ap (_$ ss) (fix-path (unfoldᵏ-body (unroll (starA s0 da)))) ⟩
  Mreᵏ (νs (acceptingInitial s0 da) ss) (λ a → next (langᵏ (starA s0 da) (DA.δ (starA s0 da) ss a)))
    ＝⟨ ap² Mreᵏ (sym (and-id-r (νs (acceptingInitial s0 da) ss)))
                (fun-ext λ a → ▹-ext λ α → go {ih▹ = ih▹} {ss = ss}) ⟩
  ·ᵏ-body (next _·ᵏ_) (unfoldᵏ-body (unroll (powA (acceptingInitial s0 da))) (next (langᵏ (powA (acceptingInitial s0 da)))) ss)
                      (＊ᵏ-body (next _＊ᵏ) (unfoldᵏ-body (unroll da) (next (langᵏ da)) s0))
    ＝⟨ ap (λ q → q (unfoldᵏ-body (unroll (powA (acceptingInitial s0 da))) (next (langᵏ (powA (acceptingInitial s0 da)))) ss)
                    (＊ᵏ-body (next _＊ᵏ) (unfoldᵏ-body (unroll da) (next (langᵏ da)) s0)))
           (sym $ fix-path ·ᵏ-body) ⟩
  (unfoldᵏ-body (unroll (powA (acceptingInitial s0 da))) (next (langᵏ (powA (acceptingInitial s0 da)))) ss
     ·ᵏ
   ＊ᵏ-body (next _＊ᵏ) (unfoldᵏ-body (unroll da) (next (langᵏ da)) s0))
    ＝⟨ ap (λ q → (q ss ·ᵏ ＊ᵏ-body (next _＊ᵏ) (unfoldᵏ-body (unroll da) (next (langᵏ da)) s0))) (sym $ fix-path (unfoldᵏ-body (unroll (powA (acceptingInitial s0 da))))) ⟩
  (langᵏ (powA (acceptingInitial s0 da)) ss ·ᵏ ＊ᵏ-body (next _＊ᵏ) (unfoldᵏ-body (unroll da) (next (langᵏ da)) s0))
    ＝⟨ ap (λ q → (langᵏ (powA (acceptingInitial s0 da)) ss ·ᵏ ＊ᵏ-body (next _＊ᵏ) (q s0))) (sym $ fix-path (unfoldᵏ-body (unroll da))) ⟩
  (langᵏ (powA (acceptingInitial s0 da)) ss ·ᵏ ＊ᵏ-body (next _＊ᵏ) (langᵏ da s0))
    ＝⟨ ap (λ q → langᵏ (powA (acceptingInitial s0 da)) ss ·ᵏ q (langᵏ da s0)) (sym $ fix-path ＊ᵏ-body) ⟩
  langᵏ (powA (acceptingInitial s0 da)) ss ·ᵏ ((langᵏ da s0) ＊ᵏ)
    ∎
  where
  go : {ih▹ : ▹ κ ((ss : List (Maybe S))
                  → langᵏ {κ = κ} (starA s0 da) ss ＝ (langᵏ (powA (acceptingInitial s0 da)) ss ·ᵏ (langᵏ da s0 ＊ᵏ)))}
       {ss : List (Maybe S)} {a : A} {@tick α : Tick κ}
       → (langᵏ (starA s0 da) (DA.δ (starA s0 da) ss a))
           ＝
         (condᵏ (νs (acceptingInitial s0 da) ss)
          (next ((langᵏ (powA (acceptingInitial s0 da)) (δs (acceptingInitial s0 da) ss a))
                   ·ᵏ
                 (＊ᵏ-body (next _＊ᵏ) (unfoldᵏ-body (unroll da) (next (langᵏ da)) s0))
                 ))
          (next ((langᵏ da (DA.δ da s0 a)) ·ᵏ ((unfoldᵏ-body (unroll da) (next (langᵏ da)) s0) ＊ᵏ)))
          α)
  go {ih▹} {ss} {a} {α} with (νs (acceptingInitial s0 da) ss)
  ... | true  =
          langᵏ (starA s0 da) (just (DA.δ da s0 a) ∷ δs (acceptingInitial s0 da) ss a)
            ＝⟨ ih▹ α (just (DA.δ da s0 a) ∷ δs (acceptingInitial s0 da) ss a) ⟩
          ((⌜ langᵏ (powA (acceptingInitial s0 da)) (just (DA.δ da s0 a) ∷ δs (acceptingInitial s0 da) ss a) ⌝ ·ᵏ (langᵏ da s0 ＊ᵏ)))
            ＝⟨ ap! (powA-consᵏ (acceptingInitial s0 da) (just (DA.δ da s0 a)) (δs (acceptingInitial s0 da) ss a)) ⟩
          ((⌜ langᵏ (acceptingInitial s0 da) (just (DA.δ da s0 a)) ⌝ ⋃ᵏ langᵏ (powA (acceptingInitial s0 da)) (δs (acceptingInitial s0 da) ss a)) ·ᵏ (langᵏ da s0 ＊ᵏ))
            ＝⟨ ap! (acceptingInitial-justᵏ s0 da (DA.δ da s0 a)) ⟩
          (⌜ langᵏ da (DA.δ da s0 a) ⋃ᵏ langᵏ (powA (acceptingInitial s0 da)) (δs (acceptingInitial s0 da) ss a) ⌝ ·ᵏ (langᵏ da s0 ＊ᵏ))
            ＝⟨ ap! (unionᵏ-comm {k = langᵏ da (DA.δ da s0 a)}) ⟩
          ((langᵏ (powA (acceptingInitial s0 da)) (δs (acceptingInitial s0 da) ss a) ⋃ᵏ langᵏ da (DA.δ da s0 a)) ·ᵏ (langᵏ da s0 ＊ᵏ))
            ＝⟨ ap (λ q → ((langᵏ (powA (acceptingInitial s0 da)) (δs (acceptingInitial s0 da) ss a) ⋃ᵏ langᵏ da (DA.δ da s0 a)) ·ᵏ (q s0 ＊ᵏ))) (fix-path (unfoldᵏ-body (unroll da))) ⟩
          ((langᵏ (powA (acceptingInitial s0 da)) (δs (acceptingInitial s0 da) ss a) ⋃ᵏ langᵏ da (DA.δ da s0 a)) ·ᵏ ((unfoldᵏ-body (unroll da) (next (langᵏ da)) s0) ＊ᵏ))
            ＝⟨ concat-union-distrib-lᵏ (langᵏ (powA (acceptingInitial s0 da)) (δs (acceptingInitial s0 da) ss a)) (langᵏ da (DA.δ da s0 a)) ((unfoldᵏ-body (unroll da) (next (langᵏ da)) s0) ＊ᵏ) ⟩
          ((langᵏ (powA (acceptingInitial s0 da)) (δs (acceptingInitial s0 da) ss a)
                   ·ᵏ
           (unfoldᵏ-body (unroll da) (next (langᵏ da)) s0 ＊ᵏ))
             ⋃ᵏ
           (langᵏ da (DA.δ da s0 a) ·ᵏ (unfoldᵏ-body (unroll da) (next (langᵏ da)) s0 ＊ᵏ)))
            ＝⟨ ap (λ q → ((langᵏ (powA (acceptingInitial s0 da)) (δs (acceptingInitial s0 da) ss a)
                            ·ᵏ (q (unfoldᵏ-body (unroll da) (next (langᵏ da)) s0)))
                           ⋃ᵏ
                          (langᵏ da (DA.δ da s0 a) ·ᵏ (unfoldᵏ-body (unroll da) (next (langᵏ da)) s0 ＊ᵏ)))) (fix-path ＊ᵏ-body) ⟩
          ((langᵏ (powA (acceptingInitial s0 da)) (δs (acceptingInitial s0 da) ss a))
                   ·ᵏ
           (＊ᵏ-body (next _＊ᵏ) (unfoldᵏ-body (unroll da) (next (langᵏ da)) s0)))
             ⋃ᵏ
          (langᵏ da (DA.δ da s0 a) ·ᵏ ((unfoldᵏ-body (unroll da) (next (langᵏ da)) s0) ＊ᵏ))
            ∎
  ... | false =
          langᵏ (starA s0 da) (δs (acceptingInitial s0 da) ss a)
            ＝⟨ ih▹ α (δs (acceptingInitial s0 da) ss a) ⟩
          (langᵏ (powA (acceptingInitial s0 da)) (δs (acceptingInitial s0 da) ss a) ·ᵏ (langᵏ da s0 ＊ᵏ))
            ＝⟨ ap (langᵏ (powA (acceptingInitial s0 da)) (δs (acceptingInitial s0 da) ss a) ·ᵏ_)
                 (  ap (λ q → q s0 ＊ᵏ) (fix-path (unfoldᵏ-body (unroll da)))
                  ∙ ap (λ q → q (unfoldᵏ-body (unroll da) (next (langᵏ da)) s0)) (fix-path ＊ᵏ-body)) ⟩
          (langᵏ (powA (acceptingInitial s0 da)) (δs (acceptingInitial s0 da) ss a) ·ᵏ
           (＊ᵏ-body (next _＊ᵏ) (unfoldᵏ-body (unroll da) (next (langᵏ da)) s0)))
            ∎

starA-lemma : (da : DA A S) (s0 : S) (ss : List (Maybe S))
            → lang (starA s0 da) ss ＝ lang (powA (acceptingInitial s0 da)) ss · (lang da s0 ＊)
starA-lemma da s0 ss = fun-ext λ κ → starA-lemmaᵏ da s0 ss

starA-correctᵏ : (da : DA A S) (s0 : S)
               → langᵏ {κ = κ} (starA s0 da) (nothing ∷ []) ＝ (langᵏ da s0 ＊ᵏ)
starA-correctᵏ da s0 =
  langᵏ (starA s0 da) (nothing ∷ [])
    ＝⟨ starA-lemmaᵏ da s0 (nothing ∷ []) ⟩
  (⌜ langᵏ (powA (acceptingInitial s0 da)) (nothing ∷ []) ⌝ ·ᵏ (langᵏ da s0 ＊ᵏ))
    ＝⟨ ap! (powA-consᵏ (acceptingInitial s0 da) nothing []) ⟩
  (⌜ langᵏ (acceptingInitial s0 da) nothing ⌝ ⋃ᵏ langᵏ (powA (acceptingInitial s0 da)) []) ·ᵏ (langᵏ da s0 ＊ᵏ)
    ＝⟨ ap! (acceptingInitial-nothingᵏ s0 da) ⟩
  ((εᵏ ⋃ᵏ langᵏ da s0) ⋃ᵏ ⌜ langᵏ (powA (acceptingInitial s0 da)) [] ⌝) ·ᵏ (langᵏ da s0 ＊ᵏ)
    ＝⟨ ap! (powA-nilᵏ (acceptingInitial s0 da)) ⟩
  ⌜ (εᵏ ⋃ᵏ langᵏ da s0) ⋃ᵏ ∅ᵏ ⌝ ·ᵏ (langᵏ da s0 ＊ᵏ)
    ＝⟨ ap! union-empty-rᵏ ⟩
  (εᵏ ⋃ᵏ langᵏ da s0) ·ᵏ (langᵏ da s0 ＊ᵏ)
    ＝⟨ concat-union-distrib-lᵏ εᵏ (langᵏ da s0) (langᵏ da s0 ＊ᵏ) ⟩
  (⌜ εᵏ ·ᵏ (langᵏ da s0 ＊ᵏ) ⌝ ⋃ᵏ (langᵏ da s0 ·ᵏ (langᵏ da s0 ＊ᵏ)))
    ＝⟨ ap! (concat-unit-lᵏ (langᵏ da s0 ＊ᵏ)) ⟩
  (langᵏ da s0 ＊ᵏ) ⋃ᵏ (langᵏ da s0 ·ᵏ (langᵏ da s0 ＊ᵏ))
    ＝⟨ {!!} ⟩
  (langᵏ da s0 ＊ᵏ)
    ∎
