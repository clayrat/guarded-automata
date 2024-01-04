{-# OPTIONS --guarded #-}
module Lang where

open import Prelude
open import Data.Bool
open import Data.Dec
open import Data.List

open import Later
open import Clocked.Moore

private variable
  ℓ : Level
  A : 𝒰 ℓ
  κ : Cl

gLang : Cl → 𝒰 ℓ → 𝒰 ℓ
gLang k A = gMoore k A Bool

Lang : 𝒰 ℓ → 𝒰 ℓ
Lang A = Moore A Bool

-- TODO Clocked.Moore.Run
_∋_ : Lang A → List A → Bool
l ∋ []       = νᵐ l
l ∋ (a ∷ as) = δᵐ l a ∋ as

trie : (List A → Bool) → Lang A
trie = unfoldListᵐ

⊘ : Lang A
⊘ = pureᵐ false

ε : Lang A
ε = Mre true λ _ → ⊘

-- TODO how to use instances?
char : ∀ {dA : is-discrete A}
     → A → Lang A
char {dA} a = Mre false λ x → if ⌊ is-discrete-β dA x a ⌋ then ε else ⊘

compl : Lang A → Lang A
compl = mapᵐ not

_⋃ᵏ_ : gLang κ A → gLang κ A → gLang κ A
_⋃ᵏ_ = zipWithᵏ _or_

_⋃_ : Lang A → Lang A → Lang A
_⋃_ = zipWithᵐ _or_

_⋂_ : Lang A → Lang A → Lang A
_⋂_ = zipWithᵐ _and_

-- TODO figure out combinators
·ᵏ-body : ▹ κ (gLang κ A → gLang κ A → gLang κ A)
            → gLang κ A → gLang κ A → gLang κ A
·ᵏ-body c▹ (Mreᵏ kᵇ kᵏ) l@(Mreᵏ lᵇ lᵏ) =
  Mreᵏ (kᵇ and lᵇ) λ a → let kl′ = c▹ ⊛ kᵏ a ⊛ next l in
                         if kᵇ then ▹map _⋃ᵏ_ kl′ ⊛ lᵏ a else kl′

_·ᵏ_ : gMoore κ A Bool → gLang κ A → gLang κ A
_·ᵏ_ = fix ·ᵏ-body

_·_ : Lang A → Lang A → Lang A
_·_ a b k = (a k) ·ᵏ (b k)

starᵏ-body : ▹ κ (gLang κ A → gLang κ A)
            → gLang κ A → gLang κ A
starᵏ-body s▹ l@(Mreᵏ _ k) = Mreᵏ true λ a → ▹map (_·ᵏ_) (k a) ⊛ (s▹ ⊛ next l)

starᵏ : gLang κ A → gLang κ A
starᵏ = fix starᵏ-body

_＊ : Lang A → Lang A
_＊ l κ = starᵏ (l κ)

-- laws

unionᵏ-assoc : {k l m : gLang κ A}
             → (k ⋃ᵏ l) ⋃ᵏ m ＝ k ⋃ᵏ (l ⋃ᵏ m)
unionᵏ-assoc = zipWithᵏ-assoc or-assoc

union-assoc : {k l m : Lang A}
            → (k ⋃ l) ⋃ m ＝ k ⋃ (l ⋃ m)
union-assoc = zipWithᵐ-assoc or-assoc

inter-assoc : {k l m : Lang A}
            → (k ⋂ l) ⋂ m ＝ k ⋂ (l ⋂ m)
inter-assoc = zipWithᵐ-assoc and-assoc

unionᵏ-comm : {k l : gLang κ A}
            → k ⋃ᵏ l ＝ l ⋃ᵏ k
unionᵏ-comm {k} {l} = zipWithᵏ-comm or-comm k l

union-comm : {k l : Lang A}
           → k ⋃ l ＝ l ⋃ k
union-comm {k} {l} = zipWithᵐ-comm or-comm k l

inter-comm : {k l : Lang A}
           → k ⋂ l ＝ l ⋂ k
inter-comm {k} {l} = zipWithᵐ-comm and-comm k l

unionᵏ-idem : {l : gLang κ A}
            → l ⋃ᵏ l ＝ l
unionᵏ-idem {l} = zipWithᵏ-idem or-idem l

union-idem : {l : Lang A}
           → l ⋃ l ＝ l
union-idem {l} = zipWithᵐ-idem or-idem l

inter-idem : {l : Lang A}
           → l ⋂ l ＝ l
inter-idem {l} = zipWithᵐ-idem and-idem l

union-empty-l : {l : Lang A}
              → ⊘ ⋃ l ＝ l
union-empty-l {l} = zipWithᵐ-id-l λ _ → refl

-- TODO we don't have an ICM solver in c-m yet

union-unionᵏ-distr : {k l m : gLang κ A}
                  → (k ⋃ᵏ l) ⋃ᵏ m ＝ (k ⋃ᵏ m) ⋃ᵏ (l ⋃ᵏ m)
union-unionᵏ-distr {k} {l} {m} =
  (k ⋃ᵏ l) ⋃ᵏ m
    ＝⟨ unionᵏ-assoc ⟩
  (k ⋃ᵏ (l ⋃ᵏ m))
    ＝⟨ ap (λ q → k ⋃ᵏ (l ⋃ᵏ q)) (sym unionᵏ-idem) ⟩
  (k ⋃ᵏ (l ⋃ᵏ (m ⋃ᵏ m)))
    ＝⟨ ap (λ q → k ⋃ᵏ q) (sym unionᵏ-assoc) ⟩
  (k ⋃ᵏ ((l ⋃ᵏ m) ⋃ᵏ m))
    ＝⟨ ap (λ q → k ⋃ᵏ q) unionᵏ-comm ⟩
  (k ⋃ᵏ (m ⋃ᵏ (l ⋃ᵏ m)))
    ＝⟨ sym unionᵏ-assoc ⟩
  (k ⋃ᵏ m) ⋃ᵏ (l ⋃ᵏ m)
    ∎

union-union-distr : {k l m : Lang A}
                  → (k ⋃ l) ⋃ m ＝ (k ⋃ m) ⋃ (l ⋃ m)
union-union-distr {k} {l} {m} =
  (k ⋃ l) ⋃ m
    ＝⟨ union-assoc ⟩
  (k ⋃ (l ⋃ m))
    ＝⟨ ap (λ q → k ⋃ (l ⋃ q)) (sym union-idem) ⟩
  (k ⋃ (l ⋃ (m ⋃ m)))
    ＝⟨ ap (λ q → k ⋃ q) (sym union-assoc) ⟩
  (k ⋃ ((l ⋃ m) ⋃ m))
    ＝⟨ ap (λ q → k ⋃ q) union-comm ⟩
  (k ⋃ (m ⋃ (l ⋃ m)))
    ＝⟨ sym union-assoc ⟩
  (k ⋃ m) ⋃ (l ⋃ m)
    ∎

concat-union-distrib-lᵏ : (k l m : gLang κ A)
                        → (k ⋃ᵏ l) ·ᵏ m ＝ (k ·ᵏ m) ⋃ᵏ (l ·ᵏ m)
concat-union-distrib-lᵏ {κ} = fix {k = κ} λ ih▹ → λ where
  k@(Mreᵏ kᵇ kᵏ) l@(Mreᵏ lᵇ lᵏ) m@(Mreᵏ mᵇ mᵏ) →
    ((k ⋃ᵏ l) ·ᵏ m)
      ＝⟨ ap (λ q → q ·ᵏ m) (zipWithᵏ-eq {f = _or_} {b = k} {c = l})  ⟩
    (apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) k) l ·ᵏ m)
      ＝⟨ ap (λ q → q (apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) k) l) m) (fix-path ·ᵏ-body) ⟩
    ·ᵏ-body (next _·ᵏ_) (apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) k) l) m
      ＝⟨ ap² Mreᵏ (and-distrib-or-r kᵇ lᵇ mᵇ) (fun-ext λ a → ▹-ext (go {ih▹ = ih▹} {kᵇ} {kᵏ} {lᵇ} {lᵏ} {mᵇ} {mᵏ})) ⟩
    apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (·ᵏ-body (next _·ᵏ_) k m)) (·ᵏ-body (next _·ᵏ_) l m)
      ＝⟨ ap (λ q → apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (·ᵏ-body (next _·ᵏ_) k m)) (q l m)) (sym $ fix-path ·ᵏ-body) ⟩
    apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (·ᵏ-body (next _·ᵏ_) k m)) (l ·ᵏ m)
      ＝⟨ ap (λ q → apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (q k m)) (l ·ᵏ m)) (sym $ fix-path ·ᵏ-body)  ⟩
    apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (k ·ᵏ m)) (l ·ᵏ m)
      ＝⟨ sym (zipWithᵏ-eq {f = _or_} {b = k ·ᵏ m} {c = l ·ᵏ m}) ⟩
    ((k ·ᵏ m) ⋃ᵏ (l ·ᵏ m))
      ∎
   where
   go : {ih▹ : ▹ κ ((k l m : gLang κ A) → ((k ⋃ᵏ l) ·ᵏ m) ＝ ((k ·ᵏ m) ⋃ᵏ (l ·ᵏ m)))}
        {kᵇ : Bool} {kᵏ : A → ▹ κ (gLang κ A)}
        {lᵇ : Bool} {lᵏ : A → ▹ κ (gLang κ A)}
        {mᵇ : Bool} {mᵏ : A → ▹ κ (gLang κ A)}
        {a : A}
      → ▹[ α ∶ κ ] ((if kᵇ or lᵇ then ▹map _⋃ᵏ_ (next _·ᵏ_ ⊛ (next apᵏ ⊛ (next (mapᵏ _or_) ⊛ kᵏ a) ⊛ lᵏ a) ⊛ next (Mreᵏ mᵇ mᵏ)) ⊛ mᵏ a
                                else next _·ᵏ_ ⊛ (next apᵏ ⊛ (next (mapᵏ _or_) ⊛ kᵏ a) ⊛ lᵏ a) ⊛ next (Mreᵏ mᵇ mᵏ)) α)
                   ＝
                  ((next apᵏ ⊛ (next (mapᵏ _or_) ⊛ (if kᵇ then ▹map _⋃ᵏ_ (next _·ᵏ_ ⊛ kᵏ a ⊛ next (Mreᵏ mᵇ mᵏ)) ⊛ mᵏ a
                                                           else next _·ᵏ_ ⊛ kᵏ a ⊛ next (Mreᵏ mᵇ mᵏ)))
                             ⊛ (if lᵇ then ▹map _⋃ᵏ_ (next _·ᵏ_ ⊛ lᵏ a ⊛ next (Mreᵏ mᵇ mᵏ)) ⊛ mᵏ a
                                       else next _·ᵏ_ ⊛ lᵏ a ⊛ next (Mreᵏ mᵇ mᵏ))) α)
   go {ih▹} {kᵇ = false} {kᵏ} {lᵇ = false} {lᵏ} {mᵇ} {mᵏ} {a} = ih▹ ⊛ kᵏ a ⊛′ lᵏ a ⊛′ next (Mreᵏ mᵇ mᵏ)
   go {ih▹} {kᵇ = false} {kᵏ} {lᵇ = true}  {lᵏ} {mᵇ} {mᵏ} {a} = λ α → ap (λ q → q ⋃ᵏ (mᵏ a α)) ((ih▹ ⊛ kᵏ a ⊛′ lᵏ a ⊛′ next (Mreᵏ mᵇ mᵏ)) α) ∙ unionᵏ-assoc
   go {ih▹} {kᵇ = true}  {kᵏ} {lᵇ = false} {lᵏ} {mᵇ} {mᵏ} {a} = λ α → ap (λ q → q ⋃ᵏ (mᵏ a α)) ((ih▹ ⊛ kᵏ a ⊛′ lᵏ a ⊛′ next (Mreᵏ mᵇ mᵏ)) α) ∙ unionᵏ-assoc ∙ ap (λ q → ((kᵏ a α) ·ᵏ (Mreᵏ mᵇ mᵏ)) ⋃ᵏ q) unionᵏ-comm ∙ sym unionᵏ-assoc
   go {ih▹} {kᵇ = true}  {kᵏ} {lᵇ = true}  {lᵏ} {mᵇ} {mᵏ} {a} = λ α → ap (λ q → q ⋃ᵏ (mᵏ a α)) ((ih▹ ⊛ kᵏ a ⊛′ lᵏ a ⊛′ next (Mreᵏ mᵇ mᵏ)) α) ∙ union-unionᵏ-distr

concat-union-distrib-l : (k l m : Lang A)
                       → (k ⋃ l) · m ＝ (k · m) ⋃ (l · m)
concat-union-distrib-l k l m = fun-ext λ κ → concat-union-distrib-lᵏ (k κ) (l κ) (m κ)
