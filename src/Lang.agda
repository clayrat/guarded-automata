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

∅ᵏ : gLang κ A
∅ᵏ = pureᵏ false

∅ : Lang A
∅ = pureᵐ false

εᵏ : gLang κ A
εᵏ = Mreᵏ true λ _ → next ∅ᵏ

ε : Lang A
ε = Mre true λ _ → ∅

-- TODO how to use instances?
char : ∀ {dA : is-discrete A}
     → A → Lang A
char {dA} a = Mre false λ x → if ⌊ is-discrete-β dA x a ⌋ then ε else ∅

compl : Lang A → Lang A
compl = mapᵐ not

_⋃ᵏ_ : gLang κ A → gLang κ A → gLang κ A
_⋃ᵏ_ = zipWithᵏ _or_

_⋃_ : Lang A → Lang A → Lang A
_⋃_ = zipWithᵐ _or_

_⋂_ : Lang A → Lang A → Lang A
_⋂_ = zipWithᵐ _and_

-- TODO figure out better combinators?
condᵏ : Bool → ▹ κ (gLang κ A) → ▹ κ (gLang κ A) → ▹ κ (gLang κ A)
condᵏ b k l = if b then ▹map _⋃ᵏ_ k ⊛ l else k

·ᵏ-body : ▹ κ (gLang κ A → gLang κ A → gLang κ A)
            → gLang κ A → gLang κ A → gLang κ A
·ᵏ-body c▹ (Mreᵏ kᵇ kᵏ) l@(Mreᵏ lᵇ lᵏ) =
  Mreᵏ (kᵇ and lᵇ) λ a → condᵏ kᵇ (c▹ ⊛ kᵏ a ⊛ next l) (lᵏ a)

_·ᵏ_ : gMoore κ A Bool → gLang κ A → gLang κ A
_·ᵏ_ = fix ·ᵏ-body

_·_ : Lang A → Lang A → Lang A
_·_ a b k = (a k) ·ᵏ (b k)

＊ᵏ-body : ▹ κ (gLang κ A → gLang κ A)
            → gLang κ A → gLang κ A
＊ᵏ-body s▹ l@(Mreᵏ _ k) = Mreᵏ true λ a → ▹map (_·ᵏ_) (k a) ⊛ (s▹ ⊛ next l)

_＊ᵏ : gLang κ A → gLang κ A
_＊ᵏ = fix ＊ᵏ-body

_＊ : Lang A → Lang A
_＊ l κ = (l κ) ＊ᵏ

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

union-empty-lᵏ : {l : gLang κ A}
               → ∅ᵏ ⋃ᵏ l ＝ l
union-empty-lᵏ {l} = zipWithᵏ-id-l λ _ → refl

union-empty-l : {l : Lang A}
              → ∅ ⋃ l ＝ l
union-empty-l {l} = zipWithᵐ-id-l λ _ → refl

-- derived laws
-- TODO we don't have an ICM solver in c-m yet

union-empty-rᵏ : {l : gLang κ A}
               → l ⋃ᵏ ∅ᵏ ＝ l
union-empty-rᵏ {l} = unionᵏ-comm ∙ union-empty-lᵏ

union-assoc-commᵏ : {k l m : gLang κ A}
                  → (k ⋃ᵏ l) ⋃ᵏ m ＝ (k ⋃ᵏ m) ⋃ᵏ l
union-assoc-commᵏ {k} = unionᵏ-assoc ∙ ap (λ q → k ⋃ᵏ q) unionᵏ-comm ∙ sym unionᵏ-assoc

union-unionᵏ-distr : {k l m : gLang κ A}
                  → (k ⋃ᵏ l) ⋃ᵏ m ＝ (k ⋃ᵏ m) ⋃ᵏ (l ⋃ᵏ m)
union-unionᵏ-distr {k} {l} {m} =
  (k ⋃ᵏ l) ⋃ᵏ m
    ＝⟨ unionᵏ-assoc ⟩
  (k ⋃ᵏ (l ⋃ᵏ ⌜ m ⌝))
    ＝˘⟨ ap¡ unionᵏ-idem ⟩
  (k ⋃ᵏ ⌜ l ⋃ᵏ (m ⋃ᵏ m) ⌝)
    ＝˘⟨ ap¡ unionᵏ-assoc ⟩
  (k ⋃ᵏ ⌜ (l ⋃ᵏ m) ⋃ᵏ m ⌝)
    ＝⟨ ap! unionᵏ-comm ⟩
  (k ⋃ᵏ (m ⋃ᵏ (l ⋃ᵏ m)))
    ＝˘⟨ unionᵏ-assoc ⟩
  (k ⋃ᵏ m) ⋃ᵏ (l ⋃ᵏ m)
    ∎

unionᵏ-swap-inner : {k l m n : gLang κ A}
                  → (k ⋃ᵏ l) ⋃ᵏ (m ⋃ᵏ n) ＝ (k ⋃ᵏ m) ⋃ᵏ (l ⋃ᵏ n)
unionᵏ-swap-inner {k} {l} {m} {n} =
  (k ⋃ᵏ l) ⋃ᵏ (m ⋃ᵏ n)
    ＝⟨ unionᵏ-assoc ⟩
  (k ⋃ᵏ ⌜ l ⋃ᵏ (m ⋃ᵏ n) ⌝)
    ＝˘⟨ ap¡ unionᵏ-assoc ⟩
  (k ⋃ᵏ (⌜ l ⋃ᵏ m ⌝ ⋃ᵏ n))
    ＝⟨ ap! unionᵏ-comm ⟩
  (k ⋃ᵏ ⌜ (m ⋃ᵏ l) ⋃ᵏ n ⌝)
    ＝⟨ ap! unionᵏ-assoc ⟩
  (k ⋃ᵏ (m ⋃ᵏ (l ⋃ᵏ n)))
    ＝˘⟨ unionᵏ-assoc ⟩
  (k ⋃ᵏ m) ⋃ᵏ (l ⋃ᵏ n)
    ∎

-- concatenation laws

concat-union-distrib-lᵏ : (k l m : gLang κ A)
                        → (k ⋃ᵏ l) ·ᵏ m ＝ (k ·ᵏ m) ⋃ᵏ (l ·ᵏ m)
concat-union-distrib-lᵏ {κ} = fix {k = κ} λ ih▹ → λ where
  k@(Mreᵏ kᵇ kᵏ) l@(Mreᵏ lᵇ lᵏ) m@(Mreᵏ mᵇ mᵏ) →
    (⌜ k ⋃ᵏ l ⌝ ·ᵏ m)
      ＝⟨ ap! (zipWithᵏ-eq {f = _or_} {b = k} {c = l}) ⟩
    (apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) k) l ·ᵏ m)
      ＝⟨ ap (λ q → q (apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) k) l) m) (fix-path ·ᵏ-body) ⟩
    ·ᵏ-body (next _·ᵏ_) (apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) k) l) m
      ＝⟨ ap² Mreᵏ (and-distrib-or-r kᵇ lᵇ mᵇ) (fun-ext λ a → ▹-ext (go {ih▹ = ih▹} {kᵇ} {kᵏ} {lᵇ} {lᵏ} {mᵇ} {mᵏ})) ⟩
    apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (·ᵏ-body (next _·ᵏ_) k m)) (·ᵏ-body (next _·ᵏ_) l m)
      ＝⟨ ap (λ q → apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (·ᵏ-body (next _·ᵏ_) k m)) (q l m)) (sym $ fix-path ·ᵏ-body) ⟩
    apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (·ᵏ-body (next _·ᵏ_) k m)) (l ·ᵏ m)
      ＝⟨ ap (λ q → apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (q k m)) (l ·ᵏ m)) (sym $ fix-path ·ᵏ-body)  ⟩
    apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (k ·ᵏ m)) (l ·ᵏ m)
      ＝˘⟨ zipWithᵏ-eq {f = _or_} {b = k ·ᵏ m} {c = l ·ᵏ m} ⟩
    ((k ·ᵏ m) ⋃ᵏ (l ·ᵏ m))
      ∎
   where
   go : {ih▹ : ▹ κ ((k l m : gLang κ A) → ((k ⋃ᵏ l) ·ᵏ m) ＝ ((k ·ᵏ m) ⋃ᵏ (l ·ᵏ m)))}
        {kᵇ : Bool} {kᵏ : A → ▹ κ (gLang κ A)}
        {lᵇ : Bool} {lᵏ : A → ▹ κ (gLang κ A)}
        {mᵇ : Bool} {mᵏ : A → ▹ κ (gLang κ A)}
        {a : A}
      → ▹[ α ∶ κ ] (condᵏ (kᵇ or lᵇ) (▹map _·ᵏ_ (▹map _⋃ᵏ_ (kᵏ a) ⊛ lᵏ a) ⊛ next (Mreᵏ mᵇ mᵏ)) (mᵏ a) α)
                    ＝
                  ((▹map _⋃ᵏ_ (condᵏ kᵇ (▹map _·ᵏ_ (kᵏ a) ⊛ next (Mreᵏ mᵇ mᵏ)) (mᵏ a))
                             ⊛ condᵏ lᵇ (▹map _·ᵏ_ (lᵏ a) ⊛ next (Mreᵏ mᵇ mᵏ)) (mᵏ a)) α)
   go {ih▹} {kᵇ = false} {kᵏ} {lᵇ = false} {lᵏ} {mᵇ} {mᵏ} {a} =
     ih▹ ⊛ kᵏ a ⊛′ lᵏ a ⊛′ next (Mreᵏ mᵇ mᵏ)
   go {ih▹} {kᵇ = false} {kᵏ} {lᵇ = true}  {lᵏ} {mᵇ} {mᵏ} {a} =
     λ α → ap (λ q → q ⋃ᵏ (mᵏ a α)) ((ih▹ ⊛ kᵏ a ⊛′ lᵏ a ⊛′ next (Mreᵏ mᵇ mᵏ)) α)
         ∙ unionᵏ-assoc
   go {ih▹} {kᵇ = true}  {kᵏ} {lᵇ = false} {lᵏ} {mᵇ} {mᵏ} {a} =
     λ α → ap (λ q → q ⋃ᵏ (mᵏ a α)) ((ih▹ ⊛ kᵏ a ⊛′ lᵏ a ⊛′ next (Mreᵏ mᵇ mᵏ)) α)
         ∙ union-assoc-commᵏ
   go {ih▹} {kᵇ = true}  {kᵏ} {lᵇ = true}  {lᵏ} {mᵇ} {mᵏ} {a} =
     λ α → ap (λ q → q ⋃ᵏ (mᵏ a α)) ((ih▹ ⊛ kᵏ a ⊛′ lᵏ a ⊛′ next (Mreᵏ mᵇ mᵏ)) α)
         ∙ union-unionᵏ-distr

concat-union-distrib-l : (k l m : Lang A)
                       → (k ⋃ l) · m ＝ (k · m) ⋃ (l · m)
concat-union-distrib-l k l m = fun-ext λ κ → concat-union-distrib-lᵏ (k κ) (l κ) (m κ)

concat-union-distrib-rᵏ : (k l m : gLang κ A)
                        → k ·ᵏ (l ⋃ᵏ m) ＝ (k ·ᵏ l) ⋃ᵏ (k ·ᵏ m)
concat-union-distrib-rᵏ {κ} = fix {k = κ} λ ih▹ → λ where
  k@(Mreᵏ kᵇ kᵏ) l@(Mreᵏ lᵇ lᵏ) m@(Mreᵏ mᵇ mᵏ) →
    (k ·ᵏ ⌜ l ⋃ᵏ m ⌝)
      ＝⟨ ap! (zipWithᵏ-eq {f = _or_} {b = l} {c = m}) ⟩
    (k ·ᵏ apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) l) m)
      ＝⟨ ap (λ q → q k (apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) l) m)) (fix-path ·ᵏ-body) ⟩
    ·ᵏ-body (next _·ᵏ_) k (apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) l) m)
      ＝⟨ ap² Mreᵏ (and-distrib-or-l kᵇ lᵇ mᵇ) (fun-ext λ a → ▹-ext (go {ih▹ = ih▹} {kᵇ} {kᵏ} {lᵇ} {lᵏ} {mᵇ} {mᵏ})) ⟩
    apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (·ᵏ-body (next _·ᵏ_) k l)) (·ᵏ-body (next _·ᵏ_) k m)
      ＝˘⟨ ap (λ q → apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (·ᵏ-body (next _·ᵏ_) k l)) (q k m)) (fix-path ·ᵏ-body) ⟩
    apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (·ᵏ-body (next _·ᵏ_) k l)) (k ·ᵏ m)
      ＝˘⟨ ap (λ q → apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (q k l)) (k ·ᵏ m)) (fix-path ·ᵏ-body) ⟩
    apᵏ-body (next apᵏ) (mapᵏ-body _or_ (next (mapᵏ _or_)) (k ·ᵏ l)) (k ·ᵏ m)
      ＝˘⟨ zipWithᵏ-eq {f = _or_} {b = k ·ᵏ l} {c = k ·ᵏ m} ⟩
    ((k ·ᵏ l) ⋃ᵏ (k ·ᵏ m))
      ∎
   where
   go : {ih▹ : ▹ κ ((k l m : gLang κ A) → (k ·ᵏ (l ⋃ᵏ m)) ＝ ((k ·ᵏ l) ⋃ᵏ (k ·ᵏ m)))}
        {kᵇ : Bool} {kᵏ : A → ▹ κ (gMoore κ A Bool)}
        {lᵇ : Bool} {lᵏ : A → ▹ κ (gMoore κ A Bool)}
        {mᵇ : Bool} {mᵏ : A → ▹ κ (gMoore κ A Bool)}
        {a : A}
      → ▹[ α ∶ κ ] (condᵏ kᵇ (▹map _·ᵏ_ (kᵏ a) ⊛ next (Mreᵏ (lᵇ or mᵇ) (λ a₁ → ▹map _⋃ᵏ_ (lᵏ a₁) ⊛ mᵏ a₁)))
                            (▹map _⋃ᵏ_ (lᵏ a) ⊛ mᵏ a) α)
                    ＝
                  ((▹map _⋃ᵏ_ (condᵏ kᵇ (▹map _·ᵏ_ (kᵏ a) ⊛ next (Mreᵏ lᵇ lᵏ)) (lᵏ a))
                             ⊛ condᵏ kᵇ (▹map _·ᵏ_ (kᵏ a) ⊛ next (Mreᵏ mᵇ mᵏ)) (mᵏ a)) α)
   go {ih▹} {kᵇ = false} {kᵏ} {lᵇ} {lᵏ} {mᵇ} {mᵏ} {a} =
     λ α → ap (λ q → kᵏ a α ·ᵏ Mreᵏ (lᵇ or mᵇ) q)
              (fun-ext λ a₁ → ▹-ext λ α₁ → (λ i → pfix apᵏ-body (~ i) α₁ (mapᵏ _or_ (lᵏ a₁ α₁)) (mᵏ a₁ α₁))
                                         ∙ (λ i → dfix apᵏ-body α₁ (pfix (mapᵏ-body _or_) (~ i) α₁ (lᵏ a₁ α₁)) (mᵏ a₁ α₁)))
         ∙ (ih▹ ⊛ kᵏ a ⊛′ next (Mreᵏ lᵇ lᵏ) ⊛′ next (Mreᵏ mᵇ mᵏ)) α
   go {ih▹} {kᵇ = true}  {kᵏ} {lᵇ} {lᵏ} {mᵇ} {mᵏ} {a} =
     λ α → ap (λ q → ((kᵏ a α) ·ᵏ Mreᵏ (lᵇ or mᵇ) q) ⋃ᵏ ((lᵏ a α) ⋃ᵏ (mᵏ a α)))
                     ((fun-ext λ a₁ → ▹-ext λ α₁ → (λ i → pfix apᵏ-body (~ i) α₁ (mapᵏ _or_ (lᵏ a₁ α₁)) (mᵏ a₁ α₁))
                                                 ∙ (λ i → dfix apᵏ-body α₁ (pfix (mapᵏ-body _or_) (~ i) α₁ (lᵏ a₁ α₁)) (mᵏ a₁ α₁))))
           ∙ ap (λ q → q ⋃ᵏ ((lᵏ a α) ⋃ᵏ (mᵏ a α))) ((ih▹ ⊛ kᵏ a ⊛′ next (Mreᵏ lᵇ lᵏ) ⊛′ next (Mreᵏ mᵇ mᵏ)) α)
           ∙ unionᵏ-swap-inner

concat-union-distrib-r : (k l m : Lang A)
                        → k · (l ⋃ m) ＝ (k · l) ⋃ (k · m)
concat-union-distrib-r k l m = fun-ext λ κ → concat-union-distrib-rᵏ (k κ) (l κ) (m κ)

concat-assocᵏ : (k l m : gLang κ A)
              → (k ·ᵏ l) ·ᵏ m ＝ k ·ᵏ (l ·ᵏ m)
concat-assocᵏ {κ} = fix {k = κ} λ ih▹ → λ where
  k@(Mreᵏ kᵇ kᵏ) l@(Mreᵏ lᵇ lᵏ) m@(Mreᵏ mᵇ mᵏ) →
    ((k ·ᵏ l) ·ᵏ m)
      ＝⟨ ap (λ q → (q k l) ·ᵏ m) (fix-path ·ᵏ-body) ⟩
    (·ᵏ-body (next _·ᵏ_) k l ·ᵏ m)
      ＝⟨ ap (λ q → q (·ᵏ-body (next _·ᵏ_) k l) m) (fix-path ·ᵏ-body) ⟩
    ·ᵏ-body (next _·ᵏ_) (·ᵏ-body (next _·ᵏ_) k l) m
      ＝⟨ ap² Mreᵏ (and-assoc kᵇ lᵇ mᵇ) (fun-ext λ a → ▹-ext (go {ih▹ = ih▹} {kᵇ} {kᵏ} {lᵇ} {lᵏ} {mᵇ} {mᵏ})) ⟩
    ·ᵏ-body (next _·ᵏ_) k (·ᵏ-body (next _·ᵏ_) l m)
      ＝˘⟨ ap (λ q → q k (·ᵏ-body (next _·ᵏ_) l m)) (fix-path ·ᵏ-body) ⟩
    (k ·ᵏ ·ᵏ-body (next _·ᵏ_) l m)
      ＝˘⟨ ap (λ q → k ·ᵏ (q l m)) (fix-path ·ᵏ-body) ⟩
    (k ·ᵏ (l ·ᵏ m))
      ∎
   where
   go : {ih▹ : ▹ κ ((k l m : gLang κ A) → ((k ·ᵏ l) ·ᵏ m) ＝ (k ·ᵏ (l ·ᵏ m)))}
        {kᵇ : Bool} {kᵏ : A → ▹ κ (gMoore κ A Bool)}
        {lᵇ : Bool} {lᵏ : A → ▹ κ (gMoore κ A Bool)}
        {mᵇ : Bool} {mᵏ : A → ▹ κ (gMoore κ A Bool)}
        {a : A}
      → ▹[ α ∶ κ ] (condᵏ (kᵇ and lᵇ) (▹map _·ᵏ_ (condᵏ kᵇ (▹map _·ᵏ_ (kᵏ a) ⊛ next (Mreᵏ lᵇ lᵏ)) (lᵏ a)) ⊛ next (Mreᵏ mᵇ mᵏ)) (mᵏ a) α)
                    ＝
                  (condᵏ kᵇ (▹map _·ᵏ_ (kᵏ a) ⊛ next (Mreᵏ (lᵇ and mᵇ) (λ a₁ → condᵏ lᵇ (▹map _·ᵏ_ (lᵏ a₁) ⊛ next (Mreᵏ mᵇ mᵏ)) (mᵏ a₁))))
                            (condᵏ lᵇ (▹map _·ᵏ_ (lᵏ a) ⊛ next (Mreᵏ mᵇ mᵏ)) (mᵏ a)) α)
   go {ih▹} {kᵇ = false} {kᵏ} {lᵇ = false} {lᵏ} {mᵇ} {mᵏ} {a} =
     λ α → (ih▹ ⊛ kᵏ a ⊛′ next (Mreᵏ false lᵏ) ⊛′ next (Mreᵏ mᵇ mᵏ)) α
         ∙ λ i → (kᵏ a α) ·ᵏ (Mreᵏ false (λ a₁ α₁ → pfix ·ᵏ-body i α₁ (lᵏ a₁ α₁) (Mreᵏ mᵇ mᵏ)))
   go {ih▹} {kᵇ = false} {kᵏ} {lᵇ = true}  {lᵏ} {mᵇ} {mᵏ} {a} =
     λ α → (ih▹ ⊛ kᵏ a ⊛′ next (Mreᵏ true lᵏ) ⊛′ next (Mreᵏ mᵇ mᵏ)) α
         ∙ λ i → (kᵏ a α) ·ᵏ (Mreᵏ mᵇ (λ a₁ α₁ → (pfix ·ᵏ-body i α₁ (lᵏ a₁ α₁) (Mreᵏ mᵇ mᵏ)) ⋃ᵏ (mᵏ a₁ α₁)))
   go {ih▹} {kᵇ = true}  {kᵏ} {lᵇ = false} {lᵏ} {mᵇ} {mᵏ} {a} =
     λ α → concat-union-distrib-lᵏ ((kᵏ a α) ·ᵏ (Mreᵏ false lᵏ)) (lᵏ a α) (Mreᵏ mᵇ mᵏ)
         ∙ ap (_⋃ᵏ (lᵏ a α ·ᵏ Mreᵏ mᵇ mᵏ)) ((ih▹ ⊛ kᵏ a ⊛′ next (Mreᵏ false lᵏ) ⊛′ next (Mreᵏ mᵇ mᵏ)) α
                                                  ∙ λ i → (kᵏ a α) ·ᵏ (Mreᵏ false (λ a₁ α₁ → pfix ·ᵏ-body i α₁ (lᵏ a₁ α₁) (Mreᵏ mᵇ mᵏ))))
   go {ih▹} {kᵇ = true}  {kᵏ} {lᵇ = true}  {lᵏ} {mᵇ} {mᵏ} {a} =
     λ α → ap (_⋃ᵏ mᵏ a α) (concat-union-distrib-lᵏ ((kᵏ a α) ·ᵏ (Mreᵏ true lᵏ)) (lᵏ a α) (Mreᵏ mᵇ mᵏ))
         ∙ unionᵏ-assoc
         ∙ ap (_⋃ᵏ ((lᵏ a α ·ᵏ Mreᵏ mᵇ mᵏ) ⋃ᵏ mᵏ a α)) ((ih▹ ⊛ kᵏ a ⊛′ next (Mreᵏ true lᵏ) ⊛′ next (Mreᵏ mᵇ mᵏ)) α
                                                         ∙ λ i → (kᵏ a α) ·ᵏ (Mreᵏ mᵇ (λ a₁ α₁ → (pfix ·ᵏ-body i α₁ (lᵏ a₁ α₁) (Mreᵏ mᵇ mᵏ)) ⋃ᵏ (mᵏ a₁ α₁))))

concat-assoc : (k l m : Lang A)
             → (k · l) · m ＝ k · (l · m)
concat-assoc k l m = fun-ext λ κ → concat-assocᵏ (k κ) (l κ) (m κ)

concat-empty-lᵏ : (l : gLang κ A) → ∅ᵏ ·ᵏ l ＝ ∅ᵏ
concat-empty-lᵏ {κ} = fix {k = κ} λ ih▹ → λ where
  l@(Mreᵏ lᵇ lᵏ) →
    (⌜ ∅ᵏ ⌝ ·ᵏ l)
      ＝⟨ ap! (fix-path (pureᵏ-body false)) ⟩
    (pureᵏ-body false (next ∅ᵏ) ·ᵏ l)
      ＝⟨ ap (λ q → q (pureᵏ-body false (next ∅ᵏ)) l) (fix-path ·ᵏ-body) ⟩
    ·ᵏ-body (next _·ᵏ_) (pureᵏ-body false (next ∅ᵏ)) l
      ＝⟨ ap (Mreᵏ false) (fun-ext λ _ → ▹-ext (ih▹ ⊛ next l)) ⟩
    pureᵏ-body false (next ∅ᵏ)
      ＝˘⟨ fix-path (pureᵏ-body false) ⟩
    ∅ᵏ
      ∎

concat-empty-l : (l : Lang A) → ∅ · l ＝ ∅
concat-empty-l l = fun-ext λ κ → concat-empty-lᵏ (l κ)

concat-empty-rᵏ : (l : gLang κ A) → l ·ᵏ ∅ᵏ ＝ ∅ᵏ
concat-empty-rᵏ {κ} = fix {k = κ} λ ih▹ → λ where
  l@(Mreᵏ lᵇ lᵏ) →
    (l ·ᵏ ⌜ ∅ᵏ ⌝)
      ＝⟨ ap! (fix-path (pureᵏ-body false)) ⟩
    (l ·ᵏ pureᵏ-body false (next ∅ᵏ))
      ＝⟨ ap (λ q → q l (pureᵏ-body false (next ∅ᵏ))) (fix-path ·ᵏ-body) ⟩
    ·ᵏ-body (next _·ᵏ_) l (pureᵏ-body false (next ∅ᵏ))
      ＝⟨ ap² Mreᵏ (and-absorb-r lᵇ) (fun-ext λ a → ▹-ext (go {ih▹ = ih▹} {lᵇ} {lᵏ})) ⟩
    pureᵏ-body false (next ∅ᵏ)
      ＝˘⟨ fix-path (pureᵏ-body false) ⟩
    ∅ᵏ
      ∎
    where
    go : {ih▹ : ▹ κ ((l : gLang κ A) → (l ·ᵏ ∅ᵏ) ＝ ∅ᵏ)}
         {lᵇ : Bool} {lᵏ : A → ▹ κ (gLang κ A)}
         {a : A}
       → ▹[ α ∶ κ ] ((if lᵇ then ▹map _⋃ᵏ_ (next _·ᵏ_ ⊛ lᵏ a ⊛ next (Mreᵏ false (λ _ → next ∅ᵏ))) ⊛ next ∅ᵏ
                            else next _·ᵏ_ ⊛ lᵏ a ⊛ next (Mreᵏ false (λ _ → next ∅ᵏ))) α)
                   ＝ ∅ᵏ
    go {ih▹} {lᵇ = false} {lᵏ} {a} =
      λ α → ap (lᵏ a α ·ᵏ_) (sym $ fix-path (pureᵏ-body false))
          ∙ (ih▹ ⊛ lᵏ a) α
    go {ih▹} {lᵇ = true}  {lᵏ} {a} =
      λ α → union-empty-rᵏ
          ∙ ap (lᵏ a α ·ᵏ_) (sym $ fix-path (pureᵏ-body false))
          ∙ (ih▹ ⊛ lᵏ a) α

concat-empty-r : (l : Lang A) → l · ∅ ＝ ∅
concat-empty-r l = fun-ext λ κ → concat-empty-rᵏ (l κ)

concat-unit-lᵏ : (l : gLang κ A) → εᵏ ·ᵏ l ＝ l
concat-unit-lᵏ {κ} l@(Mreᵏ lᵇ lᵏ) =
  εᵏ ·ᵏ l
    ＝⟨ (ap (λ q → q εᵏ l) (fix-path ·ᵏ-body)) ⟩
  ·ᵏ-body (next _·ᵏ_) εᵏ l
    ＝⟨ ap (Mreᵏ lᵇ) (fun-ext λ a → ▹-ext λ α → (λ i → condᵏ true (next (concat-empty-lᵏ (Mreᵏ lᵇ lᵏ) i)) (lᵏ a) α)
                                              ∙ λ i → ▹map (fun-ext {f = ∅ᵏ ⋃ᵏ_} (λ l → union-empty-lᵏ) i) (lᵏ a) α) ⟩
  l
    ∎

concat-unit-l : (l : Lang A) → ε · l ＝ l
concat-unit-l l = fun-ext λ κ → concat-unit-lᵏ (l κ)

concat-unit-rᵏ : (l : gLang κ A) → l ·ᵏ εᵏ ＝ l
concat-unit-rᵏ {κ} = fix {k = κ} λ ih▹ → λ where
  l@(Mreᵏ lᵇ lᵏ) →
    l ·ᵏ εᵏ
      ＝⟨ (ap (λ q → q l εᵏ) (fix-path ·ᵏ-body)) ⟩
    ·ᵏ-body (next _·ᵏ_) l εᵏ
      ＝⟨ ap² Mreᵏ (and-id-r lᵇ) (fun-ext λ a → ▹-ext λ α → go {ih▹ = ih▹} {lᵇ} {lᵏ} α) ⟩
    l
      ∎
   where
   go : {ih▹ : ▹ κ ((l : gLang κ A) → l ·ᵏ εᵏ ＝ l)}
        {lᵇ : Bool} {lᵏ : A → ▹ κ (gMoore κ A Bool)}
        {a : A}
      → ▹[ α ∶ κ ] (condᵏ lᵇ (▹map _·ᵏ_ (lᵏ a) ⊛ next εᵏ) (next ∅ᵏ) α)
                    ＝
                  (lᵏ a α)
   go {ih▹} {lᵇ = false} {lᵏ} {a} = ih▹ ⊛ lᵏ a
   go {ih▹} {lᵇ = true}  {lᵏ} {a} = λ α → union-empty-rᵏ ∙ (ih▹ ⊛ lᵏ a) α

concat-unit-r : (l : Lang A) → l · ε ＝ l
concat-unit-r l = fun-ext λ κ → concat-unit-rᵏ (l κ)

-- Kleene star laws

star-emptyᵏ : (∅ᵏ {κ = κ} {A = A}) ＊ᵏ ＝ εᵏ
star-emptyᵏ =
  ⌜ ∅ᵏ ⌝ ＊ᵏ
    ＝⟨ ap! (fix-path (pureᵏ-body false)) ⟩
  (pureᵏ-body false (next ∅ᵏ) ＊ᵏ)
    ＝⟨ ap (λ q → q (pureᵏ-body false (next ∅ᵏ))) (fix-path ＊ᵏ-body) ⟩
  ＊ᵏ-body (next _＊ᵏ) (pureᵏ-body false (next ∅ᵏ))
    ＝⟨ ap (Mreᵏ true) (fun-ext λ a → ▹-ext λ _ → concat-empty-lᵏ ((Mreᵏ false (λ _ → next ∅ᵏ)) ＊ᵏ)) ⟩
  εᵏ
    ∎

star-empty : (∅ {A = A}) ＊ ＝ ε
star-empty = fun-ext λ κ → star-emptyᵏ

star-concat-idemᵏ : (l : gLang κ A) → (l ＊ᵏ) ·ᵏ (l ＊ᵏ) ＝ l ＊ᵏ
star-concat-idemᵏ {κ} = fix {k = κ} λ ih▹ → λ where
  l@(Mreᵏ lᵇ lᵏ) →
      ((l ＊ᵏ) ·ᵏ (l ＊ᵏ))
        ＝⟨ ap (λ q → (q l ·ᵏ (l ＊ᵏ))) (fix-path ＊ᵏ-body) ⟩
      (＊ᵏ-body (next _＊ᵏ) l ·ᵏ (l ＊ᵏ))
        ＝⟨ ap (λ q → ＊ᵏ-body (next _＊ᵏ) l ·ᵏ q l) (fix-path ＊ᵏ-body) ⟩
      (＊ᵏ-body (next _＊ᵏ) l ·ᵏ ＊ᵏ-body (next _＊ᵏ) l)
        ＝⟨ ap (λ q → q (＊ᵏ-body (next _＊ᵏ) l) (＊ᵏ-body (next _＊ᵏ) l)) (fix-path ·ᵏ-body) ⟩
      ·ᵏ-body (next _·ᵏ_) (＊ᵏ-body (next _＊ᵏ) l) (＊ᵏ-body (next _＊ᵏ) l)
        ＝⟨ ap (Mreᵏ true) (fun-ext λ a → ▹-ext (go {ih▹ = ih▹} {lᵇ} {lᵏ} {a})) ⟩
      ＊ᵏ-body (next _＊ᵏ) l
        ＝˘⟨ ap (_$ l) (fix-path ＊ᵏ-body) ⟩
      (l ＊ᵏ)
        ∎
    where
    go : {ih▹ : ▹ κ ((l : gLang κ A) → ((l ＊ᵏ) ·ᵏ (l ＊ᵏ)) ＝ (l ＊ᵏ))}
         {lᵇ : Bool} {lᵏ : A → ▹ κ (gMoore κ A Bool)}
         {a : A}
       → ▹[ α ∶ κ ] ((▹map _⋃ᵏ_ (▹map _·ᵏ_ (▹map _·ᵏ_ (lᵏ a) ⊛ next ((Mreᵏ lᵇ lᵏ) ＊ᵏ))
                                         ⊛ next (Mreᵏ true (λ a₁ → ▹map _·ᵏ_ (lᵏ a₁) ⊛ next ((Mreᵏ lᵇ lᵏ) ＊ᵏ))))
                             ⊛ (▹map _·ᵏ_ (lᵏ a) ⊛ (next ((Mreᵏ lᵇ lᵏ) ＊ᵏ)))) α)
                     ＝
                   ((lᵏ a α) ·ᵏ ((Mreᵏ lᵇ lᵏ) ＊ᵏ))
    go {ih▹} {lᵇ} {lᵏ} {a} = λ α →
       ((▹map _⋃ᵏ_ (▹map _·ᵏ_ (▹map _·ᵏ_ (lᵏ a) ⊛ next ((Mreᵏ lᵇ lᵏ) ＊ᵏ))
                                         ⊛ next (Mreᵏ true (λ a₁ → ▹map _·ᵏ_ (lᵏ a₁) ⊛ next ((Mreᵏ lᵇ lᵏ) ＊ᵏ))))
                             ⊛ (▹map _·ᵏ_ (lᵏ a) ⊛ (next ((Mreᵏ lᵇ lᵏ) ＊ᵏ)))) α)
         ＝⟨ ap (λ q → ((lᵏ a α ·ᵏ (Mreᵏ lᵇ lᵏ ＊ᵏ)) ·ᵏ (Mreᵏ true q)) ⋃ᵏ (lᵏ a α ·ᵏ (Mreᵏ lᵇ lᵏ ＊ᵏ)))
                (fun-ext λ a₁ → ▹-ext λ α₁ → ap (lᵏ a₁ α₁ ·ᵏ_) (λ i → pfix ＊ᵏ-body (~ i) α₁ (Mreᵏ lᵇ lᵏ))) ⟩
       (⌜ (lᵏ a α ·ᵏ (Mreᵏ lᵇ lᵏ ＊ᵏ)) ·ᵏ (Mreᵏ lᵇ lᵏ ＊ᵏ) ⌝ ⋃ᵏ (lᵏ a α ·ᵏ (Mreᵏ lᵇ lᵏ ＊ᵏ)))
         ＝⟨ ap! (concat-assocᵏ (lᵏ a α) (Mreᵏ lᵇ lᵏ ＊ᵏ) (Mreᵏ lᵇ lᵏ ＊ᵏ)) ⟩
       ((lᵏ a α ·ᵏ ⌜ (Mreᵏ lᵇ lᵏ ＊ᵏ) ·ᵏ (Mreᵏ lᵇ lᵏ ＊ᵏ) ⌝) ⋃ᵏ (lᵏ a α ·ᵏ (Mreᵏ lᵇ lᵏ ＊ᵏ)))
         ＝⟨ ap! ((ih▹ ⊛ next (Mreᵏ lᵇ lᵏ)) α) ⟩
       ((lᵏ a α ·ᵏ (Mreᵏ lᵇ lᵏ ＊ᵏ)) ⋃ᵏ (lᵏ a α ·ᵏ (Mreᵏ lᵇ lᵏ ＊ᵏ)))
         ＝⟨ unionᵏ-idem ⟩
       ((lᵏ a α) ·ᵏ ((Mreᵏ lᵇ lᵏ) ＊ᵏ))
         ∎
