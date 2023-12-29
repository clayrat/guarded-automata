{-# OPTIONS --guarded #-}
module Lang where

open import Prelude
open import Data.Bool
open import Data.Dec
open import Data.List

open import LaterCl
open import Clocked.Moore

private variable
  ℓ : Level
  A : 𝒰 ℓ
  k : Cl

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

_⋃_ : Lang A → Lang A → Lang A
_⋃_ = zipWithᵐ _or_

_⋂_ : Lang A → Lang A → Lang A
_⋂_ = zipWithᵐ _and_

-- TODO figure out combinators
corecᵏ-body : ▹ k (gMoore k A Bool → gMoore k A Bool → gMoore k A Bool)
            → gMoore k A Bool → gMoore k A Bool → gMoore k A Bool
corecᵏ-body c▹ (Mreᵏ kᵇ kᵏ) l@(Mreᵏ lᵇ lᵏ) =
  Mreᵏ (kᵇ and lᵇ) λ a → let kl′ = c▹ ⊛ (kᵏ a) ⊛ next l in if kᵇ then ▹map (zipWithᵏ _or_) kl′ ⊛ lᵏ a else kl′

corecᵏ : gMoore k A Bool → gMoore k A Bool → gMoore k A Bool
corecᵏ = fix corecᵏ-body

_·_ : Lang A → Lang A → Lang A
_·_ a b k = corecᵏ (a k) (b k)

starᵏ-body : ▹ k (gMoore k A Bool → gMoore k A Bool)
            → gMoore k A Bool → gMoore k A Bool
starᵏ-body s▹ l@(Mreᵏ _ k) = Mreᵏ true λ a → ▹map corecᵏ (k a) ⊛ (s▹ ⊛ next l)

starᵏ : gMoore k A Bool → gMoore k A Bool
starᵏ = fix starᵏ-body

_＊ : Lang A → Lang A
_＊ l k = starᵏ (l k)

-- laws

union-assoc : {k l m : Lang A}
            → (k ⋃ l) ⋃ m ＝ k ⋃ (l ⋃ m)
union-assoc = zipWithᵐ-assoc or-assoc
