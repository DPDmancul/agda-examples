----------------------------------------------------------------------
------------ Trascrizione dell'incontro del 31 marzo 2023 ------------
--                                                                  --
-- Video: https://youtu.be/KMKmyOJvG5s                              --
-- Appunti (in inglese): https://dpdmancul.gitlab.io/agda-examples/ --
----------------------------------------------------------------------

---------------------
-- Numeri naturali --
---------------------

open import Data.Nat

-- data ℕ : Set where
--   zero : ℕ
--   suc : ℕ → ℕ

open import Relation.Binary.PropositionalEquality -- per l'uguaglianza (≡)

zero-proof : zero ≡ 0
zero-proof = refl

one-proof : suc zero ≡ 1
one-proof = refl

one : ℕ
one = suc zero

two-proof : suc one ≡ 2
two-proof = refl

somma : ℕ → ℕ → ℕ
somma zero    m = m
somma (suc n) m = suc (somma n m)

-- suc n + m = (n + 1) + m = (n + m) + 1 = suc (n + m)

-- _+_ = somma
-- _+_ a b = a + b

-- ipotesi : n ∈ ℕ
-- tesi : n + 0 = n
-- ipotesi ⇒ tesi
-- n ∈ ℕ ⇒ n + 0 = n
sum-zero : (n : ℕ) → n + 0 ≡ n
sum-zero zero = refl
sum-zero (suc n') rewrite sum-zero n' = refl

open import Data.Nat.Properties -- contiene +-assoc, +-comm, ...

open ≡-Reasoning

comm-end : (a b c : ℕ) → a + b + c ≡ a + c + b
comm-end a b c = begin
  (a + b) + c ≡⟨ +-assoc a b c ⟩
  a + (b + c) ≡⟨ cong (a +_) (+-comm b c) ⟩
  a + (c + b) ≡˘⟨ +-assoc a c b  ⟩
  (a + c) + b ∎

--------------
--- Logica ---
--------------

-- Modus ponens
-- P ⇒ Q e P è vero allora Q è vero

modus-ponens : {P Q : Set} → (P → Q) → P → Q
modus-ponens p→q p = p→q p

-- Modus tollens
-- P ⇒ Q e Q è falso allora P è falso

-- Q è falso = Q ⇒ falso

open import Data.Empty

-- data ⊥ : Set where
--

-- ¬ Q = Q → ⊥

open import Relation.Nullary

-- ¬_ : Set → Set
-- ¬ X = X → ⊥

open import Relation.Nullary.Negation

-- ¬ P = P → ⊥
modus-tollens : {P Q : Set} → (P → Q) → ¬ Q → ¬ P
modus-tollens p→q ¬q p = contradiction (modus-ponens p→q p) ¬q

-- Principio del terzo escluso
-- X oppure ¬ X
-- Non si può dimostrarlo, ma si può dimostrare che non è vero che è falso

open import Data.Sum

pte : {A : Set} → ¬ ¬ (A ⊎ ¬ A)
pte a⊎¬a→⊥ = a⊎¬a→⊥ (inj₂ (λ x → a⊎¬a→⊥ (inj₁ x)))

-- ¬ ¬ X è una monade di continuazione (come le promesse, Future, Task della programmazione asincrona)
-- non possiamo ottenere il valore di X dalla monade, ma possiamo operare su di esso con una funzione
-- X → Y, ottenendo una monade ¬ ¬ Y (continue with)

¬¬map : {X Y : Set} → (X → Y) → ¬ ¬ X → ¬ ¬ Y
¬¬map x→y x→⊥→⊥ y→⊥ = x→⊥→⊥ (λ z → y→⊥ (modus-ponens x→y z))


-- Sillogismi

module _
  (Treno Sbuffa Thomas Aristotele : Set → Set)
  where

  -- tutti i treni sbuffano, Thomas è un treno, quindi Thomas sbuffa
  thomas-sbuffa : (∀ {x} → Treno x → Sbuffa x) → (∀ {x} → Thomas x → Treno x) →  (∀ {x} → Thomas x → Sbuffa x)
  thomas-sbuffa treno-sbuffa thomas-treno thomas = treno-sbuffa (thomas-treno thomas)

  -- tutti i treni sbuffano, Aristotele (molto annoiato da questo corso) sbuffa, Aristotele f un treno
  -- aristotele-treno : (∀ {x} → Treno x → Sbuffa x) → (∀ {x} → Aristotele x → Sbuffa x) → (∀ {x} → Aristotele x → Treno x)
  -- aristotele-treno treno-sbuffa aristotele-sbuffa aristotele = -- non dimostrabile (ovviamente)


----------------------------------
-- Programmazione (Informatica) --
----------------------------------

-- open import Data.List

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_ 

example-list : List ℕ
example-list = 5 ∷ 7 ∷ 20 ∷ 1 ∷ []
-- [5, 7, 20, 1]

lenght : {A : Set} → List A → ℕ
lenght []       = 0
lenght (x ∷ xs) = suc (lenght xs)

tail : {A : Set} → List A → List A
tail []       = []
tail (x ∷ xs) = xs

-- pred : ℕ → ℕ
-- pred zero = zero
-- pred (suc n) = n

proof-list : {A : Set} → (xs : List A) → lenght (tail xs) ≡ pred (lenght xs)
proof-list []       = refl
proof-list (x ∷ xs) = refl

