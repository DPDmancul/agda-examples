# A more complex proof about commutativity

<!--
```
{-# OPTIONS --allow-unsolved-metas --without-K #-}
```
-->

In `Data.Nat.Properties` there are already the proofs for commutative, associative, ... properties. So we will see a more complex proof: the commutativity of the two middle terms in an addition of four naturals.

To do proofs like this it is convenient to use `≡-Reasoning` which allow us to do the proof step-by-step.

```agda
open import Data.Nat
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

comm-middle : (a b c d : ℕ) → a + b + c + d ≡ a + c + b + d
comm-middle a b c d = begin
  ((a + b) + c) + d ≡⟨ {!!} ⟩
  (a + (b + c)) + d ≡⟨ {!!} ⟩
  (a + (c + b)) + d ≡⟨ {!!} ⟩
  ((a + c) + b) + d ∎
```

Now that we have defined the steps to do (left of the `≡⟨ ⟩`) we can put the proof of each step between the angular brackets. Note that the parentheses have always been reported to highlight the associativity of the plus operator: they are not all mandatory.

Before continuing we can notice that the last term of the addition (_d_) is never involved in the proof, so we can save us some work by proving first this lemma

```agda
lemma : (a b c : ℕ) → a + b + c ≡ a + c + b
lemma a b c = begin
  (a + b) + c ≡⟨ +-assoc a b c ⟩
  a + (b + c) ≡⟨ cong (a +_) (+-comm b c) ⟩
  a + (c + b) ≡˘⟨ +-assoc a c b ⟩
  (a + c) + b ∎
```

In the last proof we used `≡˘⟨ ⟩` which means use the symmetric of the proof: `+-assoc` is `(x + y) + z ≡ x + (y + z)`, the symmetric `x + (y + z) ≡ (x + y) + z`.

Now we can conclude our proof

```agda
comm-middle' : (a b c d : ℕ) → a + b + c + d ≡ a + c + b + d
comm-middle' a b c d = cong (_+ d) (lemma a b c)
```
