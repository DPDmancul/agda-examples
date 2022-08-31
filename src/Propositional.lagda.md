# Propositional logic

<!--
```agda
{-# OPTIONS --allow-unsolved-metas --without-K #-}

module Propositional where
```
-->

## Modus ponens

\\[P \implies Q, P \vdash Q\\]

The implication \\(P \implies Q \\) in Agda is a function transforming an element of type `P` into an element of type `Q`.

```agda
modus-ponens : {P Q : Set} → (P → Q) → P → Q
modus-ponens p→q p = p→q p
```

or shorter

```agda
modus-ponens' : {P Q : Set} → (P → Q) → P → Q
modus-ponens' p→q = p→q
```

## Modus tollens

\\[P \implies Q, \neg Q \vdash \neg P \\]

The negation in Agda is realized by a function taking an element of the type to negate and returning an element of the empty type (which is not possible).

```agda
data ⊥ : Set where
  -- this is the empty type (it has no elements)
  -- you can instead `open import Data.Empty`

-- The negation is an implication to the falsity (represented by the empty type)
¬_ : Set → Set
¬ X = X → ⊥
-- you can instead write `open import Relation.Nullary`
```

The modus tollens is proven by contradiction. Contradiction is a constructive proof because from nothing we can get all we want.

```agda
-- From nothing all holds
⊥-elim : {X : Set} → ⊥ → X
⊥-elim ()

-- From a contradiction all holds
contradiction : {X Y : Set} → X → ¬ X → Y
contradiction x x→⊥ = ⊥-elim (x→⊥ x) -- x→⊥ transforms elements of X (such as x) into elements of ⊥
-- you can instead write `open import Relation.Nullary.Negation`
```

Now we can prove modus tollens

```agda
modus-tollens : {P Q : Set} → (P → Q) → ¬ Q → ¬ P
modus-tollens p→q ¬q p = contradiction (p→q p) ¬q
```

or shorter

```agda
modus-tollens' : {P Q : Set} → (P → Q) → ¬ Q → ¬ P
modus-tollens' p→q q→⊥ p = q→⊥ (p→q p)
```

## Law of excluded middle

\\[A \lor \neg A\\]

This, which seems an obvious preposition, is not constructively provable. At least we can prove it is not false.

```agda
open import Data.Sum

lem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
lem {X} x⊎¬x→⊥ = x⊎¬x→⊥ (inj₂ ¬x)
  where
  ¬x : ¬ X -- X → ⊥
  ¬x x = x⊎¬x→⊥ (inj₁ x)
```

or shorter

```agda
lem' : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
lem' x⊎¬x→⊥ = x⊎¬x→⊥ (inj₂ λ x → x⊎¬x→⊥ (inj₁ x))
```
