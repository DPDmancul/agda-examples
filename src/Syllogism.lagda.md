# Syllogisms

<!--
```agda
{-# OPTIONS --allow-unsolved-metas --without-K #-}

module Syllogism where
```
-->

We can use Agda as an assistant also for classical logic, here for example we will use it to construct syllogisms.

Let's start with a simple barabba syllogism (which could be also a darii, depending on the terms definition) proving that given the fact all trains puffs and that Thomas is a train, Thomas also puffs.

To avoid defining from scratch what a train and other terms are we use the _module_ feature of Agda. In the declaration of a module (with a name, or named with an underscore to make a nameless module) we can put the prerequisites of that module: some objects which we do not define, but which are needed and can be used in the module.

Recall that "A is B" in logic is \\(\forall x : A(x) \implies B(x)\\), which is `∀ {x} → A x → B x` in Agda; "no A is B" have to be translated into \\(\forall x : A(x) \implies \neg B(x)\\), which in Agda is `∀ {x} → A x → ¬ B x`.

```agda
module _
  (Train Puff Thomas Aristotele : Set → Set)
  where

  thomas-puffs : (∀ {x} → Train x → Puff x) → (∀ {y} → Thomas y → Train y) → (∀ {z} → Thomas z → Puff z)
  thomas-puffs train-puffs thomas-is-train thomas = train-puffs (thomas-is-train thomas)
```

Other than helping us (with `C-c C-,` and `C-c C-a`) writing the proof, Agda prevents us from proving a false Syllogism. For example the following stating that all trains puffs and Aristotele puffs, hence Aristotele is a train, which is obviously bad-formed. This is indeed not possible to prove in Agda: the hole cannot be filled.


```agda
  aristotele-is-train : (∀ {x} → Train x → Puff x) → (∀ {y} → Aristotele y → Puff y) → (∀ {z} → Aristotele z → Train z)
  aristotele-is-train train-puffs aristotele-puffs = {!!}
```

Indeed our `thomas-puffs` is a more generic proof: it proves all _barbara_ syllogisms: changing the names of types and variables this becomes evident:

```agda
module _
  (Middle Subject Predicate : Set → Set)
  where

  barbara : (∀ {x} → Middle x → Predicate x) → (∀ {y} → Subject y → Middle y) → (∀ {z} → Subject z → Predicate z)
  barbara major minor subject = major (minor subject)
  -- greeks-are-mortal = barbara men-are-mortal greeks-are-men 

  open import Relation.Nullary using (¬_)

  celarent : (∀ {x} → Middle x → ¬ Predicate x) → (∀ {y} → Subject y → Middle y) → (∀ {z} → Subject z → ¬ Predicate z)
  celarent major minor subject = major (minor subject)
  -- no-snake-has-fur = celarent no-reptile-has-fur snakes-are-reptile

  open import Relation.Nullary.Negation using (contradiction)

  camestres : (∀ {x} → Predicate x → Middle x) → (∀ {y} → Subject y → ¬ Middle y) → (∀ {z} → Subject z → ¬ Predicate z)
  camestres major minor subject predicate =  contradiction (major predicate) (minor subject)
  -- no-fish-is-snake = camestres snakes-are-reptiles no-fish-is-reptile
```

We can also make the proofs for particular propositions syllogisms.

Recall that "some A is B" in logic is \\(\exists x : A(x) \land B(x)\\), which is `∃[ x ] A x × B x` in Agda; "some A is not B" have to be translated into \\(\exists x : A(x) \land \neg B(x)\\), which in Agda is `∃[ x ] A x × ¬ Bx`.

```agda
  open import Data.Product

  darii : (∀ {x} → Middle x → Predicate x) → ∃[ y ] Subject y × Middle y → ∃[ z ] Subject z × Predicate z
  darii major (y , subject , middle) = y , subject , major middle
  -- some-pets-have-fur = darii rabbits-have-fur some-pets-are-rabbits

  disamis : ∃[ x ] Middle x × Predicate x  → (∀ {y} → Middle y → Subject y) → ∃[ z ] Subject z × Predicate z
  disamis (x , middle , predicate) minor = x , minor middle , predicate
  -- some-animals-are-pets = disamis some-birds-are-pets all-birds-are-animals

  ferio : (∀ {x} → Middle x → ¬ Predicate x) → ∃[ y ] Subject y × Middle y → ∃[ z ] Subject z × ¬ Predicate z
  ferio major (y , subject , middle) = y , subject , major middle
  -- some-reading-is-not-fun = ferio no-homework-is-fun some-reading-is-homework

  baroco : (∀ {x} → Predicate x → Middle x) → ∃[ y ] Subject y × ¬ Middle y → ∃[ z ] Subject z × ¬ Predicate z
  baroco major (y , subject , ¬middle) = y , subject , λ predicate → contradiction (major predicate) ¬middle
  -- some-pets-are-not-cats = baroco all-cats-are-mammals some-pets-are-not-mammals

  bocardo : ∃[ x ] Middle x × ¬ Predicate x → (∀ {y} → Middle y → Subject y) → ∃[ z ] Subject z × ¬ Predicate z
  bocardo (x , middle , ¬predicate) minor = x , minor middle , ¬predicate
  -- some-mammals-are-not-pets = bocardo some-cats-are-not-pets all-cats-are-mammals
```

And finally the proofs of the syllogisms with existential assumptions:

```agda
  barbari : (∀ {x} → Middle x → Predicate x) → (∀ {y} → Subject y → Middle y) → ∃[ z ] Subject z → ∃[ w ] Subject w × Predicate w
  barbari major minor (z , subject) =  z , subject , barbara major minor subject
  -- some-greeks-are-men = barbari men-are-mortal greeks-are-men greek

  bamalip : (∀ {x} → Predicate x → Middle x) → (∀ {y} → Middle y → Subject y) → ∃[ z ] Predicate z → ∃[ w ] Subject w × Predicate w
  bamalip major minor (z , predicate) = z , minor (major predicate) , predicate
  -- some-mortals-are-greek = bamalip greeks-are-men men-are-mortal greek

  celaront : (∀ {x} → Middle x → ¬ Predicate x) → (∀ {y} → Subject y → Middle y) → ∃[ z ] Subject z → ∃[ w ] Subject w × ¬ Predicate w
  celaront major minor (z , subject) = z , subject , celarent major minor subject
  -- some-snakes-have-no-fur = celaront no-reptiles-have-fur snakes-are-reptiles snake

  camestros : (∀ {x} → Predicate x → Middle x) → (∀ {y} → Subject y → ¬ Middle y) → ∃[ z ] Subject z → ∃[ w ] Subject w × ¬ Predicate w
  camestros major minor (z , subject) = z , subject , camestres major minor subject
  -- some-humas-are-not-horses = camestros horse-have-hooves no-humans-have-hooves human

  felapton : (∀ {x} → Middle x → ¬ Predicate x) → (∀ {y} → Middle y → Subject y) → ∃[ z ] Middle z → ∃[ w ] Subject w × ¬ Predicate w
  felapton major minor (z , middle) = z , minor middle , major middle 
  -- some-plants-are-not-animals = felapton no-flowers-are-animals flowers-are-plants flower

  darapti : (∀ {x} → Middle x → Predicate x) → (∀ {y} → Middle y → Subject y) → ∃[ z ] Middle z → ∃[ w ] Subject w × Predicate w
  darapti major minor (z , middle) = z , minor middle , major middle
  -- some-rhombuses-are-rectangles = darapti squares-are-rectangles squares-are-rhombuses square
```
