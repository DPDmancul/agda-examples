# Syllogisms

<!--
```agda
{-# OPTIONS --safe --without-K #-}

module Syllogism where
```
-->

```agda
module _
  (Train Puff Thomas Aristotele : Set)
  where

  thomas-puffs : (Train → Puff) → (Thomas → Train) → (Thomas → Puff)
  thomas-puffs train-puffs thomas-is-train thomas = train-puffs (thomas-is-train thomas)
```

```agda
module _
  (Middle Subject Predicate : Set)
  where

  barbara : (Middle → Predicate) → (Subject → Middle) → (Subject → Predicate)
  barbara major minor subject = major (minor subject)
```
