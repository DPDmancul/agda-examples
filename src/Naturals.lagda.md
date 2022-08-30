# Natural numbers

<!--
```
{-# OPTIONS --safe --without-K #-}
```
-->

```agda
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
```
