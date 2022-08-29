{-# OPTIONS --safe --without-K #-}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
