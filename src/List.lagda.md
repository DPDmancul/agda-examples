# Lists

<!--
```
{-# OPTIONS --safe --without-K #-}

module List where

open import Data.Nat hiding (pred)
```
-->

Agda could be used also to prove algorithm correctness. Here we will see some examples with lists.

The definition of a list resembles the definition of naturals: an empty list (`[]`, nil) is a list and `_∷_` is an operator (function) which takes an elemnt and a list and returns another list (which prepends the element to the list). 

```agda
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_ -- set operator precedence
```

Here we can see `List` is a dependent type: it depends on the type `A`, which is the type of its elements. Here we can see an example of list of naturals

```agda
example-list : List ℕ
example-list = 2 ∷ 3 ∷ 5 ∷ 7 ∷ 11 ∷ []
-- example-list is [2, 3, 5, 7, 11]
```

We can use the predefined list type

<!--
```
module Example where
```
-->
```agda
  open import Data.List
```

## Functions

Let's define a function which returns the list length. Since lists are inductively defined this function will be recursive

```agda
length : {A : Set} → List A → ℕ
length []       = 0
length (x ∷ xs) = suc (length xs)
```

we can see the argument `A` in curly braces: this syntax is used to define it as an implicit parameter. We will not need to provide it as argument when calling the function: it will be inferred from the provided list type.

Now define a function which removes the head of the list

```agda
tail : {A : Set} → List A → List A
tail []       = []
tail (x ∷ xs) = xs
```

## One simple proof of correctness

Now let's prove the length of the tail of a list is the predecessor of the length of the list.

```agda
pred : ℕ → ℕ
pred zero    = 0
pred (suc n) = n

open import Relation.Binary.PropositionalEquality

proof : {A : Set} → (xs : List A) → length (tail xs) ≡ pred (length xs)
proof []       = refl
proof (x ∷ xs) = refl
```

