# Natural numbers

<!--
```
{-# OPTIONS --allow-unsolved-metas --without-K #-}

module Naturals where

module Example where 
```
-->

The type representing natural numbers is defined in a constructive way: `zero` is a natural, and `suc` is a function which given in input a natural returns another natural (its successor).

```agda
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ
```

We could use the built-in naturals with

<!--
```
open import Data.Nat hiding (_+_)

module Example-import where 
```
-->
```agda
  open import Data.Nat
```

it has some facilities, as for example the possibility of writing numbers with digits instead of writing a lot of "suc"

```agda
open import Relation.Binary.PropositionalEquality

zero-proof : zero ≡ 0
zero-proof = refl

one-proof : suc zero ≡ 1
one-proof = refl

two-proof : suc (suc zero) ≡ 2
two-proof = refl

three-proof : suc (suc (suc zero)) ≡ 3
three-proof = refl
```

Those above are some simple proofs: in the first line we found the name of the proof followed by the thesis (here `≡` from `Relation.Binary.PropositionalEquality` states we want to prove the two elements are equal), then in the next line there is the proof itself. `refl` is a special proof of equality which says: it's obviuos because they are the same (in fact somewhere in `Data.Nat` they are declared `0 = zero`, `1 = suc 0`, `2 = suc 1`, ...; in reality it is a more complex thing, but we can think it is like that).

## Defining an operator

We could try to define the sum of two integers (even if it is already defined in `Data.Nat`): it is very similar to write a function in a functional programming language. As we said in the introduction proofs are code, and in fact the syntax we have used above for proofs is the same we will use to define the function.

<!--
```
module Example-sum where 
```
-->
```agda
  _+_ : ℕ → ℕ → ℕ
  n + m = {!!}
```

Since the function name starts and ends with an underscore we can use it as an infix operator (`a + b` is equal to `_+_ a b`). After the function we can see its arguments (input) followed by the result type (output), in practice this function takes two naturals and returns another natural (the same of the former).

```agda
_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)
```

We can split on the variable _n_ which can be `zero` or `suc` of some other natural _n_. In the first case we have `0 + m` which must return `m`. In the second case whe have `(n + 1) + m` which is `(n + m) + 1`.

## Simple proof

Now let's prove that summing zero has no effect

<!--
```
module Example-sum-zero where 
```
-->

```agda
  sum-zero : (n : ℕ) → n + 0 ≡ n
  sum-zero n = {!!}
```

Here we can see we have an hypothesis (separated from the thesis by an arrow): _n_ is a natural. We can get the value of the hypothesis in the next line by placing a variable before the assignment sign (=).

```agda
sum-zero : (n : ℕ) → n + 0 ≡ n
sum-zero zero = refl
sum-zero (suc n) rewrite sum-zero n = refl
```

Here we have split on the variable _n_: it could be `0` or `suc` of some other _n_. In the first case the proof is obvious, in the second it becomes obvious if we apply by induction the proof itself for the new _n_ (which is lesser than the old _n_). We could write it also in this way using the congruence property of the equality.

```agda
sum-zero' : (n : ℕ) → n + 0 ≡ n
sum-zero' zero    = refl
sum-zero' (suc n) = cong suc (sum-zero' n)
```
