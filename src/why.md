# Why we need proof assistants?

Computers were created to do calculations in a fast way and without errors. Until now the theoretical part of mathematics was not automated: it is a hand task.

Proof assistants are the first step towards automatic demonstrations. For now the help they provide in doing proofs is really limited: they usually can fill only simple holes, but can provide a solid guidance on what is missing transforming a demonstration in a puzzle.

Even if the automatisms are not yet powerful it is already time to start using proof assistants in all practical cases: they guard us from demonstration errors. Proofs assistants are based on small theories of the [foundations of mathematics](https://en.wikipedia.org/wiki/Foundations_of_mathematics) (for example Agda is based on Martin-Löf type theory), and all the rest is checked by the computer to be correct. 

Proof assistant in fact are programming languages which, instead of describing algorithms which compute formula results, are used to program applications which, given in input the hypothesis of a theorem, execute the proof to return the thesis.

It is really important to have a guarantee proofs are correct: many times we don't notice some sneaky case. For example let's prove that all the dogs have the same name (which is obviously false). Let's prove it by induction

1. Base case: when we have a set of only one dog, all the dogs have the same name.
2. Inductive step: if we have a set of _n_ dogs let's pick two subsets which their union is the whole set and their intersection is not empty. Then we apply the inductive hypothesis on the two subsets and obtain that in each of the two subsets the dogs have the same name. At least a dog is in common between the two subsets, therefore all the dogs in the whole set must have the same name.

This proof could seem correct, but there is a sneaky mistake: we cannot build the aforementioned subsets for _n = 2_. In fact to have at least a dog in common the subsets must equal the whole set, hence the inductive hypothesis cannot be applied.

If we try to write this proof in a proof assistant it will notify us of the mistake.

