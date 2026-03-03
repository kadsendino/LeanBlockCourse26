/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Rename

/-
# Fundamentals of Lean Proofs
=====================

This module introduces the most basic building blocks for constructing proofs in Lean:
- Proving equalities with `rfl`
- Using hypotheses with `assumption`
- Precise matching with `exact`
- Basic implications (`→`) and the `intro` tactic
- Rewriting with `rw`

Note: Tactic usage counts in this course are approximate, measured against
Mathlib in February 2025.


## Proofs by reflexivity - the `rfl` tactic

The `rfl` tactic proves goals that are true by definition
and is (explicitly) used around 4000 times in mathlib and many
times more implicitly through `rw`, `exact`, `simp`, ...
-/

-- Simple equality: proves that 42 equals itself
theorem simple_int_eq : 42 = 42 := by
  rfl

#check simple_int_eq

theorem simple_int_eq' : (42 = 42 : Prop) := by
  rfl

-- Works with variables: proves that any proposition equals itself
example (P : Prop) : P = P := by
  rfl

-- also works in term mode
example (P : Prop) : P = P := rfl

-- Works with logical equivalence: proves that any proposition is equivalent to itself
example (P : Prop) : P ↔ P := by
  rfl

-- does *not* work in term mode!
-- example (P : Prop) : P ↔ P := rfl

-- Works with definitional equality: proves that 2 + 2 is 4 *by definition*
-- Why is this true? Because 4 = 0.succ.succ.succ.succ, 2 = 0.succ.succ
-- and a + b.succ = (a + b).succ, so unraveling everything, both sides reduce to
-- 0.succ.succ.succ.succ, which is four!
--
-- BUT: this only works because we are cleverly modelling Nat through DTT
-- as an inductive type, not explicitly through Peano axioms! -> P05
example : 2 + 2 = 4 := by
  rfl

-- Even works with type-level equality.
-- We will explore types in more detail later.
example (α : Type) : α = α := by
  rfl

-- Note that this does *not* work since ↔ only works
-- with Prop not arbitrary Type
-- example (α : Type) : α ↔ α := by
--   rfl


/-
## Using hypotheses - the `assumption` tactic

The `assumption` tactic looks through the available hypotheses and tries to find one
that exactly matches the goal. This is useful when you already have exactly what you
need to prove in your context. This tactic is essentially unused in mathlib.
We will learn in a bit why.
-/

-- Given a natural number `n` where `10 > n` and `1 < n`, prove that `1 < n`
-- Note that the linter flags `h₁` as an unused assumption
example (n : ℕ) (h₁ : 10 > n) (h₂ : 1 < n) : 1 < n := by
  assumption

-- This also works because 1 < n is the same as n > 1 by reflexivity
example (n : ℕ) (h₁ : 10 > n) (h₂ : n > 1) : 1 < n := by
  assumption

example (n : ℕ) : (1 < n : Prop) = (n > 1 : Prop) := rfl

-- Given proposition `P` and its proof, prove `P`
--
-- `(P : Prop)` is just a proposition, it can be true, false, unprovable
-- a trivial lemma, a known theorem, an open conjecture, or complete garbage
-- 
-- `(p : P)` is an instantiation of `P` and therefore a proof to lean.
-- Notably we are not working with booleans or even ⊤ here!
example (P : Prop) (p : P) : P := by
  assumption

-- Given propositions `P` and `Q`, and proofs of both, prove `P`
-- `(P Q : Prop)` is just a short grouping of `(P : Prop) (Q : Prop)`
-- linting again complains about `(q : Q)` being unused, but 
-- `(Q : Prop)` is fine because `(q : Q)` uses it (until you remove it)
example (P Q : Prop) (p : P) (q : Q) : P := by
  assumption

/-
## Precise matching - the `exact` tactic

The `exact` tactic allows us to provide a term that precisely matches the goal type.
Unlike assumption, which searches for matches, exact requires us to specify exactly
which term we want to use, but otherwise has the same effect. The `rfl` tactic in fact
was just syntax sugar for `exact rfl`. The tactic `exact?` looks for any term that can be
used to close the goal. This tactic is used over 40,000 times in mathlib.
-/

-- Given a natural number `n` where `10 > n` and `1 < n`, prove that `1 < n`
-- `_` makes the linter not complain, refers to intentionally unnamed variable
-- same as in many other languages. Note that `\N(at)` produces `ℕ`
example (n : ℕ) (_ : 10 > n) (h₂ : 1 < n) : 1 < n := by  
  exact h₂ -- `exact` is leans `return` (in tactic mode, in term mode its implicit)

-- Given proposition `P` and its proof, prove `P`
example (P : Prop) (p : P) : P := by
  exact p

-- Given propositions `P` and `Q`, and proofs of both, prove `P`
example (P Q : Prop) (p : P) (_ : Q) : P := by
  exact p


/-
## Exercise Block 1
-/

-- Exercise 1.1
-- State and prove that `3 + 2 = 5`
example : 3 + 2 = 5 := by
  rfl

-- Exercise 1.2
-- State and prove that given any arbitrary proposition `M`
-- and a proof of it, we know that the proposition holds
example (M : Prop) (m : M) : M := by
  exact m

/-
## Basic implications

An implication `P → Q` can be proved by assuming `P` and proving `Q`.
-/

-- `P → Q` means that `P` implies `Q`
-- `h : P → Q` means `h` is a proof of the proposition `P → Q`
-- the same way that `p : P` is a proof of the proposition `P`

-- Note that `\to` produces `→`
example (P Q : Prop) (h : P → Q) : P → Q := by
  assumption

example (P Q : Prop) (h : P → Q) : P → Q := by
  exact h

-- this is called term mode (more on this later)
-- but note that this is no different than in Python implementing
-- ```
-- def foo(n: int) -> int:
--    return n
-- ```
example (P Q : Prop) (h : P → Q) : P → Q := h

-- Given a function `h : P → Q` and a proof of `P`, we get a proof of `Q`
-- `h p` just "throws" the proof of `P` into `h`
example (P Q : Prop) (h : P → Q) (p : P) : Q := by
  exact h p

-- This in fact might be somewhat more intuitive in term mode
-- because it is similar to the following silly python code
--
-- ```
-- def foo(n: int) -> float:
--   return float(n)
--
-- def bar(x: float) -> str:
--   return str(x)
-- 
-- def foobar(n: int) -> str:
--   return bar(foo(n))
-- ```
-- 
-- Just note that function application in lean does not use brackets!
example (P Q : Prop) (h : P → Q) (p : P) : Q := h p

-- We can compose `P → Q` and `Q → R` to get from `P` to `R`
-- Note that `h\1` produces `h₁` and `h\2` produces `h₂`
example (P Q R : Prop) (p : P) (h₁ : P → Q) (h₂ : Q → R) : R := by
  exact h₂ (h₁ p) -- brackets are needed to group / bind correctly

-- Again works in term mode
example (P Q R : Prop) (p : P) (h₁ : P → Q) (h₂ : Q → R) : R := h₂ (h₁ p)

-- We can also *first* compose `h₁` and `h₂` and *then* throw in `p`
-- Note that `\circ` produces `∘`
example (P Q R : Prop) (p : P) (h₁ : P → Q) (h₂ : Q → R) : R := by
  exact (h₂ ∘ h₁) p

-- The `<|` operator is a function application operator that binds less tightly
-- than function application. It lets us avoid parentheses by applying functions
-- from right to left, so `h₂ <| h₁ p` is equivalent to `h₂ (h₁ p)`.
example (P Q R : Prop) (p : P) (h₁ : P → Q) (h₂ : Q → R) : R := by
  exact h₂ <| h₁ p

-- The dollar sign `$` used to be a synonym for this operator
-- but usage is now discouraged by the linter
example (P Q R : Prop) (p : P) (h₁ : P → Q) (h₂ : Q → R) : R := by
  exact h₂ $ h₁ p


/-
## The `intro` tactic

The `intro` tactic is used to prove implications (`→`) by assuming the antecedent.
When proving `P → Q`, `intro p` creates a hypothesis `p : P` and changes the goal to `Q`.
It is used around 12,000 times in mathlib.

We already saw this for our proof that the composite of two continuous functions
is itself continuous. This is whatever implicitly happens in pen-and-paper proofs
when someone says "Let ... be ..." and it is clear that they are referring to
an assumption that they pulled from the proposition the want to show.
-/

-- The identity function: shows that any proposition implies itself
example (P : Prop) : P → P := by
  intro p
  exact p

-- Intro always applies when you have "LHS implies RHS"
-- and it instantiates the type LHS, so if LHS is a
-- proposition, this means we assume a proof of LHS
example (P : Prop) : P → P := by
  intro p
  assumption

-- Note that `id` is one instantiation of P → P (regardless of the type of P)
example (P : Prop) : P → P := by
  exact id

-- Also works in term mode
example (P : Prop) : P → P := id

-- `id` itself is actually just lambda function type magic
example (P : Prop) : P → P := fun p => p

example : (fun (α : Type) => α) = id := rfl

/-
## Exercise Block 2
-/

-- Exercise 2.1
-- Show, in at least two different ways, that if
-- `P` implies `Q` and `Q` implies `R`, then `P` implies `R`
example (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := by
  intro p
  let q := f p -- have already seen `let` in the examples in P01
  let r := g q
  exact r
-- or `by intro p; exact g (f p)` or `by exact g ∘ f`
-- or in term mode `fun p => g (f p)` or just `g ∘ f`

-- Exercise 2.2
-- Show that if `P` implies `Q`, `Q` implies `R`, and
-- `R` implies `S`, then `P` implies `S`
example (P Q R S : Prop) (h₁ : P → Q) (h₂ : Q → R) (h₃ : R → S) : P → S := by
  intro p
  exact h₃ <| h₂ <| h₁ p
-- or just term mode `h₃ ∘ h₂ ∘ h₁`

-- Note that `P → Q → R` is `P → (Q → R)`.
example (P Q R : Prop) : (P → Q → R) = (P → (Q → R)) := rfl
example (P Q R : Prop) : (P → Q → R) ↔ (P → (Q → R)) := by rfl

-- Exercise 2.3
-- Show that if `P` implies that `Q` implies `R`
-- and if also `P` implies `Q`, then `P` implies `R`.
-- Note that `→` is right-associative: `P → Q → R` is `P → (Q → R)`.
example (P Q R : Prop) (h₁ : P → Q → R) (h₂ : P → Q) : P → R := by
  sorry

-- Exercise 2.3 (alt)
-- Show that if the proposition `P` implies the proposition that
-- `Q` implies `R` and if we also have a proof of `P`, then
-- the proposition `Q → R` holds, i.e., we have a proof of it.
example (P Q R : Prop) (h₁ : P → (Q → R)) (p : P) : Q → R := by
  exact h₁ p

-- Exercise 2.4 (Master students)
example (P Q R : Prop) (h₂ : Q → R) : P → (Q → R) := by
  intro
  assumption -- or `exact h₂`

-- and the same in term mode
example (P Q R : Prop) (h₂ : Q → R) : P → (Q → R) := fun _ => h₂

-- Think if it like the following python code:
--
-- ```
-- def foo(n: int, s: str) -> str:
--   return s
-- ```
--
-- The input `n: int` (`p : P`) is completely superfluous and unused!
-- The output `-> str` we could have of course constructed in many
-- different ways, but if the type `str` suddenly (i) could not distinguish
-- between different instances (`"foo"` is the same as `"bar"`) and
-- (ii) creating an instance was hard, then suddenly `return s` is 
-- sensible and the only logical thing to do. This is what happens in our proof.

-- The boundary between assumptions (left of `:`) and statement to be proven
-- (right of `:`) is blurry as shown by intro. In fact, we will see that
-- ultimately this is just "nice syntax" for mathematicians and underlying it
-- everything is one large "arrowed" type. Note that in this version we avoid
-- the `intro p` and the liner flags `p : P` as unused.
example (P Q R : Prop) (h₂ : Q → R) (p : P) : (Q → R) := by
  exact h₂

-- Exercise 2.5 (Master students)
-- Note that `S → P → Q → R` is grouped as `S → (P → (Q → R))`
example (P Q R S : Prop) : (S → P → Q → R) = (S → (P → (Q → R))) := rfl

example (P Q R S : Prop) (h₂ : Q → R) : S → P → Q → R := by
  intro _ _ -- We can intro multiple things at the same time!
  assumption

-- and the same in term mode
example (P Q R S : Prop) (h₂ : Q → R) : S → P → Q → R := fun _ _ => h₂

/-
## The `revert` tactic

The `revert` tactic moves a hypothesis from the context back into the goal, essentially
reversing the effect of `intro`. It is used only around 350 times in mathlib.
-/

-- Note that `hA : A` is exactly the same as `a : A`. It's just a name!
example (A B : Prop) (hA : A) (h : A → B) : B := by
  exact h hA -- we have seen exactly this before

example (A B : Prop) (hA : A) (h : A → B) : B := by
  revert hA
  assumption


/-
## The `rw` tactic

The `rw` tactic performs substitutions using equalities (`=`) or equivalences (`↔`).
It's one of the most fundamental tactics in Lean, allowing us to:

- Use hypotheses to rewrite goals
- Use hypotheses to rewrite other hypotheses using `at`

This tactic is used around 70,000 times in mathlib.
-/

-- Basic rewriting in the goal
example (P Q : Prop) (h : P ↔ Q) : P → Q := by
  rw [h]
  intro q
  exact q -- or just both together with `exact id`

-- Without rewriting
example (P Q : Prop) (h : P ↔ Q) : P → Q := by
  intro p
  have p_impl_q := h.mp -- `mp`(modues ponens) is the `P → Q` direction of `P ↔ Q`
  exact p_impl_q p

-- In fact, our statement is just the modus ponens of the assumption `h`
example (P Q : Prop) (h : P ↔ Q) : P → Q := h.mp

-- Rewriting in hypotheses with `at`
example (P Q : Prop) (h₁ : P ↔ Q) (p : P) : Q := by
  rw [h₁] at p -- note that this only replaces the type `P` and does not rename the variable `p`
  assumption   -- or `exact p`

-- If you *reaaally* wanted to rename a variable, use `import Mathlib.Tactic.Rename`
example (P Q : Prop) (h₁ : P ↔ Q) (p : P) : Q := by
  rw [h₁] at p -- note that this only replaces the type `P` and does not rename the variable `p`
  rename' p => q
  exact q

-- Multiple rewrites
theorem test (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : R ↔ Q) : P ↔ R := by
  rw [h₁]
  rw [h₂] -- implicit `rfl` call automatically closes `Q ↔ Q` in goal

#print test -- tells us that `Iff.rfl` is invoked

example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : R ↔ Q) : P ↔ R := by
  rw [h₁, h₂] -- first replaces `P` with `Q`, then `R` with `Q` for `Q ↔ Q`

-- What if we flipped `Q ↔ R` around in `h₂`?
example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R := by
  rw [h₁, h₂] -- first replaces `P` with `Q`, then *that same* `Q` with `R` for `R ↔ R`

-- Works with equality of propositions too (but this is not really relevant for mathematics...)
example (P Q R : Prop) (h₁ : P = Q) (h₂ : Q = R) : P = R := by
  rw [h₁, h₂]
