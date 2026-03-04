---
title: Quick Reference
parent: Cheat Sheets
nav_order: 0
---

# Quick Reference
{: .no_toc }

What tactic do I need? Find the connective in your **goal** or **hypothesis** and read across.

---

## Logical connectives

| | `⊢` Goal | Hypothesis `h` |
|---|---|---|
| **And** `P ∧ Q` | `constructor` / `exact ⟨p, q⟩` | `obtain ⟨p, q⟩ := h` / `h.1`, `h.2` |
| **Or** `P ∨ Q` | `left` / `right` | `rcases h with p \| q` |
| **Implication** `P → Q` | `intro p` | `apply h` / `exact h p` |
| **Negation** `¬P` | `intro p` (it is `P → False`) | `exact h p` / `contradiction` |
| **Equivalence** `P ↔ Q` | `constructor` | `rw [h]` / `h.mp`, `h.mpr` |
| **Inequality** `a ≠ b` | `intro h` (it is `a = b → False`) | `exact h rfl` / `contradiction` |

**`push_neg`** simplifies negated compound statements by pushing `¬` inward: `¬∀` becomes `∃ ¬`, `¬(P ∧ Q)` becomes `P → ¬Q`, and so on. Works on both goals (`push_neg`) and hypotheses (`push_neg at h`).

## Equality and arithmetic

| | `⊢` Goal | Hypothesis `h` |
|---|---|---|
| **Equality** `a = b` | `rfl` / `calc` / `ring` / `omega` | `rw [h]` / `rw [← h]` |
| **Inequality** `a < b`, `a ≤ b` | `omega` / `linarith` | `omega` / `linarith` |

Use `rw [h] at h'` to rewrite in a specific hypothesis. Use `nth_rw n [h]` to rewrite only the *n*-th occurrence.

## Quantifiers

| | `⊢` Goal | Hypothesis `h` |
|---|---|---|
| **Universal** `∀ x, P x` | `intro x` | `apply h` / `exact h a` |
| **Existential** `∃ x, P x` | `use a` | `obtain ⟨x, hx⟩ := h` |

## True, False, and closing tactics

| | `⊢` Goal | Hypothesis `h` |
|---|---|---|
| **True** | `trivial` | — |
| **False** | `exfalso` | `contradiction` |

When the goal matches a hypothesis exactly, `exact h` or `assumption` closes it.

## Proof structure

| Tactic | Effect |
|---|---|
| `have q := h p` | Forward step: derive a new fact from existing ones |
| `suffices p : P by ...` | Backward step: state what would be enough, then prove it |
| `by_contra h` | Assume `¬ goal` and derive `False` (classical) |
| `by_cases h : P` | Split into `P` and `¬P` branches (classical) |

## Automation

| Tactic | Proves |
|---|---|
| `simp` | Goals reducible by rewrite lemmas (`simp only [...]` for control) |
| `tauto` | Propositional tautologies |
| `omega` | Linear integer and natural number arithmetic |
| `linarith` | Linear arithmetic over ordered fields |
| `ring` | Polynomial identities in commutative (semi)rings |
| `norm_num` | Closed numerical expressions |
| `grind` | Mixed reasoning (congruence, arithmetic, quantifiers) |
| `exact?` / `apply?` | Search the library for a matching lemma |
