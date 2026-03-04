---
title: "Measuring proof length"
parent: Addendum
nav_order: 9996
---

# Measuring proof length
{: .no_toc }

*March 4, 2026 · `P02.S03.B02`*

---

In the exercise blocks we asked you to minimize the number of non-whitespace characters in your proof. The course repo contains a custom `#golf` command that measures this automatically.

## Using `#golf` in your own project

To use `#golf` outside the course repo, copy [`LeanBlockCourse26/CodeGolf.lean`](https://github.com/FordUniver/LeanBlockCourse26/blob/main/LeanBlockCourse26/CodeGolf.lean) into the corresponding location in your project (i.e., `YourProject/CodeGolf.lean`) and add `import YourProject.CodeGolf` to any file where you want to use it. Then wrap your proof with `#golf`:

```lean
#golf example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro ⟨p, q⟩
  exact ⟨q, p⟩
-- Golf: 20 chars
```

## Scoring rules

Whitespace is free: indentation and newlines do not count. The tactic separator `;` is also free since it is equivalent to a newline, so formatting choices do not affect your score. The tactic combinator `<;>`, which applies a tactic to all remaining goals, **does** count.

## How it works

`#golf` is a custom Lean 4 elaboration command. It wraps any declaration (`example`, `theorem`, `def`), elaborates it normally, then extracts the proof body from the syntax tree using source positions. This avoids the need to manually paste your proof into a string.
