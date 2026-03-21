# Tutorial: Proving Fractran Machines Don't Halt in Lean 4

This tutorial documents strategies and tips for proving non-halting of Fractran machines (FMs) in the BBfLean framework, distilled from completing all 8 proofs in the Size21 directory.

## Overview

Each FM operates on a state `Q = ℕ × ℕ × ℕ × ℕ × ℕ` (or `ℕ⁶` for 6-register machines). The FM is defined as a pattern-matching function `fm : Q → Option Q` where earlier patterns have higher priority. The goal is to prove `¬halts fm c₀`.

## The Universal Proof Strategy

Every non-halting proof follows the same high-level pattern:

1. **Simulate** the FM to discover a recurring canonical form
2. **Find an invariant** (a predicate `P` on states, or a parametric family `C : A → Q`)
3. **Prove progress**: from any state satisfying `P`, the FM reaches another state satisfying `P` via `⊢⁺` (at least one step)
4. **Bootstrap**: show `c₀` reaches a state satisfying `P`

```lean
theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ reaches a canonical state in N steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨...⟩) (by execute fm N)
  -- Progress: use either progress_nonhalt or progress_nonhalt_simple
  apply progress_nonhalt_simple (fm := fm) (A := ...) (fun params ↦ ⟨...⟩) init
  intro params; exists next_params; apply main_transition_lemma
```

## Step 1: Simulation and Pattern Discovery

Write a Python simulator to trace the FM from `c₀`:

```python
def simulate(rules, c0, max_steps=5000):
    c = c0
    for i in range(max_steps):
        for check, apply_rule in rules:
            if check(c):
                c = apply_rule(c)
                break
        else:
            return  # halted
```

Look for **canonical states** — states where most registers are zero (typically 3+ zeros out of 5). Track the sequence of canonical states to discover:
- Which registers are non-zero in the canonical form
- The recurrence relation between successive canonical states
- Whether the growth is linear, quadratic, exponential, etc.

### Common canonical forms encountered

| FM | Canonical Form | Transition | Growth |
|----|---------------|------------|--------|
| #1 | `(a, 0, 0, d, 0)` | `d → 2d+1` | Exponential |
| #20 | `(0, 0, c, d, 0)` | `(c,d) → (c+d+2, 2d+1)` | Exponential |
| #40 | `(d+1, 0, 0, d, 0)` | `d → d+1` | Linear |
| #60 | `(0, 0, c, 0, e)` | `c → 2c+1` | Exponential |
| #80 | `(e+1, 0, 0, 0, e)` | `e → 2e+1` | Exponential |
| #100 | `(a, 0, 0, 0, e)` | `a → a+2e` | Superlinear |
| #120 | `(a, 0, 0, 0, e)` | `e → e+1, a → a+e+1` | Quadratic |
| #140 | `(a, 0, 0, n, n, 0)` | `n → n+1, a → a+n` | Quadratic |

## Step 2: Choosing the Right Framework Lemma

The FM.lean framework provides two main lemmas for non-halting:

### `progress_nonhalt_simple`
Use when the canonical form can be parameterized by a simple type `A` (like `ℕ` or `ℕ × ℕ`) with an explicit next-state function:

```lean
apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
  (fun ⟨a, d⟩ ↦ ⟨a+2, 0, 0, d, 0⟩) ⟨init_a, init_d⟩
intro ⟨a, d⟩; exists ⟨next_a, next_d⟩; apply transition_lemma
```

This is the cleanest approach when you know both the current and next parameters explicitly.

### `progress_nonhalt`
Use when the next state's parameters depend on complex conditions (e.g., FM #100 where `e'` depends on `e mod 4`):

```lean
apply progress_nonhalt (fm := fm)
  (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ e + 1 ∧ e ≥ 1)
· intro c ⟨a, e, hq, ha, he⟩; subst hq
  obtain ⟨e', htrans, he'⟩ := transition_lemma e a
  exact ⟨_, ⟨_, e', rfl, by omega, he'⟩, htrans⟩
· exact ⟨_, _, rfl, by omega, by omega⟩  -- initial state satisfies P
```

## Step 3: Decomposing the Transition into Phases

The most important skill is decomposing the canonical transition into clean, provable phases. Each phase typically corresponds to one rule firing repeatedly.

### Common phase types

**Register transfer (one rule repeated)**:
These are the building blocks. Each converts one register to another:

```lean
-- R4 repeated: d → e (each d gives one e)
theorem d_to_e : ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c, d, k⟩ := by
  have many_step : ∀ k d, ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c, d, k⟩ := by
    intro k; induction' k with k h <;> intro d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k d
```

Key pattern: universally quantify over all free variables, use `induction'` with `intro`, and close with `ring_nf; finish`.

**Interleaved rule chains (two rules alternating)**:
When two rules alternate (e.g., R1 then R2), prove by induction on the number of pairs:

```lean
-- Each pair: R2 then R1
theorem r2r1_chain : ∀ k, ⟨a+1, 0, c+k, d, k⟩ [fm]⊢* ⟨a+1+k, 0, c, d+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro -- quantify free vars if needed
  · exists 0
  -- Show 2 steps (R2 then R1)
  step fm; step fm
  apply stepStar_trans (ih ...)
  ring_nf; finish
```

**Complex phases (strong induction)**:
When the interaction between rules doesn't decompose into simple repetition, use `Nat.strongRecOn`:

```lean
theorem complex_phase : ∀ E, ∀ A B, ⟨A, B, 0, 2, E⟩ [fm]⊢* ⟨...⟩ := by
  intro E; induction' E using Nat.strongRecOn with E ih; intro A B
  rcases E with _ | _ | E'
  · -- base case E=0
  · -- base case E=1
  · -- inductive case E'+2: take some steps, apply ih with E' < E'+2
    step fm; step fm; step fm
    apply stepStar_trans (ih E' (by omega) _ _)
    ring_nf; finish
```

**Parity-based case splits**:
When behavior differs for even/odd values:

```lean
rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
· -- d = 2K (even case)
· -- d = 2K + 1 (odd case)
```

## Step 4: Essential Tactics

### `step fm`
Applies one FM step with symbolic variables. Works by unfolding `fm`, simplifying, and checking `rfl`. This is the workhorse tactic — it handles pattern matching even with symbolic `a`, `b`, `c`, `d`, `e`.

### `finish`
Closes a `⊢*` goal with zero steps (`exists 0`).

### `execute fm n`
Applies `step fm` exactly `n` times then `finish`. Only works when the FM can deterministically execute `n` steps from the current symbolic state.

### `ring_nf`
Normalizes arithmetic expressions. Essential after `step fm` when the goal has expressions like `a + (k + 1) + 2` that need to match `a + k + 3`.

### `omega`
Solves linear arithmetic goals. Use for inequalities in invariant proofs.

### Composition lemmas
- `stepStar_trans`: compose two `⊢*` transitions
- `stepStar_stepPlus_stepPlus`: `⊢*` then `⊢⁺` gives `⊢⁺`
- `stepPlus_stepStar_stepPlus`: `⊢⁺` then `⊢*` gives `⊢⁺`
- `stepStar_not_halts_not_halts`: if A reaches B and B never halts, A never halts

## Step 5: Common Pitfalls

### 1. Rule priority matters
Lean's pattern matching tries rules in order. If both R3 (`a ≥ 1`) and R5 (`e ≥ 1`) could fire, the one listed FIRST in the match statement wins. Always check which rule actually fires in each state.

### 2. `step fm` may apply the wrong rule
If you expect R3 to fire but R1 has higher priority and also matches, `step fm` will apply R1. Trace the execution carefully before writing lemmas.

### 3. Parameterization pitfalls
When using `progress_nonhalt_simple`, the parameterization `C : A → Q` must satisfy `C(next_params) = actual_next_state`. If the mapping doesn't compose cleanly (e.g., the next `a` parameter depends on both current `a` and `d`), you may need a different parameterization or `progress_nonhalt` instead.

### 4. Arithmetic in Lean's ℕ
Natural number subtraction is truncating (`3 - 5 = 0`). Use `a + k` instead of `a - k` when possible. Express states like `(a-1, ...)` as `(a, ...)` with the input being `(a+1, ...)`.

### 5. Universal quantification in inductive lemmas
Always universally quantify ALL free variables inside the induction:
```lean
-- GOOD: quantify a, c, d inside
have many_step : ∀ k, ∀ a c d, ⟨a+k, ...⟩ [fm]⊢* ⟨a, ...⟩ := by
  intro k; induction' k with k h <;> intro a c d
  ...
-- BAD: free variables outside induction
have many_step : ⟨a+k, ...⟩ [fm]⊢* ⟨a, ...⟩ := by
  induction' k with k h  -- a, c, d are fixed!
```

### 6. The `ring_nf; finish` pattern
After `step fm` and `apply stepStar_trans (h ...)`, the goal often has the right values but in the wrong arithmetic form. `ring_nf` normalizes both sides, and `finish` closes with `exists 0`. This pattern appears in virtually every inductive lemma.

## Step 6: Proof Complexity Guide

From simplest to most complex:

1. **Linear growth** (FM #40): Single-parameter invariant, straightforward phases, may need parity case split
2. **Quadratic growth** (FM #120, #140): Two-parameter invariant, clean phase decomposition
3. **Exponential/doubling** (FM #80): Single-parameter with doubling, needs careful multi-phase decomposition
4. **Two-register exponential** (FM #1, #20): Two-parameter invariant with coupled recurrence
5. **Complex dynamics** (FM #60): Requires identifying non-obvious cycle structure, may need remainder-based case analysis
6. **Strong induction required** (FM #100): When transition depends on input mod k, use strong induction with explicit base cases for each residue class

## Quick Reference: Proof Template

```lean
import BBfLean.FM
import Mathlib.Tactic.Ring

namespace MyFM

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ... => ...
  | _ => none

-- Phase lemmas (register transfers, interleaved chains, etc.)
theorem phase1 : ... := by ...
theorem phase2 : ... := by ...

-- Main transition (compose phases)
theorem main_trans : ⟨canonical_state⟩ [fm]⊢⁺ ⟨next_canonical⟩ := by
  apply stepStar_stepPlus_stepPlus phase1
  apply stepPlus_stepStar_stepPlus phase2
  ...

-- Final theorem
theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨first_canonical⟩) (by execute fm N)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨x, y⟩ ↦ ⟨canonical_of x y⟩) ⟨init_x, init_y⟩
  intro ⟨x, y⟩; exists ⟨next_x, next_y⟩; apply main_trans
```
