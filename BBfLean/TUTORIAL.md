# Tutorial: Proving Fractran Machines Don't Halt in Lean 4

Distilled from completing all 132 sorry proofs in the Size21 directory (100% success rate).

## Universal Proof Strategy

1. **Simulate** the FM in Python to find canonical states (most registers zero) and recurrence
2. **Find an invariant** — a parametric family `C : A → Q` or predicate `P`
3. **Prove progress** — from any canonical state, reach the next via `⊢⁺`
4. **Bootstrap** — show `c₀` reaches the first canonical state

```lean
theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨...⟩) (by execute fm N)
  apply progress_nonhalt_simple (fm := fm) (A := ...) (fun params ↦ ⟨...⟩) init
  intro params; exists next_params; apply main_transition_lemma
```

## Choosing the Framework Lemma

- **`progress_nonhalt_simple`** (~60%): When the next-state function is deterministic given parameters. Clean for linear, quadratic, exponential with explicit parameterization.
- **`progress_nonhalt`** (~40%): When transitions depend on modular arithmetic (parity, mod 3/4), invariant inequalities (e.g., `a >= e/2 + 1`), or alternating canonical families.

```lean
-- progress_nonhalt_simple example
apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
  (fun ⟨a, d⟩ ↦ ⟨a+2, 0, 0, d, 0⟩) ⟨init_a, init_d⟩
intro ⟨a, d⟩; exists ⟨next_a, next_d⟩; apply transition_lemma

-- progress_nonhalt example (for mod-k or invariant cases)
apply progress_nonhalt (fm := fm)
  (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ e + 1 ∧ e ≥ 1)
```

## Phase Decomposition

Every transition decomposes into phases. The three building blocks:

**1. Register transfer (one rule repeated):**
```lean
theorem d_to_e : ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c, d, k⟩ := by
  have many_step : ∀ k d, ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c, d, k⟩ := by
    intro k; induction' k with k h <;> intro d
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (h _); ring_nf; finish
  exact many_step k d
```

**2. Interleaved chain (2-3 rules alternating):**
```lean
-- 3-step rounds (e.g., R3,R2,R2)
theorem r3r2r2_chain : ∀ k, ∀ c d e, ⟨0, 0, c+k, d, e⟩ [fm]⊢* ⟨0, 0, c, d+3*k, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish
```

**3. Strong induction (for non-uniform phases):**
```lean
theorem complex_phase : ∀ D, ∀ A B, ⟨A, B+1, 0, D, 0⟩ [fm]⊢* ⟨...⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro A B
  rcases D with _ | _ | D'
  · -- D=0 base case
  · -- D=1 base case
  · -- D'+2: take steps, apply ih D' (by omega)
```

Key rule: **universally quantify ALL free variables** inside the induction.

## Essential Tactics

| Tactic | Purpose |
|--------|---------|
| `step fm` | Apply one FM step symbolically |
| `finish` | Close `⊢*` goal with zero steps (`exists 0`) |
| `execute fm n` | Apply n steps then finish |
| `ring_nf` | Normalize arithmetic expressions |
| `omega` | Solve linear arithmetic/inequalities |
| `ring_nf; finish` | The universal closer after `stepStar_trans` |

**Composition:** `stepStar_trans` (⊢* + ⊢* = ⊢*), `stepStar_stepPlus_stepPlus` (⊢* + ⊢⁺ = ⊢⁺), `stepPlus_stepStar_stepPlus` (⊢⁺ + ⊢* = ⊢⁺)

## Common Pitfalls

1. **Rule priority**: Rules fire top-to-bottom in the match statement. Always simulate to check which rule fires in each state.
2. **ℕ subtraction is truncating**: Use `a + k` patterns, not `a - k`. Express `(a-1, ...)` as input `(a+1, ...)`.
3. **Quantify induction variables**: All free vars must be universally quantified inside `induction'`. This is the #1 source of proof failures.
4. **Parity splits**: Use `rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩`.
5. **Mod-k dispatch**: Use `interval_cases (e % 3)` after `have : e % 3 < 3 := Nat.mod_lt _ (by omega)`.
6. **Arithmetic rewrites**: After `step fm`, use `rw [show expr1 = expr2 from by ring]` to massage expressions before the next step.

## FM Family Taxonomy

Based on all 132 completed proofs, machines cluster into families:

| Family | Canonical Form | Typical Growth | Frequency |
|--------|---------------|----------------|-----------|
| A | `(a, 0, 0, 0, e)` | Quadratic/Superlinear | ~25% |
| B | `(0, 0, 0, d, e)` | Quadratic/Exponential | ~20% |
| C | `(0, 0, c, d, 0)` | Quadratic/Exponential | ~15% |
| D | `(n+1, 0, 0, 0, n)` or `(e+1, 0, 0, 0, e)` | Linear/Exponential | ~15% |
| E | `(d+1, 0, 0, d, 0)` or `(a, 0, 0, d, 0)` | Linear/Superlinear | ~15% |
| F | 6-register with accumulator (e.g., triangular numbers) | Quadratic | ~10% |

**Growth distribution**: ~40% quadratic, ~25% exponential/doubling, ~20% superlinear (mod-k dependent), ~15% linear.

**Typical phase structure**: Register transfer (1-2 chains) -> Opening steps (R5, R1) -> Interleaved chain (R1R1R2, R1R2, R3R2R2, etc.) -> Drain phase (R3R2R2, R2 chain, etc.). Parity or mod-k splits are needed in ~40% of proofs.

## Proof Template

```lean
import BBfLean.FM
import Mathlib.Tactic.Ring

namespace MyFM

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ... => ...
  | _ => none

-- Phase lemmas
theorem phase1 : ... := by ...
theorem phase2 : ... := by ...

-- Main transition (compose phases)
theorem main_trans : ⟨canonical_state⟩ [fm]⊢⁺ ⟨next_canonical⟩ := by
  apply stepStar_stepPlus_stepPlus phase1
  apply stepPlus_stepStar_stepPlus phase2 ...

-- Final theorem
theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨first_canonical⟩) (by execute fm N)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨x, y⟩ ↦ ⟨canonical_of x y⟩) ⟨init_x, init_y⟩
  intro ⟨x, y⟩; exists ⟨next_x, next_y⟩; apply main_trans
```
