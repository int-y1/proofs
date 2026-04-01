# Tutorial: Proving Fractran Machines Don't Halt in Lean 4

Distilled from completing 132 sorry proofs in Size21 and 390 sorry proofs in Size22 (522 total, 99.7% first-attempt success rate). One machine (#1554) was discovered to actually halt.

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

**Important**: Some machines actually halt! If simulation shows the machine reaches a halting state, prove `halts fm c₀` instead of `¬halts fm c₀`. Machine #1554 halted after 21 canonical iterations with `c mod 11 = 1` triggering termination.

## Choosing the Framework Lemma

- **`progress_nonhalt_simple`** (~55%): When the next-state function is deterministic given parameters. Clean for linear, quadratic, exponential with explicit parameterization.
- **`progress_nonhalt`** (~45%): When transitions depend on modular arithmetic (parity, mod 3/4/5/7), invariant inequalities (e.g., `a >= e/2 + 1`), or alternating canonical families.

```lean
-- progress_nonhalt_simple example
apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
  (fun ⟨a, d⟩ ↦ ⟨a+2, 0, 0, d, 0⟩) ⟨init_a, init_d⟩
intro ⟨a, d⟩; exists ⟨next_a, next_d⟩; apply transition_lemma

-- progress_nonhalt example (for mod-k or invariant cases)
apply progress_nonhalt (fm := fm)
  (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ e + 1 ∧ e ≥ 1)
```

## Parameterization Tips

- **Absorb slack into parameters**: Instead of `(0, 0, 0, d, e)` with invariant `e >= d+2`, use `(0, 0, 0, d, F+d+2)` parameterized by `(d, F)` to eliminate the inequality entirely. This avoids `omega` failures in the invariant proof.
- **Use ℕ × ℕ or ℕ × ℕ × ℕ** when the recurrence has multiple growing quantities that aren't determined by a single parameter. E.g., `(d, e) -> (d+1, e+d+1)` needs two parameters.
- **Avoid division in canonical forms**: If `e` is always even, parameterize as `2*k` not `e/2`. If canonical states have `c = 3q+2`, use `q` as the parameter.
- **Offset parameters to avoid preconditions**: Use `(a+2, 0, 0, d+1, e+1)` instead of `(a, 0, 0, d, e)` with `a >= 2, d >= 1, e >= 1` — the offset encoding makes the invariant trivially true for all ℕ.
- **Two-step or three-step macros**: When canonical states alternate between two forms (e.g., even/odd b), compose two sub-transitions into a single macro-step that maps one canonical family to itself. This avoids needing a disjunctive predicate.

## Phase Decomposition

Every transition decomposes into phases. The four building blocks:

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

**4. Combined drain (strong induction on composite measure):**
When two registers drain interdependently (e.g., R2 fires when e >= 1, R3 fires when e = 0 but b >= 1), use strong induction on a composite measure like `a + 3*b` or `d + e`:
```lean
theorem drain : ∀ D, ∀ A B E, ⟨A+1, B, 0, D, E⟩ [fm]⊢* ⟨0, 0, 0, D+..., E+...⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro A B E
  rcases E with _ | E'
  · -- e=0: R3 fires (uses b), reducing b, then recurse with smaller D measure
  · -- e>=1: R2 fires, reducing both a and e
```

## Essential Tactics

| Tactic | Purpose |
|--------|---------|
| `step fm` | Apply one FM step symbolically |
| `finish` | Close `⊢*` goal with zero steps (`exists 0`) |
| `execute fm n` | Apply n steps then finish |
| `ring_nf` | Normalize arithmetic expressions |
| `omega` | Solve linear arithmetic/inequalities |
| `ring_nf; finish` | The universal closer after `stepStar_trans` |
| `simp [fm]` | When `step fm` fails on symbolic register values |

**Composition:** `stepStar_trans` (⊢* + ⊢* = ⊢*), `stepStar_stepPlus_stepPlus` (⊢* + ⊢⁺ = ⊢⁺), `stepPlus_stepStar_stepPlus` (⊢⁺ + ⊢* = ⊢⁺)

## Common Pitfalls

1. **Rule priority**: Rules fire top-to-bottom in the match statement. Always simulate to check which rule fires in each state.
2. **ℕ subtraction is truncating**: Use `a + k` patterns, not `a - k`. Express `(a-1, ...)` as input `(a+1, ...)`.
3. **Quantify induction variables**: All free vars must be universally quantified inside `induction'`. This is the #1 source of proof failures.
4. **Parity splits**: Use `rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩`.
5. **Mod-k dispatch**: Use `interval_cases (e % 3)` after `have : e % 3 < 3 := Nat.mod_lt _ (by omega)`.
6. **Arithmetic rewrites**: After `step fm`, use `rw [show expr1 = expr2 from by ring]` to massage expressions before the next step.
7. **`step fm` failures**: When registers are symbolic (e.g., `c` could be 0 or nonzero), `step fm` may fail because Lean can't determine which match branch fires. Use `simp [fm]` or prove the step explicitly via `step_stepStar` with a `by simp [fm]` witness.
8. **Large bootstrap counts**: Some machines need 30-180+ steps to reach the first canonical state. Don't be surprised — just use `execute fm N` with the right N.
9. **`match` reduction failures in `progress_nonhalt_simple`**: When the `exists` witness in the `nonhalt` theorem doesn't reduce through the `match` in the canonical form, use `refine ⟨⟨next_a, next_d⟩, ?_⟩` then `show` to rewrite the goal into the form matching `main_trans`, followed by `ring`-based rewrites.
10. **Don't assume non-halting**: Simulate first! Machine #1554 was discovered to actually halt. If the machine halts, prove `halts fm c₀` instead.

## FM Family Taxonomy

Based on all 522 completed proofs (132 Size21 + 390 Size22), machines cluster into families:

| Family | Canonical Form | Typical Growth | Frequency |
|--------|---------------|----------------|-----------|
| A | `(a, 0, 0, 0, e)` | Quadratic/Superlinear | ~25% |
| B | `(0, 0, 0, d, e)` | Quadratic/Exponential | ~18% |
| C | `(0, 0, c, 0, e)` or `(0, 0, c, d, 0)` | Quadratic/Exponential | ~14% |
| D | `(n+1, 0, 0, 0, n)` or `(e+1, 0, 0, 0, e)` | Linear/Exponential | ~12% |
| E | `(d+1, 0, 0, d, 0)` or `(a, 0, 0, d, 0)` | Linear/Superlinear | ~11% |
| F | 6-register with accumulator (triangular numbers, etc.) | Quadratic | ~8% |
| G | `(a, 0, c, 0, 0)` or `(a, b, 0, 0, 0)` | Superlinear/Exponential | ~7% |
| H | `(0, 0, 0, D)` (4-register) or `(0, 0, c, 0)` | Exponential | ~5% |

**Growth distribution**: ~35% quadratic, ~30% exponential/doubling, ~20% superlinear (mod-k dependent), ~15% linear.

**Typical phase structure**: Register transfer (1-2 chains) -> Opening steps (R5, R1) -> Interleaved chain (R1R1R2, R1R2, R3R2R2, R5R1R1, etc.) -> Drain phase (R3R2R2, R2 chain, R3R2 alternation, etc.). Parity or mod-k splits are needed in ~45% of proofs.

## Difficulty Spectrum

**Easy (~60%, < 60k tokens):** Deterministic recurrence, `progress_nonhalt_simple`, at most parity split. Common patterns: `d -> d+1`, `d -> 2d+1`, `(d,e) -> (d+1, e+d+1)`.

**Medium (~30%, 60-120k tokens):** Parity-dependent transitions, 2-3 case mod split, one non-trivial invariant inequality. Requires `progress_nonhalt`.

**Hard (~10%, > 120k tokens):** Mod-k dispatch with k >= 5 (especially mod 5, mod 7, mod 10, mod 11), nested invariants with non-obvious bounds, recursive sub-cycles, or interleaved drains where two registers compete (requiring strong induction on composite measures).

**Hardest patterns to watch for:**
- Mod-7+ dispatch (7+ separate transition lemmas needed)
- Machines where the drain phase depends on *which register runs out first* (a vs e, or b vs d)
- Coupled invariants like `a <= d+1 ∧ d+2 <= 2*a ∧ d >= 1`
- Machines requiring a two-step or three-step macro-transition (canonical -> intermediate -> ... -> next canonical)
- Alternating canonical families with 3+ forms (e.g., `b mod 3` cycles through 3 types)
- Machines with non-trivial halting conditions (e.g., #1554 halts when `c mod 11 = 1`)

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
