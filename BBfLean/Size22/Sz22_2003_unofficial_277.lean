import BBfLean.FM

/-!
# sz22_2003_unofficial #277: [14/15, 33/2, 1/3, 125/11, 1/35, 3/5]

Vector representation:
```
 1 -1 -1  1  0
-1  1  0  0  1
 0 -1  0  0  0
 0  0  3  0 -1
 0  0 -1 -1  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_277

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 2: Rule1+Rule2 loop. (0, 1, k, d, e) ->* (0, 1, 0, d+k, e+k) in 2k steps.
theorem r1r2_loop : ⟨0, 1, k, d, e⟩ [fm]⊢* ⟨0, 1, 0, d+k, e+k⟩ := by
  induction k generalizing d e with
  | zero => simp; exists 0
  | succ k ih =>
    step fm; step fm
    apply stepStar_trans (ih (d := d+1) (e := e+1))
    show ⟨0, 1, 0, d + 1 + k, e + 1 + k⟩ [fm]⊢* ⟨0, 1, 0, d + (k + 1), e + (k + 1)⟩
    have h1 : d + 1 + k = d + (k + 1) := by omega
    have h2 : e + 1 + k = e + (k + 1) := by omega
    rw [h1, h2]; exists 0

-- Phase 4: Rule4 loop. (0, 0, c, d, e) ->* (0, 0, c+3*e, d, 0)
theorem r4_loop : ⟨0, 0, c, d, e⟩ [fm]⊢* ⟨0, 0, c+3*e, d, 0⟩ := by
  induction e generalizing c with
  | zero => simp; exists 0
  | succ e ih =>
    step fm
    apply stepStar_trans (ih (c := c+3))
    show ⟨0, 0, c + 3 + 3 * e, d, 0⟩ [fm]⊢* ⟨0, 0, c + 3 * (e + 1), d, 0⟩
    have : c + 3 + 3 * e = c + 3 * (e + 1) := by omega
    rw [this]; exists 0

-- Phase 5: Rule5 loop. (0, 0, c+d, d, 0) ->* (0, 0, c, 0, 0) when c >= 1
theorem r5_loop : ⟨0, 0, c+d, d, 0⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  induction d generalizing c with
  | zero => simp; exists 0
  | succ d ih =>
    show ⟨0, 0, (c + d) + 1, d + 1, 0⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩
    step fm
    exact ih

-- Main cycle: (0, 0, n+2, 0, 0) ->+ (0, 0, 2*n+2, 0, 0)
theorem main_cycle (n : ℕ) : ⟨0, 0, n+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*n+2, 0, 0⟩ := by
  -- Phase 1: rule 6: (0,0,n+2,0,0) -> (0,1,n+1,0,0)
  apply step_stepStar_stepPlus (by (try unfold fm); rfl : (⟨0, 0, n+2, 0, 0⟩ : Q) [fm]⊢ ⟨0, 1, n+1, 0, 0⟩)
  -- Phase 2: r1r2 loop: (0,1,n+1,0,0) ->* (0,1,0,n+1,n+1)
  apply stepStar_trans (r1r2_loop (k := n+1) (d := 0) (e := 0))
  simp only [Nat.zero_add]
  -- Phase 3: rule 3: (0,1,0,n+1,n+1) -> (0,0,0,n+1,n+1)
  apply stepStar_trans (step_stepStar (by (try unfold fm); rfl : (⟨0, 1, 0, n+1, n+1⟩ : Q) [fm]⊢ ⟨0, 0, 0, n+1, n+1⟩))
  -- Phase 4: r4 loop: (0,0,0,n+1,n+1) ->* (0,0,3*(n+1),n+1,0)
  apply stepStar_trans (r4_loop (c := 0) (d := n+1) (e := n+1))
  simp only [Nat.zero_add]
  -- Phase 5: r5 loop: (0,0,3*(n+1),n+1,0) ->* (0,0,2*(n+1),0,0)
  have h : 3 * (n + 1) = 2 * (n + 1) + (n + 1) := by omega
  have h2 : 2 * n + 2 = 2 * (n + 1) := by omega
  rw [h, h2]
  exact r5_loop

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩)
  · execute fm 3
  · show ¬halts fm ⟨0, 0, 1 + 2, 0, 0⟩
    apply progress_nonhalt_simple (fm := fm) (A := ℕ) (C := fun n ↦ ⟨0, 0, n + 2, 0, 0⟩) (i₀ := 1)
    intro n
    exact ⟨2 * n, main_cycle n⟩
