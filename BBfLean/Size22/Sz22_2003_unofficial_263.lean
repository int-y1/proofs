import BBfLean.FM

/-!
# sz22_2003_unofficial #263: [14/15, 1/3, 66/7, 25/2, 1/55, 3/5]

Vector representation:
```
 1 -1 -1  1  0
 0 -1  0  0  0
 1  1  0 -1  1
-1  0  2  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_263

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Inner loop: (a, 1, k, 0, e) ->* (a + 2*k, 1, 0, 0, e + k)
theorem r1r3_loop (a e : ℕ) : ∀ k, ⟨a, 1, k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 1, 0, 0, e + k⟩ := by
  intro k; induction k generalizing a e with
  | zero => simp; finish
  | succ k ih =>
    step fm; step fm
    apply stepStar_trans (ih (a + 2) (e + 1))
    have h1 : a + 2 + 2 * k = a + 2 * (k + 1) := by omega
    have h2 : e + 1 + k = e + (k + 1) := by omega
    rw [h1, h2]; finish

-- Phase 2: (k, 0, c, 0, e) ->* (0, 0, c + 2*k, 0, e) via rule 4 repeated
theorem a_to_c (c e : ℕ) : ∀ k, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction k generalizing c with
  | zero => simp; finish
  | succ k ih =>
    step fm
    apply stepStar_trans (ih (c + 2))
    have h1 : c + 2 + 2 * k = c + 2 * (k + 1) := by omega
    rw [h1]; finish

-- Phase 3: (0, 0, c + k, 0, k) ->* (0, 0, c, 0, 0) via rule 5 repeated
theorem ce_cancel (c : ℕ) : ∀ k, ⟨0, 0, c + k, 0, k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro k; induction k generalizing c with
  | zero => simp; finish
  | succ k ih =>
    step fm
    exact ih c

-- Main cycle: (0, 0, C+3, 0, 0) ->+ (0, 0, 3*C+6, 0, 0)
theorem cycle (C : ℕ) : ⟨0, 0, C + 3, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * C + 6, 0, 0⟩ := by
  -- Step A: rule 6
  step fm
  -- Phase 1: r1r3_loop
  apply stepStar_trans (r1r3_loop 0 0 (C + 2))
  simp
  -- Step C: rule 2
  step fm
  -- Phase 2: a_to_c
  apply stepStar_trans (a_to_c 0 (C + 2) (2 * (C + 2)))
  simp
  -- Phase 3: ce_cancel
  have h : 2 * (2 * (C + 2)) = 3 * (C + 2) + (C + 2) := by omega
  rw [h]
  apply stepStar_trans (ce_cancel (3 * (C + 2)) (C + 2))
  have h2 : 3 * (C + 2) = 3 * C + 6 := by omega
  rw [h2]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩)
  · execute fm 8
  exact progress_nonhalt_simple (fun n => (⟨0, 0, n + 3, 0, 0⟩ : Q)) 0
    (fun i => ⟨3 * i + 3, by exact cycle i⟩)
