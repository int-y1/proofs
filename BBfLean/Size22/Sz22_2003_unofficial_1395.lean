import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1395: [7/15, 1/14, 27/77, 4/3, 385/2]

Vector representation:
```
 0 -1 -1  1  0
-1  0  0 -1  0
 0  3  0 -1 -1
 2 -1  0  0  0
-1  0  1  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1395

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e+1⟩
  | _ => none

theorem r5r2_chain : ∀ k, ⟨a + 1 + 2 * k, 0, c, 0, e⟩ [fm]⊢* ⟨a + 1, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show a + 1 + 2 * (k + 1) = (a + 1 + 2 * k) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a := a) (c := c + 1) (e := e + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨0, b, 0, d + k, k⟩ [fm]⊢* ⟨0, b + 3 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 3) (d := d))
    ring_nf; finish

theorem r3_3r1_chain : ∀ j, ⟨0, 0, c + 3 * j, d + 1, e + j⟩ [fm]⊢* ⟨0, 0, c, d + 2 * j + 1, e⟩ := by
  intro j; induction' j with j ih generalizing c d e
  · ring_nf; exists 0
  · rw [show c + 3 * (j + 1) = (c + 3 * j) + 3 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show d + 3 = (d + 2) + 1 from by ring]
    apply stepStar_trans (ih (c := c) (d := d + 2) (e := e))
    ring_nf; finish

theorem r4_chain : ∀ k, ⟨a, k, 0, 0, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

theorem phase_end : ⟨0, b + 1, 0, 1, 0⟩ [fm]⊢* ⟨2 * b + 1, 0, 0, 0, 0⟩ := by
  step fm; step fm
  show ⟨0 + 1, b, 0, 0, 0⟩ [fm]⊢* _
  apply stepStar_trans (r4_chain b (a := 0 + 1))
  ring_nf; finish

-- Phase A: (2*n+1, 0, 0, 0, 0) ⊢⁺ (0, 0, n+1, 1, n+1)
theorem phase_a : ⟨2 * n + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, n + 1, 1, n + 1⟩ := by
  rw [show 2 * n + 1 = 0 + 1 + 2 * n from by ring]
  apply stepStar_step_stepPlus (r5r2_chain n (a := 0) (c := 0) (e := 0))
  show (⟨0 + 1, 0, 0 + n, 0, 0 + n⟩ : Q) [fm]⊢ _
  simp [fm]

-- n = 3*m: (6*m+1, 0, 0, 0, 0) ⊢⁺ (12*m+3, 0, 0, 0, 0)
theorem trans_case0 : ⟨6 * m + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨12 * m + 3, 0, 0, 0, 0⟩ := by
  rw [show 6 * m + 1 = 2 * (3 * m) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phase_a (n := 3 * m))
  -- at (0, 0, 3*m+1, 1, 3*m+1)
  -- Phase B: rewrite to match r3_3r1_chain
  rw [show 3 * m + 1 = 1 + 3 * m from by ring]
  nth_rewrite 2 [show 1 + 3 * m = (2 * m + 1) + m from by ring]
  apply stepStar_trans (r3_3r1_chain m (c := 1) (d := 0) (e := 2 * m + 1))
  step fm; step fm
  rw [show 0 + 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (r3_chain (2 * m) (b := 2) (d := 1))
  -- Phase C
  rw [show 2 + 3 * (2 * m) = (6 * m + 1) + 1 from by ring]
  apply stepStar_trans (phase_end (b := 6 * m + 1))
  ring_nf; finish

-- n = 3*m+1: (6*m+3, 0, 0, 0, 0) ⊢⁺ (12*m+7, 0, 0, 0, 0)
theorem trans_case1 : ⟨6 * m + 3, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨12 * m + 7, 0, 0, 0, 0⟩ := by
  rw [show 6 * m + 3 = 2 * (3 * m + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phase_a (n := 3 * m + 1))
  rw [show 3 * m + 1 + 1 = 2 + 3 * m from by ring]
  nth_rewrite 2 [show 2 + 3 * m = (2 * m + 2) + m from by ring]
  apply stepStar_trans (r3_3r1_chain m (c := 2) (d := 0) (e := 2 * m + 2))
  step fm; step fm; step fm
  rw [show 0 + 2 * m + 1 + 1 = 1 + (2 * m + 1) from by ring]
  apply stepStar_trans (r3_chain (2 * m + 1) (b := 1) (d := 1))
  rw [show 1 + 3 * (2 * m + 1) = (6 * m + 3) + 1 from by ring]
  apply stepStar_trans (phase_end (b := 6 * m + 3))
  ring_nf; finish

-- n = 3*m+2: (6*m+5, 0, 0, 0, 0) ⊢⁺ (12*m+11, 0, 0, 0, 0)
theorem trans_case2 : ⟨6 * m + 5, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨12 * m + 11, 0, 0, 0, 0⟩ := by
  rw [show 6 * m + 5 = 2 * (3 * m + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phase_a (n := 3 * m + 2))
  rw [show 3 * m + 2 + 1 = 0 + 3 * (m + 1) from by ring]
  nth_rewrite 2 [show 0 + 3 * (m + 1) = (2 * m + 2) + (m + 1) from by ring]
  apply stepStar_trans (r3_3r1_chain (m + 1) (c := 0) (d := 0) (e := 2 * m + 2))
  rw [show 0 + 2 * (m + 1) + 1 = 1 + (2 * m + 2) from by ring]
  apply stepStar_trans (r3_chain (2 * m + 2) (b := 0) (d := 1))
  rw [show 0 + 3 * (2 * m + 2) = (6 * m + 5) + 1 from by ring]
  apply stepStar_trans (phase_end (b := 6 * m + 5))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 1, 0, 0, 0, 0⟩) 0
  intro n
  obtain ⟨m, rfl | rfl | rfl⟩ : ∃ m, n = 3 * m ∨ n = 3 * m + 1 ∨ n = 3 * m + 2 :=
    ⟨n / 3, by omega⟩
  · exists 6 * m + 1
    show ⟨2 * (3 * m) + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨2 * (6 * m + 1) + 1, 0, 0, 0, 0⟩
    rw [show 2 * (3 * m) + 1 = 6 * m + 1 from by ring,
        show 2 * (6 * m + 1) + 1 = 12 * m + 3 from by ring]
    exact trans_case0
  · exists 6 * m + 3
    show ⟨2 * (3 * m + 1) + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨2 * (6 * m + 3) + 1, 0, 0, 0, 0⟩
    rw [show 2 * (3 * m + 1) + 1 = 6 * m + 3 from by ring,
        show 2 * (6 * m + 3) + 1 = 12 * m + 7 from by ring]
    exact trans_case1
  · exists 6 * m + 5
    show ⟨2 * (3 * m + 2) + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨2 * (6 * m + 5) + 1, 0, 0, 0, 0⟩
    rw [show 2 * (3 * m + 2) + 1 = 6 * m + 5 from by ring,
        show 2 * (6 * m + 5) + 1 = 12 * m + 11 from by ring]
    exact trans_case2
