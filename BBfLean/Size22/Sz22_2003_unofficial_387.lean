import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #387: [2/15, 99/14, 25/2, 7/11, 44/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 2  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_387

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | _ => none

-- R4 repeated: move e to d
theorem e_to_d : ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  have h : ∀ k d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
    intro k; induction k with
    | zero => intro d; exists 0
    | succ k ih =>
      intro d; step fm
      apply stepStar_trans (ih (d + 1))
      ring_nf; finish
  exact h k d

-- R3 repeated: convert a to c
theorem a_to_c : ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
  have h : ∀ k a c, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
    intro k; induction k with
    | zero => intro a c; exists 0
    | succ k ih =>
      intro a c
      rw [show a + (k + 1) = (a + k) + 1 from by ring]
      step fm
      apply stepStar_trans (ih a (c + 2))
      ring_nf; finish
  exact h k a c

-- One R2+R1+R1 iteration
theorem mid_step : ⟨a + 1, 0, c + 2, d + 1, e⟩ [fm]⊢* ⟨a + 2, 0, c, d, e + 1⟩ := by
  step fm; step fm; step fm
  ring_nf; finish

-- Middle loop: repeated R2+R1+R1
theorem mid_loop : ∀ k, ∀ a c e, ⟨a + 1, 0, c + 2 * k, k, e⟩ [fm]⊢* ⟨a + 1 + k, 0, c, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c e; simp; exists 0
  | succ k ih =>
    intro a c e
    show (⟨a + 1, 0, c + 2 * (k + 1), k + 1, e⟩ : Q) [fm]⊢* ⟨a + 1 + (k + 1), 0, c, 0, e + (k + 1)⟩
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    apply stepStar_trans (@mid_step a (c + 2 * k) k e)
    apply stepStar_trans (ih (a + 1) c (e + 1))
    ring_nf; finish

-- R5 step
theorem r5 : (⟨0, 0, c + 1, d, 0⟩ : Q) [fm]⊢ ⟨2, 0, c, d, 1⟩ := by
  show fm ⟨0, 0, c + 1, d, 0⟩ = some ⟨2, 0, c, d, 1⟩
  unfold fm; simp

-- The main cycle
theorem cycle (n : ℕ) : (⟨0, 0, 3 * n + 2, 0, n⟩ : Q) [fm]⊢⁺ ⟨0, 0, 3 * (n + 1) + 2, 0, n + 1⟩ := by
  -- Phase 1: e_to_d
  apply stepStar_stepPlus_stepPlus (@e_to_d (3 * n + 2) 0 n)
  simp only [Nat.zero_add]
  -- Phase 2: R5
  rw [show 3 * n + 2 = (3 * n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (@r5 (3 * n + 1) n)
  -- Goal: (2, 0, 3*n+1, n, 1) ⊢* (0, 0, 3*(n+1)+2, 0, n+1)
  -- Phase 3: mid_loop with a=1, c=n+1, k=n, e=1
  -- Need: (1+1, 0, (n+1)+2*n, n, 1) ⊢* (1+1+n, 0, n+1, 0, 1+n)
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show 3 * n + 1 = (n + 1) + 2 * n from by ring]
  apply stepStar_trans (mid_loop n 1 (n + 1) 1)
  -- Goal: (1+1+n, 0, n+1, 0, 1+n) ⊢* (0, 0, 3*(n+1)+2, 0, n+1)
  -- Phase 4: a_to_c
  rw [show 1 + 1 + n = 0 + (n + 2) from by ring,
      show 1 + n = n + 1 from by ring]
  apply stepStar_trans (a_to_c (a := 0) (k := n + 2) (c := n + 1) (e := n + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩)
  · execute fm 1
  · exact progress_nonhalt_simple (fm := fm) (fun n ↦ ⟨0, 0, 3 * n + 2, 0, n⟩) 0
      (fun n ↦ ⟨n + 1, cycle n⟩)

end Sz22_2003_unofficial_387
