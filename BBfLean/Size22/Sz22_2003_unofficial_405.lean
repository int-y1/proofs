import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #405: [225/77, 1/6, 7/3, 2/35, 363/2]

Vector representation:
```
 0  2  2 -1 -1
-1 -1  0  0  0
 0 -1  0  1  0
 1  0 -1 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_405

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c+2, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- r5+r2 pair: (k+2, 0, c, 0, e) →* (k, 0, c, 0, e+2)
theorem r5r2_pair : ⟨k+2, 0, c, 0, e⟩ [fm]⊢* ⟨k, 0, c, 0, e+2⟩ := by
  rw [show k + 2 = (k + 1) + 1 from by ring]
  step fm; step fm; finish

-- Drain a via n r5+r2 pairs: (2*n+k, 0, c, 0, e) →* (k, 0, c, 0, e+2*n)
theorem drain_a : ∀ n, ∀ k e, ⟨2*n+k, 0, c, 0, e⟩ [fm]⊢* ⟨k, 0, c, 0, e+2*n⟩ := by
  intro n; induction n with
  | zero => intro k e; simp; exists 0
  | succ n ih =>
    intro k e
    rw [show 2 * (n + 1) + k = 2 * n + (k + 2) from by ring]
    apply stepStar_trans (ih (k+2) e)
    apply stepStar_trans r5r2_pair
    ring_nf; finish

-- r5 then r3: (1, 0, c, 0, e) →⁺ (0, 0, c, 1, e+2)
theorem r5_r3_final : ⟨1, 0, c, 0, e⟩ [fm]⊢⁺ ⟨0, 0, c, 1, e+2⟩ := by
  step fm; step fm; finish

-- Phase 1: (2*n+1, 0, c, 0, 0) →⁺ (0, 0, c, 1, 2*n+2)
theorem phase1 : ⟨2*n+1, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, c, 1, 2*n+2⟩ := by
  apply stepStar_stepPlus_stepPlus (drain_a n 1 0)
  rw [show (0 : ℕ) + 2 * n = 2 * n from by ring]
  apply stepPlus_stepStar_stepPlus r5_r3_final
  ring_nf; finish

-- Phase 2 loop: (0, b, c, 1, k+1) →* (0, b+k+2, c+2*(k+1), 0, 0)
-- Does k r1+r3 pairs then a final r1.
theorem phase2_loop : ∀ k, ∀ b c, ⟨0, b, c, 1, k+1⟩ [fm]⊢* ⟨0, b+k+2, c+2*(k+1), 0, 0⟩ := by
  intro k; induction k with
  | zero => intro b c; step fm; ring_nf; finish
  | succ k ih =>
    intro b c
    rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b+1) (c+2))
    ring_nf; finish

-- Phase 2: (0, 0, c, 1, 2*n+2) →* (0, 2*n+3, c+4*n+4, 0, 0)
theorem phase2 : ⟨0, 0, c, 1, 2*n+2⟩ [fm]⊢* ⟨0, 2*n+3, c+4*n+4, 0, 0⟩ := by
  rw [show 2*n+2 = (2*n+1) + 1 from by ring]
  apply stepStar_trans (phase2_loop (2*n+1) 0 c)
  ring_nf; finish

-- Drain b to d: (0, b+k, c, d, 0) →* (0, b, c, d+k, 0)
theorem b_to_d : ∀ k, ∀ b d, ⟨0, b+k, c, d, 0⟩ [fm]⊢* ⟨0, b, c, d+k, 0⟩ := by
  intro k; induction k with
  | zero => intro b d; exists 0
  | succ k ih =>
    intro b d
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b _)
    ring_nf; finish

-- Drain c,d to a: (a, 0, c+k, d+k, 0) →* (a+k, 0, c, d, 0)
theorem cd_to_a : ∀ k, ∀ a c d, ⟨a, 0, c+k, d+k, 0⟩ [fm]⊢* ⟨a+k, 0, c, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ c d)
    ring_nf; finish

-- Main cycle: (2*n+1, 0, n*n, 0, 0) →⁺ (2*(n+1)+1, 0, (n+1)*(n+1), 0, 0)
theorem cycle (n : ℕ) : ⟨2*n+1, 0, n*n, 0, 0⟩ [fm]⊢⁺ ⟨2*(n+1)+1, 0, (n+1)*(n+1), 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus phase1
  apply stepStar_trans phase2
  rw [show (2*n+3 : ℕ) = 0 + (2*n+3) from by ring]
  apply stepStar_trans (b_to_d (2*n+3) 0 0)
  rw [show (0 : ℕ) + (2*n+3) = 2*n+3 from by ring]
  have h := cd_to_a (2*n+3) 0 (n*n+2*n+1) 0
  simp only [show (n*n+2*n+1) + (2*n+3) = n*n+4*n+4 from by ring,
             show 0 + (2*n+3) = 2*n+3 from by ring] at h
  apply stepStar_trans h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (fun n => ⟨2*n+1, 0, n*n, 0, 0⟩) 0
  intro n
  exact ⟨n+1, cycle n⟩

end Sz22_2003_unofficial_405
