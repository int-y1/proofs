import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1626: [77/15, 2366/3, 9/143, 5/7, 3/2]

Vector representation:
```
 0 -1 -1  1  1  0
 1 -1  0  1  0  2
 0  2  0  0 -1 -1
 0  0  1 -1  0  0
-1  1  0  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1626

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f+2⟩
  | ⟨a, b, c, d, e+1, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

-- Phase 1: R4 drain d to c
theorem r4_drain : ∀ k, ∀ a c f, ⟨a, 0, c, k, 0, f⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a c f
  · exists 0
  · rw [show c + (k + 1) = (c + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) f)
    ring_nf; finish

-- Phase 3: R3R1R1 chain (k rounds)
theorem r3r1r1_chain : ∀ k, ∀ a d e f,
    ⟨a, 0, 2 * k, d, e + 1, f + k + 1⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k + 1, f + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · simp; exists 0
  · rw [show 2 * (k + 1) = (2 * k) + 2 from by ring,
        show f + (k + 1) + 1 = (f + 1) + k + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 1 + 1 = d + 2 from by ring,
        show e + 1 + 1 = (e + 1) + 1 from by ring,
        show f + 1 + k = f + k + 1 from by ring]
    apply stepStar_trans (ih a (d + 2) (e + 1) f)
    ring_nf; finish

-- Phase 4: R3R2R2 chain (k+1 rounds)
theorem r3r2r2_chain : ∀ k, ∀ A D f,
    ⟨A, 0, 0, D, k + 1, f + 1⟩ [fm]⊢* ⟨A + 2 * (k + 1), 0, 0, D + 2 * (k + 1), 0, f + 3 * (k + 1) + 1⟩ := by
  intro k; induction' k with k ih <;> intro A D f
  · step fm; step fm; step fm; ring_nf; finish
  · step fm; step fm; step fm
    rw [show f + 4 = (f + 3) + 1 from by ring]
    apply stepStar_trans (ih (A + 2) (D + 2) (f + 3))
    ring_nf; finish

-- Combined: Phase 2 + 3 (R5, R1, then R3R1R1 chain)
theorem r5_r1_r3r1r1 (a m G : ℕ) :
    ⟨a + 1, 0, 2 * m + 1, 0, 0, m + G + 1⟩ [fm]⊢⁺ ⟨a, 0, 0, 2 * m + 1, m + 1, G + 1⟩ := by
  step fm
  step fm
  rw [show m + G + 1 = G + m + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain m a 1 0 G)
  rw [show 1 + 2 * m = 2 * m + 1 from by ring]; ring_nf; finish

-- Main transition
theorem main_trans (a m G : ℕ) :
    ⟨a + 1, 0, 0, 2 * m + 1, 0, m + G + 1⟩ [fm]⊢⁺
    ⟨a + 2 * m + 2, 0, 0, 4 * m + 3, 0, G + 3 * m + 4⟩ := by
  apply stepStar_stepPlus_stepPlus (r4_drain (2 * m + 1) (a + 1) 0 (m + G + 1))
  rw [show (0 : ℕ) + (2 * m + 1) = 2 * m + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (r5_r1_r3r1r1 a m G)
  have h4 := r3r2r2_chain m a (2 * m + 1) G
  rw [show a + 2 * (m + 1) = a + 2 * m + 2 from by ring,
      show 2 * m + 1 + 2 * (m + 1) = 4 * m + 3 from by ring,
      show G + 3 * (m + 1) + 1 = G + 3 * m + 4 from by ring] at h4
  exact h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0 + 1, 0, 0, 2 * 0 + 1, 0, 0 + 1 + 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨a, m, G⟩ ↦ ⟨a + 1, 0, 0, 2 * m + 1, 0, m + G + 1⟩) ⟨0, 0, 1⟩
  intro ⟨a, m, G⟩
  refine ⟨⟨a + 2 * m + 1, 2 * m + 1, G + m + 2⟩, ?_⟩
  show ⟨a + 1, 0, 0, 2 * m + 1, 0, m + G + 1⟩ [fm]⊢⁺
    ⟨(a + 2 * m + 1) + 1, 0, 0, 2 * (2 * m + 1) + 1, 0, (2 * m + 1) + (G + m + 2) + 1⟩
  rw [show (a + 2 * m + 1) + 1 = a + 2 * m + 2 from by ring,
      show 2 * (2 * m + 1) + 1 = 4 * m + 3 from by ring,
      show (2 * m + 1) + (G + m + 2) + 1 = G + 3 * m + 4 from by ring]
  exact main_trans a m G

end Sz22_2003_unofficial_1626
