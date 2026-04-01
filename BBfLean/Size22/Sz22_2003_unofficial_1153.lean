import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1153: [5/6, 44/35, 7/2, 3/11, 110/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  1  0
 0  1  0  0 -1
 1  0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1153

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e+1⟩
  | _ => none

-- R3/R2 pairs.
theorem r3r2_chain : ∀ c a e, ⟨a + 1, 0, c, 0, e⟩ [fm]⊢* ⟨a + c + 1, 0, 0, 0, e + c⟩ := by
  intro c; induction' c with c ih <;> intro a e
  · exists 0
  · step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- R3 drain.
theorem a_to_d : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1) e)
    ring_nf; finish

-- R4 drain.
theorem e_to_b : ∀ k b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- One round of R1,R1,R2.
theorem r1r1r2 : ⟨2, B + 2, C, D + 1, E⟩ [fm]⊢* ⟨2, B, C + 1, D, E + 1⟩ := by
  step fm; step fm; step fm; finish

-- k rounds of R1,R1,R2.
theorem r1r1r2_chain : ∀ k B C D E, ⟨2, B + 2 * k, C, D + k, E⟩ [fm]⊢* ⟨2, B, C + k, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro B C D E
  · exists 0
  · rw [show B + 2 * (k + 1) = (B + 2) + 2 * k from by ring,
        show D + (k + 1) = (D + 1) + k from by ring]
    apply stepStar_trans (ih (B + 2) C (D + 1) E)
    apply stepStar_trans r1r1r2
    ring_nf; finish

-- Interleaved chain with explicit n parameter for b and d.
-- After R1+R2 from (1, 2n+2, 1, n+1, 1), we get (2, 2n+1, 1, n, 2).
-- Then n rounds of R1,R1,R2, then final R1.
theorem interleaved_from : ∀ n, ⟨2, 2 * n + 1, 1, n, 2⟩ [fm]⊢* ⟨1, 0, n + 2, 0, n + 2⟩ := by
  intro n
  rw [show 2 * n + 1 = 1 + 2 * n from by ring]
  have h := r1r1r2_chain n 1 1 0 2
  rw [show 0 + n = n from by ring] at h
  apply stepStar_trans h
  step fm
  ring_nf; finish

-- Full cycle.
theorem main_trans : ∀ n, ⟨1, 0, n + 1, 0, n + 1⟩ [fm]⊢⁺ ⟨1, 0, n + 2, 0, n + 2⟩ := by
  intro n
  -- Phase 1: r3r2_chain
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r3r2_chain (n + 1) 0 (n + 1))
  -- Phase 2: a_to_d
  rw [show 0 + (n + 1) + 1 = n + 2 from by ring,
      show n + 1 + (n + 1) = 2 * n + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (a_to_d (n + 2) 0 (2 * n + 2))
  -- Phase 3: e_to_b
  rw [show 0 + (n + 2) = n + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * n + 2) 0 (n + 2))
  -- Phase 4: R5
  rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring,
      show n + 2 = (n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (by rfl : fm ⟨0, 2 * n + 2, 0, (n + 1) + 1, 0⟩ = some ⟨1, 2 * n + 2, 1, n + 1, 1⟩)
  -- Phase 5: R1, R2
  step fm
  step fm
  -- Phase 6: interleaved_from + final R1
  exact interleaved_from n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 1, 0, 1⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, n + 1, 0, n + 1⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1153
