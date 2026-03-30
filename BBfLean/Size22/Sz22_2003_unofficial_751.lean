import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #751: [35/6, 4/55, 847/2, 3/7, 10/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_751

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r4_chain : ∀ k b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem r3_chain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 2))
    ring_nf; finish

theorem r2r1r1_chain : ∀ k c d e, ⟨0, 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem phase_r5r1 (m g : ℕ) :
    ⟨0, 2 * m + 1, 0, 0, 2 * m + g + 3⟩ [fm]⊢⁺ ⟨0, 2 * m, 2, 1, 2 * m + g + 2⟩ := by
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring,
      show 2 * m + g + 3 = (2 * m + g + 2) + 1 from by ring]
  step fm; step fm; finish

theorem phase_rest (m g : ℕ) :
    ⟨0, 2 * m, 2, 1, 2 * m + g + 2⟩ [fm]⊢* ⟨0, 0, 0, 4 * m + 5, 4 * m + g + 8⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * m + g + 2 = (m + g + 2) + m from by ring]
  apply stepStar_trans (r2r1r1_chain m 1 1 (m + g + 2))
  rw [show 1 + m + 1 = m + 2 from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring,
      show m + g + 2 = g + (m + 2) from by ring]
  apply stepStar_trans (r2_chain (m + 2) 0 (2 * m + 1) g)
  rw [show 0 + 2 * (m + 2) = 0 + (2 * m + 4) from by ring]
  apply stepStar_trans (r3_chain (2 * m + 4) 0 (2 * m + 1) g)
  rw [show 2 * m + 1 + (2 * m + 4) = 4 * m + 5 from by ring,
      show g + 2 * (2 * m + 4) = 4 * m + g + 8 from by ring]
  finish

theorem main_trans (m g : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, 2 * m + g + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m + 5, 4 * m + g + 8⟩ := by
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * m + 1) 0 0 (2 * m + g + 3))
  rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phase_r5r1 m g)
  exact phase_rest m g

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 7⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, g⟩ ↦ ⟨0, 0, 0, 2 * m + 1, 2 * m + g + 3⟩) ⟨2, 0⟩
  intro ⟨m, g⟩
  refine ⟨⟨2 * m + 2, g + 1⟩, ?_⟩
  show (0, 0, 0, 2 * m + 1, 2 * m + g + 3) [fm]⊢⁺ (0, 0, 0, 2 * (2 * m + 2) + 1, 2 * (2 * m + 2) + (g + 1) + 3)
  rw [show 2 * (2 * m + 2) + 1 = 4 * m + 5 from by ring,
      show 2 * (2 * m + 2) + (g + 1) + 3 = 4 * m + g + 8 from by ring]
  exact main_trans m g

end Sz22_2003_unofficial_751
