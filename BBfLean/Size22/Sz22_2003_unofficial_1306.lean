import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1306: [63/10, 121/2, 4/33, 5/7, 21/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 2 -1  0  0 -1
 0  0  1 -1  0
 0  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1306

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem d_to_c : ∀ k c d, ⟨0, 0, c, d + k, (e : ℕ)⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

theorem r3r2r2_chain : ∀ k D e, ⟨0, k, 0, D, e + 1⟩ [fm]⊢* ⟨0, 0, 0, D, e + 3 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro D e
  · exists 0
  · step fm
    step fm
    step fm
    rw [show e + 2 + 2 = (e + 3) + 1 from by omega]
    apply stepStar_trans (ih D (e + 3))
    ring_nf; finish

theorem process : ∀ C, ∀ B D E, ⟨2, B, C, D, (E : ℕ) + C⟩ [fm]⊢* ⟨0, 0, 0, D + C, E + 3 * B + 5 * C + 4⟩ := by
  intro C
  induction C using Nat.strongRecOn with
  | _ C ih =>
  intro B D E
  match C with
  | 0 =>
    step fm
    step fm
    rw [show E + 0 + 2 + 2 = (E + 3) + 1 from by omega]
    apply stepStar_trans (r3r2r2_chain B D (E + 3))
    ring_nf; finish
  | 1 =>
    step fm
    step fm
    rw [show E + 1 + 2 = (E + 2) + 1 from by omega]
    apply stepStar_trans (r3r2r2_chain (B + 2) (D + 1) (E + 2))
    ring_nf; finish
  | (C : ℕ) + 2 =>
    rw [show E + (C + 2) = (E + C) + 2 from by ring]
    step fm
    step fm
    rw [show E + C + 2 = (E + C + 1) + 1 from by omega]
    step fm
    show ⟨2, B + 2 + 1, C, D + 1 + 1, E + C + 1⟩ [fm]⊢* _
    rw [show B + 2 + 1 = B + 3 from by omega,
        show D + 1 + 1 = D + 2 from by omega,
        show E + C + 1 = (E + 1) + C from by omega]
    apply stepStar_trans (ih C (by omega) (B + 3) (D + 2) (E + 1))
    ring_nf; finish

theorem main_transition (d E : ℕ) :
    ⟨0, 0, 0, d, E + d + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 1, E + 5 * d + 4⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, d, 0, E + d + 2⟩)
  · have := d_to_c d 0 0 (e := E + d + 2)
    simp only [Nat.zero_add] at this
    exact this
  · rw [show E + d + 2 = (E + d + 1) + 1 from by omega]
    step fm
    rw [show E + d + 1 = (E + d) + 1 from by omega]
    step fm
    show ⟨2, 0, d, 1, E + d⟩ [fm]⊢* ⟨0, 0, 0, d + 1, E + 5 * d + 4⟩
    apply stepStar_trans (process d 0 1 E)
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩)
  · execute fm 1
  · apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
      (fun ⟨d, E⟩ ↦ ⟨0, 0, 0, d, E + d + 2⟩) ⟨0, 0⟩
    intro ⟨d, E⟩
    refine ⟨⟨d + 1, E + 4 * d + 1⟩, ?_⟩
    simp only []
    rw [show E + 4 * d + 1 + (d + 1) + 2 = E + 5 * d + 4 from by omega]
    exact main_transition d E

end Sz22_2003_unofficial_1306
