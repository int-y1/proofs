import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #699: [35/6, 4/55, 121/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_699

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem middle_phase : ∀ B, ∀ C D F, ⟨0, B, C + 1, D, F + B + C + 1⟩ [fm]⊢* ⟨2 * C + B + 2, 0, 0, D + B, F⟩ := by
  intro B; induction' B using Nat.strongRecOn with B IH; intro C D F
  rcases B with _ | _ | B
  · rw [show F + 0 + C + 1 = F + (C + 1) from by ring,
        show 2 * C + 0 + 2 = 0 + 2 * (C + 1) from by ring,
        show D + 0 = D from by ring]
    exact r2_chain (C + 1) 0 D F
  · rw [show F + 1 + C + 1 = (F + C + 1) + 1 from by ring]
    step fm
    rw [show F + C + 1 = (F + C) + 1 from by ring]
    step fm; step fm
    rw [show 2 * C + 1 + 2 = 3 + 2 * C from by ring]
    exact r2_chain C 3 (D + 1) F
  · rw [show F + (B + 2) + C + 1 = (F + B + (C + 1) + 1) + 1 from by ring]
    step fm
    rw [show F + B + (C + 1) + 1 = (F + B + C + 1) + 1 from by ring]
    step fm; step fm
    rw [show F + B + C + 1 = F + B + (C + 1) from by ring]
    apply stepStar_trans (IH B (by omega) (C + 1) (D + 2) F)
    rw [show 2 * (C + 1) + B + 2 = 2 * C + (B + 2) + 2 from by ring,
        show D + 2 + B = D + (B + 2) from by ring]
    finish

theorem main_trans (n E : ℕ) :
    ⟨n + 2, 0, 0, n + 2, E⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, n + 3, E + n + 1⟩ := by
  have phase1 : ⟨n + 2, 0, 0, n + 2, E⟩ [fm]⊢* ⟨0, 0, 0, n + 2, E + 2 * (n + 2)⟩ := by
    have := r3_chain (n + 2) 0 (n + 2) E
    simp at this; exact this
  have phase2 : ⟨0, 0, 0, n + 2, E + 2 * (n + 2)⟩ [fm]⊢* ⟨0, n + 2, 0, 0, E + 2 * (n + 2)⟩ := by
    have := r4_chain (n + 2) 0 0 (E + 2 * (n + 2))
    simp at this; exact this
  have phase3 : ⟨0, n + 2, 0, 0, E + 2 * (n + 2)⟩ [fm]⊢⁺ ⟨1, n + 2, 0, 1, E + 2 * n + 3⟩ := by
    rw [show E + 2 * (n + 2) = (E + 2 * n + 3) + 1 from by ring]
    step fm; finish
  have phase4 : ⟨1, n + 2, 0, 1, E + 2 * n + 3⟩ [fm]⊢⁺ ⟨0, n + 1, 1, 2, E + 2 * n + 3⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show n + 2 = (n + 1) + 1 from by ring]
    step fm; finish
  have phase5 : ⟨0, n + 1, 1, 2, E + 2 * n + 3⟩ [fm]⊢* ⟨n + 3, 0, 0, n + 3, E + n + 1⟩ := by
    rw [show E + 2 * n + 3 = (E + n + 1) + (n + 1) + 0 + 1 from by ring]
    apply stepStar_trans (middle_phase (n + 1) 0 2 (E + n + 1))
    rw [show 2 * 0 + (n + 1) + 2 = n + 3 from by ring,
        show 2 + (n + 1) = n + 3 from by ring]
    finish
  exact stepStar_stepPlus_stepPlus phase1
    (stepStar_stepPlus_stepPlus phase2
      (stepPlus_trans phase3
        (stepPlus_stepStar_stepPlus phase4 phase5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 1⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, E⟩ ↦ ⟨n + 2, 0, 0, n + 2, E⟩) ⟨0, 1⟩
  intro ⟨n, E⟩; exact ⟨⟨n + 1, E + n + 1⟩, main_trans n E⟩

end Sz22_2003_unofficial_699
