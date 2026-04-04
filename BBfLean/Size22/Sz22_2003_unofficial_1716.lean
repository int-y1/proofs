import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1716: [77/30, 9/2, 4/21, 5/11, 77/3]

Vector representation:
```
-1 -1 -1  1  1
-1  2  0  0  0
 2 -1  0 -1  0
 0  0  1  0 -1
 0 -1  0  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1716

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | _ => none

theorem r4_chain : ∀ k B C,
    ⟨0, B, C, 0, k⟩ [fm]⊢* ⟨0, B, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro B C
  · exists 0
  step fm
  apply stepStar_trans (ih B (C + 1))
  ring_nf; finish

theorem r1r1r3_chain : ∀ m B C D E,
    ⟨2, B + 3 * m, C + 2 * m, D, E⟩ [fm]⊢* ⟨2, B, C, D + m, E + 2 * m⟩ := by
  intro m; induction' m with m ih <;> intro B C D E
  · exists 0
  rw [show B + 3 * (m + 1) = (B + 3 * m + 2) + 1 from by ring,
      show C + 2 * (m + 1) = (C + 2 * m + 1) + 1 from by ring]
  step fm
  rw [show C + 2 * m + 1 = (C + 2 * m) + 1 from by ring,
      show B + 3 * m + 2 = (B + 3 * m + 1) + 1 from by ring]
  step fm
  rw [show B + 3 * m + 1 = (B + 3 * m) + 1 from by ring,
      show D + 2 = (D + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (ih B C (D + 1) (E + 2))
  ring_nf; finish

theorem r3r2r2_chain : ∀ k B D E,
    ⟨0, B + 1, 0, D + k, E⟩ [fm]⊢* ⟨0, B + 1 + 3 * k, 0, D, E⟩ := by
  intro k; induction' k with k ih <;> intro B D E
  · exists 0
  rw [show D + (k + 1) = (D + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (B + 3) D E)
  ring_nf; finish

theorem even_tail (m : ℕ) :
    ⟨2, m, 0, m, 2 * m + 1⟩ [fm]⊢* ⟨0, 4 * m + 4, 0, 0, 2 * m + 1⟩ := by
  step fm; step fm
  rw [show m + 1 + 1 + 2 = (m + 3) + 1 from by ring]
  have h := r3r2r2_chain m (m + 3) 0 (2 * m + 1)
  rw [show m + 3 + 1 + 3 * m = 4 * m + 4 from by ring,
      show 0 + m = m from by ring] at h
  exact h

theorem odd_tail (m : ℕ) :
    ⟨2, m + 2, 1, m, 2 * m + 1⟩ [fm]⊢* ⟨0, 4 * m + 6, 0, 0, 2 * m + 2⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show m + 2 = (m + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm; step fm
  rw [show m + 1 + 2 = (m + 2) + 1 from by ring,
      show 2 * m + 1 + 1 = 2 * m + 2 from by ring]
  apply stepStar_trans
  · rw [show m + 1 = 0 + (m + 1) from by ring]
    exact r3r2r2_chain (m + 1) (m + 2) 0 (2 * m + 2)
  ring_nf; finish

theorem main_trans_even (m : ℕ) :
    ⟨0, 4 * m + 2, 0, 0, 2 * m⟩ [fm]⊢⁺ ⟨0, 4 * m + 4, 0, 0, 2 * m + 1⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (2 * m) (4 * m + 2) 0
    rw [show 0 + 2 * m = 2 * m from by ring] at h; exact h
  rw [show 4 * m + 2 = (4 * m + 1) + 1 from by ring]
  step fm
  rw [show 4 * m + 1 = (4 * m) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  apply stepStar_trans
  · rw [show 4 * m = m + 3 * m from by ring,
        show 2 * m = 0 + 2 * m from by ring]
    exact r1r1r3_chain m m 0 0 1
  rw [show 0 + m = m from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring]
  exact even_tail m

theorem main_trans_odd (m : ℕ) :
    ⟨0, 4 * m + 4, 0, 0, 2 * m + 1⟩ [fm]⊢⁺ ⟨0, 4 * m + 6, 0, 0, 2 * m + 2⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (2 * m + 1) (4 * m + 4) 0
    rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring] at h; exact h
  rw [show 4 * m + 4 = (4 * m + 3) + 1 from by ring]
  step fm
  rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  apply stepStar_trans
  · rw [show 4 * m + 2 = (m + 2) + 3 * m from by ring,
        show 2 * m + 1 = 1 + 2 * m from by ring]
    exact r1r1r3_chain m (m + 2) 1 0 1
  rw [show 0 + m = m from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring]
  exact odd_tail m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m, q = ⟨0, 4 * m + 2, 0, 0, 2 * m⟩ ∨
                        q = ⟨0, 4 * m + 4, 0, 0, 2 * m + 1⟩)
  · intro q ⟨m, hq⟩
    rcases hq with hq | hq
    · subst hq
      refine ⟨⟨0, 4 * m + 4, 0, 0, 2 * m + 1⟩, ⟨m, Or.inr rfl⟩, ?_⟩
      exact main_trans_even m
    · subst hq
      refine ⟨⟨0, 4 * m + 6, 0, 0, 2 * m + 2⟩, ⟨m + 1, Or.inl ?_⟩, ?_⟩
      · ring_nf
      · exact main_trans_odd m
  · exact ⟨0, Or.inl (by ring_nf)⟩

end Sz22_2003_unofficial_1716
