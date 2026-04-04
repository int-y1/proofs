import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1715: [77/30, 4/21, 9/2, 5/11, 77/3]

Vector representation:
```
-1 -1 -1  1  1
 2 -1  0 -1  0
-1  2  0  0  0
 0  0  1  0 -1
 0 -1  0  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1715

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | _ => none

theorem r1r1r2_chain : ∀ m, ∀ B C D E,
    ⟨2, B + 3 * m, C + 2 * m, D, E⟩ [fm]⊢* ⟨2, B, C, D + m, E + 2 * m⟩ := by
  intro m; induction' m with m ih <;> intro B C D E
  · exists 0
  rw [show B + 3 * (m + 1) = (B + 3 * m + 2) + 1 from by ring,
      show C + 2 * (m + 1) = (C + 2 * m) + 1 + 1 from by ring]
  step fm
  rw [show C + 2 * m + 1 = (C + 2 * m) + 1 from by ring,
      show B + 3 * m + 2 = (B + 3 * m + 1) + 1 from by ring]
  step fm
  rw [show B + 3 * m + 1 = (B + 3 * m) + 1 from by ring,
      show D + 2 = (D + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (ih B C (D + 1) (E + 2))
  ring_nf; finish

theorem r2_drain : ∀ k, ∀ A D E,
    ⟨A, D + k, 0, D + k, E⟩ [fm]⊢* ⟨A + 2 * k, D, 0, D, E⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · exists 0
  rw [show D + (k + 1) = (D + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (A + 2) D E)
  ring_nf; finish

theorem r3_chain : ∀ k, ∀ A B E,
    ⟨A + k, B, 0, 0, E⟩ [fm]⊢* ⟨A, B + 2 * k, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A B E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih A (B + 2) E)
  ring_nf; finish

theorem r4_chain : ∀ k, ∀ B C,
    ⟨0, B, C, 0, k⟩ [fm]⊢* ⟨0, B, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro B C
  · exists 0
  step fm
  apply stepStar_trans (ih B (C + 1))
  ring_nf; finish

theorem main_trans_even (m : ℕ) :
    ⟨0, 4 * m + 4, 2 * m + 1, 0, 0⟩ [fm]⊢⁺ ⟨0, 4 * m + 6, 2 * m + 2, 0, 0⟩ := by
  rw [show 4 * m + 4 = (4 * m + 3) + 1 from by ring]
  step fm
  rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  apply stepStar_trans
  · rw [show 4 * m + 2 = (m + 2) + 3 * m from by ring,
        show 2 * m + 1 = 1 + 2 * m from by ring]
    exact r1r1r2_chain m (m + 2) 1 0 1
  rw [show 0 + m = m from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring]
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show m + 2 = (m + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  apply stepStar_trans
  · rw [show m + 1 = 0 + (m + 1) from by ring]
    exact r2_drain (m + 1) 1 0 (2 * m + 2)
  rw [show 1 + 2 * (m + 1) = 2 * m + 3 from by ring]
  apply stepStar_trans
  · rw [show 2 * m + 3 = 0 + (2 * m + 3) from by ring]
    exact r3_chain (2 * m + 3) 0 0 (2 * m + 2)
  rw [show 0 + 2 * (2 * m + 3) = 4 * m + 6 from by ring]
  have h := r4_chain (2 * m + 2) (4 * m + 6) 0
  rw [show (0 : ℕ) + (2 * m + 2) = 2 * m + 2 from by ring] at h
  exact h

theorem main_trans_odd (m : ℕ) :
    ⟨0, 4 * m + 6, 2 * m + 2, 0, 0⟩ [fm]⊢⁺ ⟨0, 4 * m + 8, 2 * m + 3, 0, 0⟩ := by
  rw [show 4 * m + 6 = (4 * m + 5) + 1 from by ring]
  step fm
  rw [show 4 * m + 5 = (4 * m + 4) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  apply stepStar_trans
  · rw [show 4 * m + 4 = (m + 1) + 3 * (m + 1) from by ring,
        show 2 * m + 2 = 0 + 2 * (m + 1) from by ring]
    exact r1r1r2_chain (m + 1) (m + 1) 0 0 1
  rw [show 0 + (m + 1) = m + 1 from by ring,
      show 1 + 2 * (m + 1) = 2 * m + 3 from by ring]
  apply stepStar_trans
  · rw [show m + 1 = 0 + (m + 1) from by ring]
    exact r2_drain (m + 1) 2 0 (2 * m + 3)
  rw [show 2 + 2 * (m + 1) = 2 * m + 4 from by ring]
  apply stepStar_trans
  · rw [show 2 * m + 4 = 0 + (2 * m + 4) from by ring]
    exact r3_chain (2 * m + 4) 0 0 (2 * m + 3)
  rw [show 0 + 2 * (2 * m + 4) = 4 * m + 8 from by ring]
  have h := r4_chain (2 * m + 3) (4 * m + 8) 0
  rw [show (0 : ℕ) + (2 * m + 3) = 2 * m + 3 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 4, 1, 0, 0⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m, q = ⟨0, 4 * m + 4, 2 * m + 1, 0, 0⟩ ∨
                        q = ⟨0, 4 * m + 6, 2 * m + 2, 0, 0⟩)
  · intro q ⟨m, hq⟩
    rcases hq with hq | hq
    · subst hq
      refine ⟨⟨0, 4 * m + 6, 2 * m + 2, 0, 0⟩, ⟨m, Or.inr rfl⟩, ?_⟩
      exact main_trans_even m
    · subst hq
      refine ⟨⟨0, 4 * m + 8, 2 * m + 3, 0, 0⟩, ⟨m + 1, Or.inl ?_⟩, ?_⟩
      · ring_nf
      · exact main_trans_odd m
  · exact ⟨0, Or.inl (by ring_nf)⟩

end Sz22_2003_unofficial_1715
