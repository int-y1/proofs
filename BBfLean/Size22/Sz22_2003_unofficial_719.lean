import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #719: [35/6, 4/55, 1331/2, 3/7, 6/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  3
 0  1  0 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_719

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

theorem r2r1r1_chain : ∀ k, ∀ b c d e, ⟨0, b + 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, b, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 3))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- Even: (0, 2m, 0, 0, 4m²+6m+3) ⊢⁺ (0, 2m+1, 0, 0, 4m²+10m+7)
theorem main_even (m : ℕ) :
    ⟨0, 2 * m, 0, 0, 4 * m ^ 2 + 6 * m + 3⟩ [fm]⊢⁺ ⟨0, 2 * m + 1, 0, 0, 4 * m ^ 2 + 10 * m + 7⟩ := by
  -- R5 step
  rw [show 4 * m ^ 2 + 6 * m + 3 = (4 * m ^ 2 + 6 * m + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * m, 0, 0, (4 * m ^ 2 + 6 * m + 2) + 1⟩ = some ⟨1, 2 * m + 1, 0, 0, 4 * m ^ 2 + 6 * m + 2⟩
    simp [fm]
  -- R1 step
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm
  -- Rewrite for r2r1r1_chain
  rw [show 2 * m = 0 + 2 * m from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show 4 * m ^ 2 + 6 * m + 2 = (4 * m ^ 2 + 5 * m + 2) + m from by ring]
  apply stepStar_trans (r2r1r1_chain m 0 0 1 (4 * m ^ 2 + 5 * m + 2))
  -- After chain: (0, 0, m+1, 2m+1, 4m²+5m+2)
  -- Rewrite for r2_chain
  rw [show 0 + m + 1 = 0 + (m + 1) from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring,
      show 4 * m ^ 2 + 5 * m + 2 = (4 * m ^ 2 + 4 * m + 1) + (m + 1) from by ring]
  apply stepStar_trans (r2_chain (m + 1) 0 0 (2 * m + 1) (4 * m ^ 2 + 4 * m + 1))
  -- After chain: (2m+2, 0, 0, 2m+1, 4m²+4m+1)
  -- Rewrite for r3_chain
  rw [show 0 + 2 * (m + 1) = 0 + (2 * m + 2) from by ring]
  apply stepStar_trans (r3_chain (2 * m + 2) 0 (2 * m + 1) (4 * m ^ 2 + 4 * m + 1))
  -- After chain: (0, 0, 0, 2m+1, 4m²+4m+1+3(2m+2)) = (0, 0, 0, 2m+1, 4m²+10m+7)
  -- Rewrite for r4_chain
  rw [show 4 * m ^ 2 + 4 * m + 1 + 3 * (2 * m + 2) = 4 * m ^ 2 + 10 * m + 7 from by ring,
      show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  exact r4_chain (2 * m + 1) 0 0 (4 * m ^ 2 + 10 * m + 7)

-- Odd: (0, 2m+1, 0, 0, 4m²+10m+7) ⊢⁺ (0, 2m+2, 0, 0, 4m²+14m+13)
theorem main_odd (m : ℕ) :
    ⟨0, 2 * m + 1, 0, 0, 4 * m ^ 2 + 10 * m + 7⟩ [fm]⊢⁺ ⟨0, 2 * m + 2, 0, 0, 4 * m ^ 2 + 14 * m + 13⟩ := by
  -- R5 step
  rw [show 4 * m ^ 2 + 10 * m + 7 = (4 * m ^ 2 + 10 * m + 6) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * m + 1, 0, 0, (4 * m ^ 2 + 10 * m + 6) + 1⟩ = some ⟨1, 2 * m + 2, 0, 0, 4 * m ^ 2 + 10 * m + 6⟩
    simp [fm]
  -- R1 step
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm
  -- Rewrite for r2r1r1_chain
  rw [show 2 * m + 1 = 1 + 2 * m from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show 4 * m ^ 2 + 10 * m + 6 = (4 * m ^ 2 + 9 * m + 6) + m from by ring]
  apply stepStar_trans (r2r1r1_chain m 1 0 1 (4 * m ^ 2 + 9 * m + 6))
  -- After chain: (0, 1, m+1, 2m+1, 4m²+9m+6)
  -- R2 step + R1 step
  rw [show 0 + m + 1 = (m) + 1 from by ring,
      show 1 + 2 * m = (2 * m) + 1 from by ring,
      show 4 * m ^ 2 + 9 * m + 6 = (4 * m ^ 2 + 9 * m + 5) + 1 from by ring]
  step fm; step fm
  -- After: (1, 0, m+1, 2m+2, 4m²+9m+5)
  -- Rewrite for r2_chain
  rw [show m + 1 = 0 + (m + 1) from by ring,
      show 4 * m ^ 2 + 9 * m + 5 = (4 * m ^ 2 + 8 * m + 4) + (m + 1) from by ring,
      show 2 * m + 1 + 1 = 2 * m + 2 from by ring]
  apply stepStar_trans (r2_chain (m + 1) 1 0 (2 * m + 2) (4 * m ^ 2 + 8 * m + 4))
  -- After chain: (2m+3, 0, 0, 2m+2, 4m²+8m+4)
  -- Rewrite for r3_chain
  rw [show 1 + 2 * (m + 1) = 0 + (2 * m + 3) from by ring]
  apply stepStar_trans (r3_chain (2 * m + 3) 0 (2 * m + 2) (4 * m ^ 2 + 8 * m + 4))
  -- After chain: (0, 0, 0, 2m+2, 4m²+8m+4+3(2m+3)) = (0, 0, 0, 2m+2, 4m²+14m+13)
  -- Rewrite for r4_chain
  rw [show 4 * m ^ 2 + 8 * m + 4 + 3 * (2 * m + 3) = 4 * m ^ 2 + 14 * m + 13 from by ring,
      show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  exact r4_chain (2 * m + 2) 0 0 (4 * m ^ 2 + 14 * m + 13)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 13⟩) (by execute fm 17)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m, q = ⟨0, 2 * m, 0, 0, 4 * m ^ 2 + 6 * m + 3⟩ ∨
                        q = ⟨0, 2 * m + 1, 0, 0, 4 * m ^ 2 + 10 * m + 7⟩)
  · intro c ⟨m, hq⟩
    rcases hq with rfl | rfl
    · exact ⟨_, ⟨m, Or.inr rfl⟩, main_even m⟩
    · exact ⟨_, ⟨m + 1, Or.inl (by ring_nf)⟩, main_odd m⟩
  · exact ⟨1, Or.inl (by ring_nf)⟩

end Sz22_2003_unofficial_719
