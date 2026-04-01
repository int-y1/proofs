import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1195: [5/6, 49/2, 5324/35, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  3
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1195

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+3⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem e_to_b : ∀ k b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

theorem r3r1r1_chain : ∀ k b c d e,
    ⟨0, 2 * k + b, c + 1, d + k, e⟩ [fm]⊢* ⟨0, b, c + k + 1, d, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · simp; exists 0
  · rw [show 2 * (k + 1) + b = (2 * k + b) + 1 + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih b (c + 1) d (e + 3))
    ring_nf; finish

theorem r3r2r2_chain : ∀ k c d e,
    ⟨0, 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 3 * k + 1, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 + 1 + 1 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 3))
    ring_nf; finish

-- Combined transition: (0,0,0,g+m+2,2m) →⁺ (0,0,0,g+3m+4,6m+3)
theorem even_trans_core : ∀ m g,
    ⟨0, 0, 0, g + m + 2, 2 * m⟩ [fm]⊢⁺ ⟨0, 0, 0, g + 3 * m + 4, 6 * m + 3⟩ := by
  intro m g
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m) 0 (g + m + 2))
  show ⟨0, 0 + 2 * m, 0, g + m + 2, 0⟩ [fm]⊢⁺ _
  rw [show 0 + 2 * m = 2 * m from by ring,
      show g + m + 2 = (g + m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (show ⟨0, 2 * m, 0, (g + m + 1) + 1, 0⟩ [fm]⊢ ⟨0, 2 * m, 1, g + m + 1, 0⟩ from by simp [fm])
  show ⟨0, 2 * m, 1, g + m + 1, 0⟩ [fm]⊢* _
  rw [show (2 * m : ℕ) = 2 * m + 0 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show g + m + 1 = (g + 1) + m from by ring,
      show (0 : ℕ) = 0 from rfl]
  apply stepStar_trans (r3r1r1_chain m 0 0 (g + 1) 0)
  show ⟨0, 0, 0 + m + 1, g + 1, 0 + 3 * m⟩ [fm]⊢* _
  rw [show 0 + m + 1 = 0 + (m + 1) from by ring,
      show 0 + 3 * m = 3 * m from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 1) 0 g (3 * m))
  ring_nf; finish

-- Combined transition: (0,0,0,g+m+2,2m+1) →⁺ (0,0,0,g+3m+5,6m+6)
theorem odd_trans_core : ∀ m g,
    ⟨0, 0, 0, g + m + 2, 2 * m + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, g + 3 * m + 5, 6 * m + 6⟩ := by
  intro m g
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m + 1) 0 (g + m + 2))
  show ⟨0, 0 + (2 * m + 1), 0, g + m + 2, 0⟩ [fm]⊢⁺ _
  rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring,
      show g + m + 2 = (g + m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (show ⟨0, 2 * m + 1, 0, (g + m + 1) + 1, 0⟩ [fm]⊢ ⟨0, 2 * m + 1, 1, g + m + 1, 0⟩ from by simp [fm])
  show ⟨0, 2 * m + 1, 1, g + m + 1, 0⟩ [fm]⊢* _
  rw [show (2 * m + 1 : ℕ) = 2 * m + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from by ring,
      show g + m + 1 = (g + 1) + m from by ring,
      show (0 : ℕ) = 0 from rfl]
  apply stepStar_trans (r3r1r1_chain m 1 0 (g + 1) 0)
  -- (0, 1, m+1, g+1, 3m)
  show ⟨0, 1, 0 + m + 1, g + 1, 0 + 3 * m⟩ [fm]⊢* _
  rw [show 0 + m + 1 = m + 1 from by ring,
      show 0 + 3 * m = 3 * m from by ring,
      show g + 1 = g + 1 from rfl]
  -- Special round R3+R1+R2
  rw [show g + 1 = (g + 0) + 1 from by ring]
  step fm  -- R3
  step fm  -- R1
  step fm  -- R2
  -- (0, 0, m+1, g+0+2, 3m+3)
  show ⟨0, 0, m + 1, g + 0 + 2, 3 * m + 3⟩ [fm]⊢* _
  rw [show m + 1 = 0 + (m + 1) from by ring,
      show g + 0 + 2 = (g + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 1) 0 (g + 1) (3 * m + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 3⟩)
  · execute fm 5
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ 2 * D ≥ E + 4 ∧ E ≥ 3)
  · intro c ⟨D, E, hq, hD, hE⟩; subst hq
    rcases Nat.even_or_odd E with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      obtain ⟨g, rfl⟩ : ∃ g, D = g + m + 2 := ⟨D - m - 2, by omega⟩
      exact ⟨⟨0, 0, 0, g + 3 * m + 4, 6 * m + 3⟩,
        ⟨g + 3 * m + 4, 6 * m + 3, rfl, by omega, by omega⟩,
        even_trans_core m g⟩
    · rw [show 2 * m + 1 = 2 * m + 1 from rfl] at hm; subst hm
      obtain ⟨g, rfl⟩ : ∃ g, D = g + m + 2 := ⟨D - m - 2, by omega⟩
      exact ⟨⟨0, 0, 0, g + 3 * m + 5, 6 * m + 6⟩,
        ⟨g + 3 * m + 5, 6 * m + 6, rfl, by omega, by omega⟩,
        odd_trans_core m g⟩
  · exact ⟨4, 3, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1195
