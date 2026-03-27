import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #162: [1/45, 49/3, 15/77, 2/7, 1089/2]

Vector representation:
```
 0 -2 -1  0  0
 0 -1  0  2  0
 0  1  1 -1 -1
 1  0  0 -1  0
-1  2  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_162

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+2⟩
  | _ => none

-- R3/R2 loop: each pair drains 1 from e, adds 1 to c and d
-- (a,0,c,d+1,e+k) ⊢* (a,0,c+k,d+k+1,e)
theorem r3r2_loop : ∀ k, ∀ a c d e,
    ⟨a, 0, c, d + 1, e + k⟩ [fm]⊢* ⟨a, 0, c + k, d + k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · simp; exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  show ⟨a, 0, c + 1, (d + 1) + 1, e + k⟩ [fm]⊢* ⟨a, 0, c + (k + 1), d + (k + 1) + 1, e⟩
  apply stepStar_trans (ih a (c + 1) (d + 1) e)
  ring_nf; finish

-- R4 loop: drains d into a
theorem r4_loop : ∀ k, ∀ a c d,
    ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a + k, 0, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (a + 1) c d)
  ring_nf; finish

-- R5/R1 loop: converts a,c into e
theorem r5r1_loop : ∀ k, ∀ a c e,
    ⟨a + k, 0, c + k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih a c (e + 2))
  ring_nf; finish

-- Main transition: (a,0,0,4,e) ⊢⁺ (a+3,0,0,4,2*e+2)
theorem main_trans : ∀ a e,
    ⟨a, 0, 0, 4, e⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 4, 2 * e + 2⟩ := by
  intro a e
  -- Phase 1 (stepStar): R3/R2 loop, e pairs
  -- (a, 0, 0, 3+1, 0+e) ⊢* (a, 0, e, e+4, 0)
  have h1 : ⟨a, 0, 0, 3 + 1, 0 + e⟩ [fm]⊢* ⟨a, 0, 0 + e, 3 + e + 1, 0⟩ :=
    r3r2_loop e a 0 3 0
  rw [show (0 : ℕ) + e = e from by ring, show 3 + e + 1 = e + 4 from by ring,
      show 3 + 1 = 4 from by ring] at h1
  -- One R4 step to get stepPlus
  have h2 : fm ⟨a, 0, e, (e + 3) + 1, 0⟩ = some ⟨a + 1, 0, e, e + 3, 0⟩ := by simp [fm]
  rw [show e + 4 = (e + 3) + 1 from by ring] at h1
  -- Remaining R4 steps (stepStar)
  have h3 : ⟨a + 1, 0, e, 0 + (e + 3), 0⟩ [fm]⊢* ⟨a + 1 + (e + 3), 0, e, 0, 0⟩ :=
    r4_loop (e + 3) (a + 1) e 0
  rw [show (0 : ℕ) + (e + 3) = e + 3 from by ring,
      show a + 1 + (e + 3) = a + e + 4 from by ring] at h3
  -- Phase 3 (stepStar): R5/R1 loop, e pairs
  have h4 : ⟨(a + 4) + e, 0, 0 + e, 0, 0⟩ [fm]⊢* ⟨a + 4, 0, 0, 0, 0 + 2 * e⟩ :=
    r5r1_loop e (a + 4) 0 0
  rw [show (a + 4) + e = a + e + 4 from by ring, show (0 : ℕ) + e = e from by ring,
      show (0 : ℕ) + 2 * e = 2 * e from by ring] at h4
  -- Phase 4 (stepStar): R5, R2, R2
  have h5 : ⟨(a + 3) + 1, 0, 0, 0, 2 * e⟩ [fm]⊢* ⟨a + 3, 0, 0, 4, 2 * e + 2⟩ := by
    step fm; step fm; step fm; finish
  rw [show (a + 3) + 1 = a + 4 from by ring] at h5
  -- Compose: h1 (star) + h2 (step) = stepPlus, then h3,h4,h5 (star) = stepPlus
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 2⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 4, e⟩)
  · intro q ⟨a, e, hq⟩
    subst hq
    exact ⟨⟨a + 3, 0, 0, 4, 2 * e + 2⟩, ⟨a + 3, 2 * e + 2, rfl⟩, main_trans a e⟩
  · exact ⟨0, 2, rfl⟩

end Sz22_2003_unofficial_162
