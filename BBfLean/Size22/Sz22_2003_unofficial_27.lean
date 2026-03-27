import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #27: [1/15, 196/3, 9/539, 5/7, 33/2]

Vector representation:
```
 0 -1 -1  0  0
 2 -1  0  2  0
 0  2  0 -2 -1
 0  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_27

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: transfer d to c
theorem d_to_c : ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  have many_step : ∀ k c, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
    intro k; induction' k with k h <;> intro c
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (h _); ring_nf; finish
  exact many_step k c

-- (R5, R1) repeated: consume a and c, produce e
theorem r5r1_chain : ⟨a + k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  have many_step : ∀ k a e, ⟨a + k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
    intro k; induction' k with k h <;> intro a e
    · exists 0
    rw [← Nat.add_assoc]; step fm; step fm
    apply stepStar_trans (h _ _); ring_nf; finish
  exact many_step k a e

-- R5 then R2: pivot from e-accumulation to d-building
theorem pivot_step : ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 2, e + 1⟩ := by
  step fm; step fm; finish

-- (R3, R2, R2) repeated: grow a and d while consuming e
theorem r3r2r2_chain : ⟨a, 0, 0, d + 2, e + k⟩ [fm]⊢* ⟨a + 4 * k, 0, 0, d + 2 + 2 * k, e⟩ := by
  have many_step : ∀ k a d e, ⟨a, 0, 0, d + 2, e + k⟩ [fm]⊢* ⟨a + 4 * k, 0, 0, d + 2 + 2 * k, e⟩ := by
    intro k; induction' k with k h <;> intro a d e
    · exists 0
    rw [show e + (k + 1) = e + k + 1 from by ring]
    rw [show d + 2 = d + 0 + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _); ring_nf; finish
  exact many_step k a d e

-- Compose phases into main transition
theorem phases_combined :
    ⟨m + d + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨m + 4 * d + 6, 0, 0, 2 * d + 4, 0⟩ := by
  -- Phase 1: R4 x d: transfer d to c
  have h1 : ⟨m + d + 1, 0, 0, d, 0⟩ [fm]⊢* ⟨m + d + 1, 0, d, 0, 0⟩ := by
    have := @d_to_c (m + d + 1) 0 0 d
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: (R5, R1) x d
  have h2 : ⟨m + d + 1, 0, d, 0, 0⟩ [fm]⊢* ⟨m + 1, 0, 0, 0, d⟩ := by
    rw [show m + d + 1 = (m + 1) + d from by ring]
    have := @r5r1_chain (m + 1) d 0
    simp only [Nat.zero_add] at this; exact this
  -- Phase 3: pivot
  have h3 : ⟨m + 1, 0, 0, 0, d⟩ [fm]⊢⁺ ⟨m + 2, 0, 0, 2, d + 1⟩ := by
    exact @pivot_step m d
  -- Phase 4: (R3, R2, R2) x (d+1)
  have h4 : ⟨m + 2, 0, 0, 2, d + 1⟩ [fm]⊢* ⟨m + 4 * d + 6, 0, 0, 2 * d + 4, 0⟩ := by
    have := @r3r2r2_chain (m + 2) 0 0 (d + 1)
    simp only [Nat.zero_add] at this
    rw [show m + 2 + 4 * (d + 1) = m + 4 * d + 6 from by ring] at this
    rw [show 0 + 2 + 2 * (d + 1) = 2 * d + 4 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus h3 h4))

-- Main transition: (a, 0, 0, d, 0) →⁺ (a + 3*d + 5, 0, 0, 2*d + 4, 0)
theorem main_trans (ha : a ≥ d + 1) :
    ⟨a, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 3 * d + 5, 0, 0, 2 * d + 4, 0⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, a = m + d + 1 := ⟨a - d - 1, by omega⟩
  have := @phases_combined m d
  rw [show m + 4 * d + 6 = m + d + 1 + 3 * d + 5 from by ring] at this
  exact this

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨6, 0, 0, 4, 0⟩)
  · execute fm 5
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ a ≥ d + 1)
  · intro c ⟨a, d, hq, ha⟩; subst hq
    exact ⟨⟨a + 3 * d + 5, 0, 0, 2 * d + 4, 0⟩,
           ⟨a + 3 * d + 5, 2 * d + 4, rfl, by omega⟩,
           main_trans ha⟩
  · exact ⟨6, 4, rfl, by omega⟩

end Sz22_2003_unofficial_27
