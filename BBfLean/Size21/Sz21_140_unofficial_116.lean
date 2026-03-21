import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #116: [77/15, 4/3, 9/14, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1
 2 -1  0  0  0
-1  2  0 -1  0
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_116

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- Phase 1: R4 repeated: e → c
theorem e_to_c : ∀ k c, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro c
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R3/R2/R2 chain: (a+k, 0, 0, k, e) →* (a+4*k, 0, 0, 0, e)
theorem r3r2r2_chain : ∀ k, ∀ a, ⟨a + k, 0, 0, k, e⟩ [fm]⊢* ⟨a + 4 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a
  · exists 0
  rw [show a + (k + 1) = a + k + 1 from by ring]
  step fm; step fm; step fm
  rw [show a + k + 2 + 2 = a + 4 + k from by ring]
  apply stepStar_trans (h (a + 4))
  ring_nf; finish

-- Inner loop even: (A+m, 2, 2*m, D, E) →* (A+4, 0, 0, D+m, E+2*m)
theorem inner_even : ∀ m, ∀ A D E, ⟨A + m, 2, 2 * m, D, E⟩ [fm]⊢* ⟨A + 4, 0, 0, D + m, E + 2 * m⟩ := by
  intro m; induction' m with m ih <;> intro A D E
  · execute fm 2
  rw [show A + (m + 1) = (A + m) + 1 from by ring,
      show 2 * (m + 1) = 2 * m + 2 from by ring]
  step fm; step fm
  rw [show A + m + 1 = (A + m) + 1 from by ring]
  step fm
  apply stepStar_trans (ih A (D + 1) (E + 2))
  ring_nf; finish

-- Inner loop odd: (A+m, 2, 2*m+1, D, E) →* (A+2, 0, 0, D+m+1, E+2*m+1)
theorem inner_odd : ∀ m, ∀ A D E, ⟨A + m, 2, 2 * m + 1, D, E⟩ [fm]⊢* ⟨A + 2, 0, 0, D + m + 1, E + 2 * m + 1⟩ := by
  intro m; induction' m with m ih <;> intro A D E
  · execute fm 2
  rw [show A + (m + 1) = (A + m) + 1 from by ring,
      show 2 * (m + 1) + 1 = 2 * m + 1 + 2 from by ring]
  step fm; step fm
  rw [show A + m + 1 = (A + m) + 1 from by ring]
  step fm
  apply stepStar_trans (ih A (D + 1) (E + 2))
  ring_nf; finish

-- Main transition: (a+e+2, 0, 0, 0, e+1) →⁺ (a+2*e+4, 0, 0, 0, e+2)
theorem main_trans : ⟨a + e + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨a + 2 * e + 4, 0, 0, 0, e + 2⟩ := by
  -- Phase 1: R4*(e+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a + e + 2, 0, e + 1, 0, 0⟩)
  · have h := e_to_c (a := a + e + 2) (e := 0) (e + 1) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 (1 step, giving stepPlus)
  apply step_stepStar_stepPlus (c₂ := ⟨a + e + 1, 1, e + 1, 0, 1⟩)
  · rw [show a + e + 2 = (a + e + 1) + 1 from by ring]
    show fm ⟨(a + e + 1) + 1, 0, e + 1, 0, 0⟩ = some ⟨a + e + 1, 1, e + 1, 0, 1⟩
    simp [fm]
  -- R1 step
  apply stepStar_trans (c₂ := ⟨a + e + 1, 0, e, 1, 2⟩)
  · have : fm ⟨a + e + 1, 0 + 1, e + 1, 0, 1⟩ = some ⟨a + e + 1, 0, e, 1, 2⟩ := by simp [fm]
    exact step_stepStar this
  -- R3 step
  apply stepStar_trans (c₂ := ⟨a + e, 2, e, 0, 2⟩)
  · rw [show a + e + 1 = (a + e) + 1 from by ring]
    have : fm ⟨(a + e) + 1, 0, e, 0 + 1, 2⟩ = some ⟨a + e, 2, e, 0, 2⟩ := by simp [fm]
    exact step_stepStar this
  -- Phase 3: parity split on e
  rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- Even e = 2*m
    rw [show m + m = 2 * m from by ring] at hm; subst hm
    apply stepStar_trans (c₂ := ⟨a + m + 4, 0, 0, m, 2 + 2 * m⟩)
    · have h := inner_even m (a + m) 0 2
      rw [show a + m + m = a + 2 * m from by ring,
          show 0 + m = m from by ring] at h; exact h
    have h := r3r2r2_chain (e := 2 + 2 * m) m (a + 4)
    rw [show a + 4 + m = a + m + 4 from by ring] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  · -- Odd e = 2*m + 1
    subst hm
    apply stepStar_trans (c₂ := ⟨a + m + 1 + 2, 0, 0, m + 1, 2 + 2 * m + 1⟩)
    · have h := inner_odd m (a + m + 1) 0 2
      rw [show a + m + 1 + m = a + (2 * m + 1) from by ring,
          show 0 + m + 1 = m + 1 from by ring] at h; exact h
    have h := r3r2r2_chain (e := 2 + 2 * m + 1) (m + 1) (a + 2)
    rw [show a + 2 + (m + 1) = a + m + 1 + 2 from by ring] at h
    refine stepStar_trans h ?_
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + e + 2, 0, 0, 0, e + 1⟩)
  · intro c ⟨a, e, hq⟩; subst hq
    exact ⟨⟨a + 2 * e + 4, 0, 0, 0, e + 2⟩, ⟨a + e + 1, e + 1, by ring_nf⟩, main_trans⟩
  · exact ⟨0, 0, rfl⟩
