import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #117: [77/15, 9/14, 2/3, 5/11, 231/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 1 -1  0  0  0
 0  0  1  0 -1
-1  1  0  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_117

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e+1⟩
  | _ => none

-- R4 repeated: e → c (when b=0, d=0)
theorem e_to_c : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e+k⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 repeated: b → a (when c=0, d=0)
theorem b_to_a : ∀ k, ∀ a b e, ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+k, b, 0, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a b e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2 repeated: a,d → b (when c=0)
theorem r2_drain : ∀ k, ∀ a b d e, ⟨a+k, b, 0, d+k, e⟩ [fm]⊢* ⟨a, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R1*2 + R2 round
theorem r1r1r2_round (A C D E : ℕ) : ⟨A+1, 2, C+2, D, E⟩ [fm]⊢⁺ ⟨A, 2, C, D+1, E+2⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, show C + 2 = (C + 1) + 1 from by ring]
  step fm
  step fm
  rw [show D + 1 + 1 = (D + 1) + 1 from by ring]
  step fm
  finish

-- R1*2 + R2 rounds by induction
theorem r1r1r2_rounds : ∀ k, ∀ A C D E, ⟨A+k, 2, C+2*k, D, E⟩ [fm]⊢* ⟨A, 2, C, D+k, E+2*k⟩ := by
  intro k; induction' k with k h <;> intro A C D E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring,
      show C + 2 * (k + 1) = (C + 2 * k) + 2 from by ring]
  apply stepStar_trans (stepPlus_stepStar (r1r1r2_round _ _ _ _))
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Main transition for even n: n = 2*m, m >= 1
-- (2*m+1, 0, 0, 0, 2*m) ⊢⁺ (2*m+2, 0, 0, 0, 2*m+1)
theorem main_trans_even (m : ℕ) : ⟨2*m+1, 0, 0, 0, 2*m⟩ [fm]⊢⁺ ⟨2*m+2, 0, 0, 0, 2*m+1⟩ := by
  -- Phase 1: R4 * 2m: e → c. (2m+1, 0, 2m, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2*m+1, 0, 2*m, 0, 0⟩)
  · have h := e_to_c (2*m) (2*m+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 step: (2m+1, 0, 2m, 0, 0) → (2m, 1, 2m, 1, 1)
  apply step_stepStar_stepPlus (c₂ := ⟨2*m, 1, 2*m, 1, 1⟩)
  · show fm ⟨(2*m) + 1, 0, 2*m, 0, 0⟩ = some ⟨2*m, 1, 2*m, 1, 1⟩; simp [fm]
  rcases m with _ | m
  · -- m = 0: state is (0, 1, 0, 1, 1)
    execute fm 4
  · -- m+1 >= 1: state is (2*(m+1), 1, 2*(m+1), 1, 1)
    -- R1: (2m+2, 0, 2m+1, 2, 2)
    apply stepStar_trans (c₂ := ⟨2*m+2, 0, 2*m+1, 2, 2⟩)
    · rw [show 2 * (m + 1) = (2 * m + 1) + 1 from by ring,
          show (1 : ℕ) = 0 + 1 from rfl]
      step fm; ring_nf; finish
    -- R2: (2m+1, 2, 2m+1, 1, 2)
    apply stepStar_trans (c₂ := ⟨2*m+1, 2, 2*m+1, 1, 2⟩)
    · rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring,
          show (2 : ℕ) = 0 + 1 + 1 from rfl]
      step fm; ring_nf; finish
    -- r1r1r2_rounds: m rounds. (2m+1, 2, 2m+1, 1, 2) → (m+1, 2, 1, m+1, 2m+2)
    apply stepStar_trans (c₂ := ⟨m+1, 2, 1, m+1, 2*m+2⟩)
    · have h := r1r1r2_rounds m (m+1) 1 1 2
      rw [show m + 1 + m = 2 * m + 1 from by ring,
          show 1 + 2 * m = 2 * m + 1 from by ring,
          show 1 + m = m + 1 from by ring,
          show 2 + 2 * m = 2 * m + 2 from by ring] at h
      exact h
    -- R1 (one more): (m+1, 2, 1, m+1, 2m+2) → (m+1, 1, 0, m+2, 2m+3)
    apply stepStar_trans (c₂ := ⟨m+1, 1, 0, m+2, 2*m+3⟩)
    · rw [show (2 : ℕ) = 1 + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
      step fm; ring_nf; finish
    -- R2 drain (m+1): (m+1, 1, 0, m+2, 2m+3) → (0, 2m+3, 0, 1, 2m+3)
    apply stepStar_trans (c₂ := ⟨0, 2*m+3, 0, 1, 2*m+3⟩)
    · have h := r2_drain (m+1) 0 1 1 (2*m+3)
      rw [show 0 + (m + 1) = m + 1 from by ring,
          show 1 + (m + 1) = m + 2 from by ring,
          show 1 + 2 * (m + 1) = 2 * m + 3 from by ring] at h
      exact h
    -- R3: (0, 2m+3, 0, 1, 2m+3) → (1, 2m+2, 0, 1, 2m+3)
    apply stepStar_trans (c₂ := ⟨1, 2*m+2, 0, 1, 2*m+3⟩)
    · rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
      step fm; ring_nf; finish
    -- R2: (1, 2m+2, 0, 1, 2m+3) → (0, 2m+4, 0, 0, 2m+3)
    apply stepStar_trans (c₂ := ⟨0, 2*m+4, 0, 0, 2*m+3⟩)
    · rw [show (1 : ℕ) = 0 + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
      step fm; ring_nf; finish
    -- b_to_a: (0, 2m+4, 0, 0, 2m+3) → (2m+4, 0, 0, 0, 2m+3)
    have h := b_to_a (2*m+4) 0 0 (2*m+3)
    simp only [Nat.zero_add] at h
    rw [show 2 * (m + 1) + 2 = 2 * m + 4 from by ring,
        show 2 * (m + 1) + 1 = 2 * m + 3 from by ring]
    exact h

-- Main transition for odd n: n = 2*m+1
-- (2*m+2, 0, 0, 0, 2*m+1) ⊢⁺ (2*m+3, 0, 0, 0, 2*m+2)
theorem main_trans_odd (m : ℕ) : ⟨2*m+2, 0, 0, 0, 2*m+1⟩ [fm]⊢⁺ ⟨2*m+3, 0, 0, 0, 2*m+2⟩ := by
  -- Phase 1: R4 * (2m+1): e → c. (2m+2, 0, 2m+1, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2*m+2, 0, 2*m+1, 0, 0⟩)
  · have h := e_to_c (2*m+1) (2*m+2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 step: (2m+2, 0, 2m+1, 0, 0) → (2m+1, 1, 2m+1, 1, 1)
  apply step_stepStar_stepPlus (c₂ := ⟨2*m+1, 1, 2*m+1, 1, 1⟩)
  · show fm ⟨(2*m+1) + 1, 0, 2*m+1, 0, 0⟩ = some ⟨2*m+1, 1, 2*m+1, 1, 1⟩; simp [fm]
  -- R1: (2m+1, 1, 2m+1, 1, 1) → (2m+1, 0, 2m, 2, 2)
  apply stepStar_trans (c₂ := ⟨2*m+1, 0, 2*m, 2, 2⟩)
  · rw [show 2 * m + 1 = (2 * m) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm; ring_nf; finish
  -- R2: (2m+1, 0, 2m, 2, 2) → (2m, 2, 2m, 1, 2)
  apply stepStar_trans (c₂ := ⟨2*m, 2, 2*m, 1, 2⟩)
  · rw [show 2 * m + 1 = (2 * m) + 1 from by ring,
        show (2 : ℕ) = 0 + 1 + 1 from rfl]
    step fm; ring_nf; finish
  -- r1r1r2_rounds: m rounds. (2m, 2, 2m, 1, 2) → (m, 2, 0, m+1, 2m+2)
  apply stepStar_trans (c₂ := ⟨m, 2, 0, m+1, 2*m+2⟩)
  · have h := r1r1r2_rounds m m 0 1 2
    rw [show m + m = 2 * m from by ring,
        show 0 + 2 * m = 2 * m from by ring,
        show 1 + m = m + 1 from by ring,
        show 2 + 2 * m = 2 * m + 2 from by ring] at h
    exact h
  -- R2 drain m: (m, 2, 0, m+1, 2m+2) → (0, 2m+2, 0, 1, 2m+2)
  apply stepStar_trans (c₂ := ⟨0, 2*m+2, 0, 1, 2*m+2⟩)
  · have h := r2_drain m 0 2 1 (2*m+2)
    rw [show 0 + m = m from by ring,
        show 1 + m = m + 1 from by ring,
        show 2 + 2 * m = 2 * m + 2 from by ring] at h
    exact h
  -- R3: (0, 2m+2, 0, 1, 2m+2) → (1, 2m+1, 0, 1, 2m+2)
  apply stepStar_trans (c₂ := ⟨1, 2*m+1, 0, 1, 2*m+2⟩)
  · rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
    step fm; ring_nf; finish
  -- R2: (1, 2m+1, 0, 1, 2m+2) → (0, 2m+3, 0, 0, 2m+2)
  apply stepStar_trans (c₂ := ⟨0, 2*m+3, 0, 0, 2*m+2⟩)
  · rw [show (1 : ℕ) = 0 + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
    step fm; ring_nf; finish
  -- b_to_a: (0, 2m+3, 0, 0, 2m+2) → (2m+3, 0, 0, 0, 2m+2)
  have h := b_to_a (2*m+3) 0 0 (2*m+2)
  rw [show 0 + (2 * m + 3) = 2 * m + 3 from by ring] at h
  exact h

-- Main transition combining even and odd
theorem main_trans (n : ℕ) : ⟨n+1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 0, n+1⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    exact main_trans_even m
  · subst hm
    exact main_trans_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, 0, 0, n⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩
