import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #15: [14/15, 9/22, 125/2, 11/7, 3/5]

Vector representation:
```
 1 -1 -1  1  0
-1  2  0  0 -1
-1  0  3  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Canonical form: (0, 0, d+3, d, 0) with d → 2d+1 (exponential growth).

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_15

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: d → e
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 chain: a → c
theorem r3_chain : ∀ k, ∀ a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 3 * k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R1R1R2 chain
theorem r1r1r2_chain : ∀ k, ∀ X c D e,
    ⟨X, 2, c + 2 * k, D, e + k⟩ [fm]⊢* ⟨X + k, 2, c, D + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro X c D e
  · ring_nf; exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k + 1) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show (e + k) + 1 = (e + k) + 1 from rfl]
  step fm
  apply stepStar_trans (ih (X + 1) c (D + 2) e)
  ring_nf; finish

-- R2 drain
theorem r2_drain : ∀ k, ∀ a b D, ⟨a + k, b, 0, D, k⟩ [fm]⊢* ⟨a, b + 2 * k, 0, D, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b D
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R1 step helper
theorem r1_step (A B C D E : ℕ) :
    ⟨A, B+1, C+1, D, E⟩ [fm]⊢ ⟨A+1, B, C, D+1, E⟩ := by
  show fm ⟨A, B+1, C+1, D, E⟩ = some ⟨A+1, B, C, D+1, E⟩
  simp [fm]

-- R2 step helper
theorem r2_step (A C D E : ℕ) :
    ⟨A+1, 0, C, D, E+1⟩ [fm]⊢ ⟨A, 2, C, D, E⟩ := by
  show fm ⟨A+1, 0, C, D, E+1⟩ = some ⟨A, 2, C, D, E⟩
  simp [fm]

-- R3 step helper
theorem r3_step (A C D : ℕ) :
    ⟨A+1, 0, C, D, 0⟩ [fm]⊢ ⟨A, 0, C+3, D, 0⟩ := by
  show fm ⟨A+1, 0, C, D, 0⟩ = some ⟨A, 0, C+3, D, 0⟩
  simp [fm]

-- General tail
theorem gen_tail : ∀ b, ∀ A D,
    ⟨A + 1, b, 0, D, 0⟩ [fm]⊢* ⟨0, 0, 3 * A + 2 * b + 3, D + b, 0⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro A D
  rcases b with _ | _ | _ | b
  · have h := r3_chain (A + 1) 0 0 D
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  · apply stepStar_trans (c₂ := ⟨A + 1, 0, 2, D + 1, 0⟩)
    · have h1 : ⟨A + 1, 0 + 1, 0, D, 0⟩ [fm]⊢ ⟨A, 0 + 1, 3, D, 0⟩ := by
        show fm ⟨A + 1, 0 + 1, 0, D, 0⟩ = some ⟨A, 0 + 1, 3, D, 0⟩; simp [fm]
      rw [show (0 + 1 : ℕ) = 1 from rfl] at h1
      apply stepStar_trans (step_stepStar h1)
      exact step_stepStar (r1_step A 0 2 D 0)
    have h := r3_chain (A + 1) 0 2 (D + 1)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  · apply stepStar_trans (c₂ := ⟨A + 2, 0, 1, D + 2, 0⟩)
    · have h1 : ⟨A + 1, 1 + 1, 0, D, 0⟩ [fm]⊢ ⟨A, 1 + 1, 3, D, 0⟩ := by
        show fm ⟨A + 1, 1 + 1, 0, D, 0⟩ = some ⟨A, 1 + 1, 3, D, 0⟩; simp [fm]
      rw [show (1 + 1 : ℕ) = 2 from rfl] at h1
      apply stepStar_trans (step_stepStar h1)
      apply stepStar_trans (step_stepStar (r1_step A 1 2 D 0))
      exact step_stepStar (r1_step (A + 1) 0 1 (D + 1) 0)
    have h := r3_chain (A + 2) 0 1 (D + 2)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  · rw [show b + 1 + 1 + 1 = b + 3 from by ring]
    apply stepStar_trans (c₂ := ⟨A + 3, b, 0, D + 3, 0⟩)
    · apply stepStar_trans (c₂ := ⟨A, b + 3, 3, D, 0⟩)
      · have : ⟨A + 1, (b + 2) + 1, 0, D, 0⟩ [fm]⊢ ⟨A, (b + 2) + 1, 3, D, 0⟩ := by
          show fm ⟨A + 1, (b + 2) + 1, 0, D, 0⟩ = some ⟨A, (b + 2) + 1, 3, D, 0⟩; simp [fm]
        rw [show (b + 2) + 1 = b + 3 from by ring] at this
        exact step_stepStar this
      apply stepStar_trans (c₂ := ⟨A + 1, b + 2, 2, D + 1, 0⟩)
      · exact step_stepStar (r1_step A (b + 2) 2 D 0)
      apply stepStar_trans (c₂ := ⟨A + 2, b + 1, 1, D + 2, 0⟩)
      · exact step_stepStar (r1_step (A + 1) (b + 1) 1 (D + 1) 0)
      exact step_stepStar (r1_step (A + 2) b 0 (D + 2) 0)
    have h := ih b (by omega) (A + 2) (D + 3)
    rw [show A + 2 + 1 = A + 3 from by ring] at h
    refine stepStar_trans h ?_; ring_nf; finish

-- Rest of transition for odd d=2m+1
theorem rest_odd (m : ℕ) :
    ⟨0, 1, 2 * m + 3, 0, 2 * m + 1⟩ [fm]⊢* ⟨0, 0, 4 * m + 6, 4 * m + 3, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨0, 2, 2 * m + 2, 1, 2 * m⟩)
  · rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    apply stepStar_trans (step_stepStar (r1_step 0 0 (2 * m + 2) 0 (2 * m + 1)))
    rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
    exact step_stepStar (r2_step 0 (2 * m + 2) 1 (2 * m))
  -- R1R1R2 chain: m rounds
  apply stepStar_trans (c₂ := ⟨m, 2, 2, 2 * m + 1, m⟩)
  · have h := r1r1r2_chain m 0 2 1 m
    simp only [Nat.zero_add] at h
    rw [show 2 + 2 * m = 2 * m + 2 from by ring,
        show m + m = 2 * m from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨m + 2, 0, 0, 2 * m + 3, m⟩)
  · apply stepStar_trans (step_stepStar (r1_step m 1 1 (2 * m + 1) m))
    exact step_stepStar (r1_step (m + 1) 0 0 (2 * m + 2) m)
  -- R2 drain
  apply stepStar_trans (c₂ := ⟨2, 2 * m, 0, 2 * m + 3, 0⟩)
  · have h := r2_drain m 2 0 (2 * m + 3)
    simp only [Nat.zero_add] at h
    rw [show 2 + m = m + 2 from by ring] at h; exact h
  -- Tail
  have h := gen_tail (2 * m) 1 (2 * m + 3)
  rw [show (1 : ℕ) + 1 = 2 from by ring,
      show 3 * 1 + 2 * (2 * m) + 3 = 4 * m + 6 from by ring,
      show 2 * m + 3 + 2 * m = 4 * m + 3 from by ring] at h; exact h

-- Rest of transition for even d=2m+2
theorem rest_even (m : ℕ) :
    ⟨0, 1, 2 * m + 4, 0, 2 * m + 2⟩ [fm]⊢* ⟨0, 0, 4 * m + 8, 4 * m + 5, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨0, 2, 2 * m + 3, 1, 2 * m + 1⟩)
  · rw [show 2 * m + 4 = (2 * m + 3) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    apply stepStar_trans (step_stepStar (r1_step 0 0 (2 * m + 3) 0 (2 * m + 2)))
    rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
    exact step_stepStar (r2_step 0 (2 * m + 3) 1 (2 * m + 1))
  -- R1R1R2 chain: m rounds
  apply stepStar_trans (c₂ := ⟨m, 2, 3, 2 * m + 1, m + 1⟩)
  · have h := r1r1r2_chain m 0 3 1 (m + 1)
    simp only [Nat.zero_add] at h
    rw [show 3 + 2 * m = 2 * m + 3 from by ring,
        show m + 1 + m = 2 * m + 1 from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨m + 2, 0, 1, 2 * m + 3, m + 1⟩)
  · apply stepStar_trans (step_stepStar (r1_step m 1 2 (2 * m + 1) (m + 1)))
    exact step_stepStar (r1_step (m + 1) 0 1 (2 * m + 2) (m + 1))
  apply stepStar_trans (c₂ := ⟨m + 1, 2, 1, 2 * m + 3, m⟩)
  · rw [show m + 2 = (m + 1) + 1 from by ring, show m + 1 = m + 1 from rfl]
    exact step_stepStar (r2_step (m + 1) 1 (2 * m + 3) m)
  apply stepStar_trans (c₂ := ⟨m + 2, 1, 0, 2 * m + 4, m⟩)
  · exact step_stepStar (r1_step (m + 1) 1 0 (2 * m + 3) m)
  -- R2 drain
  apply stepStar_trans (c₂ := ⟨2, 2 * m + 1, 0, 2 * m + 4, 0⟩)
  · have h := r2_drain m 2 1 (2 * m + 4)
    rw [show 2 + m = m + 2 from by ring, show 1 + 2 * m = 2 * m + 1 from by ring] at h
    exact h
  -- Tail
  have h := gen_tail (2 * m + 1) 1 (2 * m + 4)
  rw [show (1 : ℕ) + 1 = 2 from by ring,
      show 3 * 1 + 2 * (2 * m + 1) + 3 = 4 * m + 8 from by ring,
      show 2 * m + 4 + (2 * m + 1) = 4 * m + 5 from by ring] at h; exact h

-- Main transition: (0, 0, d+3, d, 0) → (0, 0, 2*d+4, 2*d+1, 0)
theorem main_trans (d : ℕ) : ⟨0, 0, d + 3, d, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * d + 4, 2 * d + 1, 0⟩ := by
  rcases d with _ | d
  · execute fm 3
  · apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, d + 4, 0, d + 1⟩)
    · have h := r4_chain (d + 1) (d + 4) 0 0
      simp only [Nat.zero_add] at h; exact h
    apply step_stepStar_stepPlus (c₂ := ⟨0, 1, d + 3, 0, d + 1⟩)
    · show fm ⟨0, 0, (d + 3) + 1, 0, d + 1⟩ = some ⟨0, 1, d + 3, 0, d + 1⟩
      simp [fm]
    -- Parity split
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      have h := rest_odd m
      convert h using 2; ring_nf
    · subst hm
      have h := rest_even m
      convert h using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun d ↦ ⟨0, 0, d + 3, d, 0⟩) 0
  intro d
  exact ⟨2 * d + 1, main_trans d⟩
