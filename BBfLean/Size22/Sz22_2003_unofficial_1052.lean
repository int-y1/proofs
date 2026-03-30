import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1052: [5/18, 2/35, 3773/2, 3/7, 4/11]

Vector representation:
```
-1 -2  1  0  0
 1  0 -1 -1  0
-1  0  0  3  1
 0  1  0 -1  0
 2  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1052

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

theorem r5r1r1_chain : ∀ k, ∀ b c e,
    ⟨(0 : ℕ), b + 4 * k, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + 4 * (k + 1) = (b + 4 * k) + 4 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    step fm; step fm; step fm
    exact ih b (c + 2) e

theorem r4_chain : ∀ k, ∀ b e,
    ⟨(0 : ℕ), b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm
    exact ih (b + 1) e

theorem r3_chain_b0 : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    exact ih (d + 3) (e + 1)

theorem r3_chain_b1 : ∀ k, ∀ d e,
    ⟨k, (1 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 1, 0, d + 3 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    exact ih (d + 3) (e + 1)

theorem r2r3_chain_b0 : ∀ j, ∀ a e,
    ⟨a, (0 : ℕ), 3 * (j + 1), 3, e⟩ [fm]⊢* ⟨a + 2 * j + 3, 0, 0, 0, e + j⟩ := by
  intro j; induction' j with j ih <;> intro a e
  · rw [show 3 * (0 + 1) = 3 from by ring,
        show a + 2 * 0 + 3 = a + 3 from by ring,
        show e + 0 = e from by ring]
    step fm; step fm; step fm; finish
  · rw [show 3 * (j + 1 + 1) = 3 * (j + 1) + 3 from by ring,
        show a + 2 * (j + 1) + 3 = (a + 2) + 2 * j + 3 from by ring,
        show e + (j + 1) = (e + 1) + j from by ring]
    step fm; step fm; step fm; step fm
    exact ih (a + 2) (e + 1)

theorem r2r3_chain_b1 : ∀ j, ∀ a e,
    ⟨a, (1 : ℕ), 3 * j + 1, 3, e⟩ [fm]⊢* ⟨a + 2 * j + 1, 1, 0, 2, e + j⟩ := by
  intro j; induction' j with j ih <;> intro a e
  · rw [show 3 * 0 + 1 = 1 from by ring,
        show a + 2 * 0 + 1 = a + 1 from by ring,
        show e + 0 = e from by ring]
    step fm; finish
  · rw [show 3 * (j + 1) + 1 = (3 * j + 1) + 3 from by ring,
        show a + 2 * (j + 1) + 1 = (a + 2) + 2 * j + 1 from by ring,
        show e + (j + 1) = (e + 1) + j from by ring]
    step fm; step fm; step fm; step fm
    exact ih (a + 2) (e + 1)

-- Phase 2 for sub1: (0, 3, c, 0, f+1) →* (0, 1, c+1, 3, f+1)
-- R5: (0, 3, c, 0, f+1) -> (2, 3, c, 0, f)
-- R1: (2, 3, c, 0, f) -> (1, 1, c+1, 0, f)
-- R3: (1, 1, c+1, 0, f) -> (0, 1, c+1, 3, f+1)
theorem phase2_b3 : ∀ c f,
    ⟨(0 : ℕ), 3, c, 0, f + 1⟩ [fm]⊢* ⟨0, 1, c + 1, 3, f + 1⟩ := by
  intro c f; step fm; step fm; step fm; finish

-- Phase 2 for sub2: (0, 2, c, 0, f+1) →* (0, 0, c+1, 3, f+1)
-- R5: (0, 2, c, 0, f+1) -> (2, 2, c, 0, f)
-- R1: (2, 2, c, 0, f) -> (1, 0, c+1, 0, f)
-- R3: (1, 0, c+1, 0, f) -> (0, 0, c+1, 3, f+1)
theorem phase2_b2 : ∀ c f,
    ⟨(0 : ℕ), 2, c, 0, f + 1⟩ [fm]⊢* ⟨0, 0, c + 1, 3, f + 1⟩ := by
  intro c f; step fm; step fm; step fm; finish

-- Phase 2 for sub3: (0, 1, c, 0, f+1) →* (1, 1, c, 3, f+1)
-- R5: (0, 1, c, 0, f+1) -> (2, 1, c, 0, f)
-- R3: (2, 1, c, 0, f) -> (1, 1, c, 3, f+1)
theorem phase2_b1 : ∀ c f,
    ⟨(0 : ℕ), 1, c, 0, f + 1⟩ [fm]⊢* ⟨1, 1, c, 3, f + 1⟩ := by
  intro c f; step fm; step fm; finish

theorem sub1 (k f : ℕ) :
    ⟨(0 : ℕ), 3 + 12 * k, 0, 0, f + 3 * k + 1⟩ [fm]⊢⁺
    ⟨0, 6 + 12 * k, 0, 0, f + 6 * k + 2⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have := r5r1r1_chain (3 * k) 3 0 (f + 1)
    rw [show 3 + 4 * (3 * k) = 3 + 12 * k from by ring,
        show (f + 1) + 3 * k = f + 3 * k + 1 from by ring,
        show 0 + 2 * (3 * k) = 6 * k from by ring] at this
    exact this
  -- State: (0, 3, 6k, 0, f+1). Goal: ⊢⁺
  apply stepStar_stepPlus_stepPlus (phase2_b3 (6 * k) f)
  -- State: (0, 1, 6k+1, 3, f+1)
  rw [show 6 * k + 1 = 3 * (2 * k) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r2r3_chain_b1 (2 * k) 0 (f + 1))
  rw [show 0 + 2 * (2 * k) + 1 = 4 * k + 1 from by ring,
      show (f + 1) + 2 * k = f + 2 * k + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r3_chain_b1 (4 * k + 1) 2 (f + 2 * k + 1))
  rw [show 2 + 3 * (4 * k + 1) = 12 * k + 5 from by ring,
      show (f + 2 * k + 1) + (4 * k + 1) = f + 6 * k + 2 from by ring]
  -- Phase 5: R4 chain. Take one step to get ⊢⁺, then chain the rest.
  rw [show 12 * k + 5 = (12 * k + 4) + 1 from by ring]
  step fm
  show ⟨0, 2, 0, 12 * k + 4, f + 6 * k + 2⟩ [fm]⊢* ⟨0, 6 + 12 * k, 0, 0, f + 6 * k + 2⟩
  have := r4_chain (12 * k + 4) 2 (f + 6 * k + 2)
  rw [show 2 + (12 * k + 4) = 6 + 12 * k from by ring] at this
  exact this

theorem sub2 (k f : ℕ) :
    ⟨(0 : ℕ), 6 + 12 * k, 0, 0, f + 3 * k + 2⟩ [fm]⊢⁺
    ⟨0, 9 + 12 * k, 0, 0, f + 6 * k + 4⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have := r5r1r1_chain (3 * k + 1) 2 0 (f + 1)
    rw [show 2 + 4 * (3 * k + 1) = 6 + 12 * k from by ring,
        show (f + 1) + (3 * k + 1) = f + 3 * k + 2 from by ring,
        show 0 + 2 * (3 * k + 1) = 6 * k + 2 from by ring] at this
    exact this
  -- State: (0, 2, 6k+2, 0, f+1). Goal: ⊢⁺
  apply stepStar_stepPlus_stepPlus (phase2_b2 (6 * k + 2) f)
  -- State: (0, 0, 6k+3, 3, f+1)
  rw [show 6 * k + 2 + 1 = 3 * (2 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r2r3_chain_b0 (2 * k) 0 (f + 1))
  rw [show 0 + 2 * (2 * k) + 3 = 4 * k + 3 from by ring,
      show (f + 1) + 2 * k = f + 2 * k + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r3_chain_b0 (4 * k + 3) 0 (f + 2 * k + 1))
  rw [show 0 + 3 * (4 * k + 3) = 12 * k + 9 from by ring,
      show (f + 2 * k + 1) + (4 * k + 3) = f + 6 * k + 4 from by ring]
  rw [show 12 * k + 9 = (12 * k + 8) + 1 from by ring]
  step fm
  show ⟨0, 1, 0, 12 * k + 8, f + 6 * k + 4⟩ [fm]⊢* ⟨0, 9 + 12 * k, 0, 0, f + 6 * k + 4⟩
  have := r4_chain (12 * k + 8) 1 (f + 6 * k + 4)
  rw [show 1 + (12 * k + 8) = 9 + 12 * k from by ring] at this
  exact this

theorem sub3 (k f : ℕ) :
    ⟨(0 : ℕ), 9 + 12 * k, 0, 0, f + 3 * k + 3⟩ [fm]⊢⁺
    ⟨0, 15 + 12 * k, 0, 0, f + 6 * k + 6⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have := r5r1r1_chain (3 * k + 2) 1 0 (f + 1)
    rw [show 1 + 4 * (3 * k + 2) = 9 + 12 * k from by ring,
        show (f + 1) + (3 * k + 2) = f + 3 * k + 3 from by ring,
        show 0 + 2 * (3 * k + 2) = 6 * k + 4 from by ring] at this
    exact this
  -- State: (0, 1, 6k+4, 0, f+1). Goal: ⊢⁺
  apply stepStar_stepPlus_stepPlus (phase2_b1 (6 * k + 4) f)
  -- State: (1, 1, 6k+4, 3, f+1)
  rw [show 6 * k + 4 = 3 * (2 * k + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r2r3_chain_b1 (2 * k + 1) 1 (f + 1))
  rw [show 1 + 2 * (2 * k + 1) + 1 = 4 * k + 4 from by ring,
      show (f + 1) + (2 * k + 1) = f + 2 * k + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (r3_chain_b1 (4 * k + 4) 2 (f + 2 * k + 2))
  rw [show 2 + 3 * (4 * k + 4) = 12 * k + 14 from by ring,
      show (f + 2 * k + 2) + (4 * k + 4) = f + 6 * k + 6 from by ring]
  rw [show 12 * k + 14 = (12 * k + 13) + 1 from by ring]
  step fm
  show ⟨0, 2, 0, 12 * k + 13, f + 6 * k + 6⟩ [fm]⊢* ⟨0, 15 + 12 * k, 0, 0, f + 6 * k + 6⟩
  have := r4_chain (12 * k + 13) 2 (f + 6 * k + 6)
  rw [show 2 + (12 * k + 13) = 15 + 12 * k from by ring] at this
  exact this

theorem main_trans (k f : ℕ) :
    ⟨(0 : ℕ), 3 + 12 * k, 0, 0, f + 3 * k + 1⟩ [fm]⊢⁺
    ⟨0, 15 + 12 * k, 0, 0, f + 12 * k + 7⟩ := by
  have h1 := sub1 k f
  have h2 := sub2 k (f + 3 * k)
  have h3 := sub3 k (f + 6 * k + 1)
  rw [show f + 3 * k + 3 * k + 2 = f + 6 * k + 2 from by ring,
      show f + 3 * k + 6 * k + 4 = f + 9 * k + 4 from by ring] at h2
  rw [show f + 6 * k + 1 + 3 * k + 3 = f + 9 * k + 4 from by ring,
      show f + 6 * k + 1 + 6 * k + 6 = f + 12 * k + 7 from by ring] at h3
  exact stepPlus_trans (stepPlus_trans h1 h2) h3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 3, 0, 0, 1⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, f⟩ ↦ ⟨0, 3 + 12 * k, 0, 0, f + 3 * k + 1⟩) ⟨0, 0⟩
  intro ⟨k, f⟩
  refine ⟨⟨k + 1, f + 9 * k + 3⟩, ?_⟩
  show ⟨0, 3 + 12 * k, 0, 0, f + 3 * k + 1⟩ [fm]⊢⁺
    ⟨0, 3 + 12 * (k + 1), 0, 0, (f + 9 * k + 3) + 3 * (k + 1) + 1⟩
  rw [show 3 + 12 * (k + 1) = 15 + 12 * k from by ring,
      show (f + 9 * k + 3) + 3 * (k + 1) + 1 = f + 12 * k + 7 from by ring]
  exact main_trans k f

end Sz22_2003_unofficial_1052
