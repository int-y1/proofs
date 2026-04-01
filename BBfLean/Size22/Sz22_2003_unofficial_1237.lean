import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1237: [5/6, 7/2, 44/35, 3/11, 550/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  0
 2  0 -1 -1  1
 0  1  0  0 -1
 1  0  2 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1237

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e+1⟩
  | _ => none

-- R4 chain: move e to b
theorem e_to_b : ∀ k b d, ⟨(0 : ℕ), b, 0, d, k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih
  · intro b d; exists 0
  · intro b d
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- R3,R1,R1 chain: k rounds, each consuming 2 from b
theorem r3r1r1_chain : ∀ k, ∀ b c d e, ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro b c d e; exists 0
  · intro b c d e
    rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    rw [show c + k + 1 = (c + k) + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm
    step fm
    step fm
    rw [show c + k + 2 = c + (k + 1) + 1 from by ring,
        show e + k + 1 = e + (k + 1) from by ring]
    finish

-- R3,R2,R2 chain: k rounds, draining c
theorem r3r2r2_chain : ∀ k, ∀ c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih
  · intro c d e; exists 0
  · intro c d e
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) d e)
    rw [show d + k + 1 = (d + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + k + 2 = d + (k + 1) + 1 from by ring,
        show e + k + 1 = e + (k + 1) from by ring]
    finish

-- Transition for even k = 2m
theorem main_even (m : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, 4 * m + 3, 6 * m + 3⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 4 * m + 5, 6 * m + 6⟩ := by
  -- Phase 1: R4 chain, move e to b
  have h1 : ⟨(0 : ℕ), (0 : ℕ), 0, 4 * m + 3, 6 * m + 3⟩ [fm]⊢*
             ⟨(0 : ℕ), 6 * m + 3, 0, 4 * m + 3, 0⟩ := by
    have := e_to_b (6 * m + 3) 0 (4 * m + 3)
    simpa using this
  -- Phase 2: R5
  have h2 : ⟨(0 : ℕ), 6 * m + 3, 0, 4 * m + 3, 0⟩ [fm]⊢
             ⟨1, 6 * m + 3, 2, 4 * m + 2, 1⟩ := by
    rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring]; simp [fm]
  -- Phase 3: R1
  have h3 : ⟨1, 6 * m + 3, 2, 4 * m + 2, 1⟩ [fm]⊢
             ⟨0, 6 * m + 2, 3, 4 * m + 2, 1⟩ := by
    rw [show 6 * m + 3 = (6 * m + 2) + 1 from by ring]; simp [fm]
  -- Phase 4: R3,R1,R1 chain with 3m+1 rounds
  have h4 : ⟨(0 : ℕ), 6 * m + 2, 3, 4 * m + 2, 1⟩ [fm]⊢*
             ⟨(0 : ℕ), 0, 3 * m + 4, m + 1, 3 * m + 2⟩ := by
    rw [show 6 * m + 2 = 0 + 2 * (3 * m + 1) from by ring,
        show (3 : ℕ) = 2 + 1 from by ring,
        show 4 * m + 2 = (m + 1) + (3 * m + 1) from by ring]
    have := r3r1r1_chain (3 * m + 1) 0 2 (m + 1) 1
    rw [show 2 + (3 * m + 1) + 1 = 3 * m + 4 from by ring,
        show 1 + (3 * m + 1) = 3 * m + 2 from by ring] at this
    exact this
  -- Phase 5: R3,R2,R2 chain with 3m+4 rounds
  have h5 : ⟨(0 : ℕ), (0 : ℕ), 3 * m + 4, m + 1, 3 * m + 2⟩ [fm]⊢*
             ⟨(0 : ℕ), (0 : ℕ), 0, 4 * m + 5, 6 * m + 6⟩ := by
    rw [show 3 * m + 4 = 0 + (3 * m + 4) from by ring]
    have := r3r2r2_chain (3 * m + 4) 0 m (3 * m + 2)
    rw [show m + (3 * m + 4) + 1 = 4 * m + 5 from by ring,
        show 3 * m + 2 + (3 * m + 4) = 6 * m + 6 from by ring] at this
    exact this
  -- Compose
  apply stepStar_stepPlus_stepPlus h1
  apply step_stepStar_stepPlus h2
  apply stepStar_trans (step_stepStar h3)
  apply stepStar_trans h4
  exact h5

-- Transition for odd k = 2m+1
theorem main_odd (m : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, 4 * m + 5, 6 * m + 6⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 4 * m + 7, 6 * m + 9⟩ := by
  -- Phase 1: R4 chain, move e to b
  have h1 : ⟨(0 : ℕ), (0 : ℕ), 0, 4 * m + 5, 6 * m + 6⟩ [fm]⊢*
             ⟨(0 : ℕ), 6 * m + 6, 0, 4 * m + 5, 0⟩ := by
    have := e_to_b (6 * m + 6) 0 (4 * m + 5)
    simpa using this
  -- Phase 2: R5
  have h2 : ⟨(0 : ℕ), 6 * m + 6, 0, 4 * m + 5, 0⟩ [fm]⊢
             ⟨1, 6 * m + 6, 2, 4 * m + 4, 1⟩ := by
    rw [show 4 * m + 5 = (4 * m + 4) + 1 from by ring]; simp [fm]
  -- Phase 3: R1
  have h3 : ⟨1, 6 * m + 6, 2, 4 * m + 4, 1⟩ [fm]⊢
             ⟨0, 6 * m + 5, 3, 4 * m + 4, 1⟩ := by
    rw [show 6 * m + 6 = (6 * m + 5) + 1 from by ring]; simp [fm]
  -- Phase 4: R3,R1,R1 chain with 3m+2 rounds
  have h4 : ⟨(0 : ℕ), 6 * m + 5, 3, 4 * m + 4, 1⟩ [fm]⊢*
             ⟨(0 : ℕ), 1, 3 * m + 5, m + 2, 3 * m + 3⟩ := by
    rw [show 6 * m + 5 = 1 + 2 * (3 * m + 2) from by ring,
        show (3 : ℕ) = 2 + 1 from by ring,
        show 4 * m + 4 = (m + 2) + (3 * m + 2) from by ring]
    have := r3r1r1_chain (3 * m + 2) 1 2 (m + 2) 1
    rw [show 2 + (3 * m + 2) + 1 = 3 * m + 5 from by ring,
        show 1 + (3 * m + 2) = 3 * m + 3 from by ring] at this
    exact this
  -- Phase 5: b=1 drain via R3,R1,R2
  have h5 : ⟨(0 : ℕ), 1, 3 * m + 5, m + 2, 3 * m + 3⟩ [fm]⊢*
             ⟨(0 : ℕ), (0 : ℕ), 3 * m + 5, m + 2, 3 * m + 4⟩ := by
    rw [show 3 * m + 5 = (3 * m + 4) + 1 from by ring,
        show m + 2 = (m + 1) + 1 from by ring]
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨0, 1, (3 * m + 4) + 1, (m + 1) + 1, 3 * m + 3⟩ : Q) [fm]⊢
        ⟨2, 1, 3 * m + 4, m + 1, 3 * m + 4⟩))
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨2, 1, 3 * m + 4, m + 1, 3 * m + 4⟩ : Q) [fm]⊢
        ⟨1, 0, 3 * m + 5, m + 1, 3 * m + 4⟩))
    apply step_stepStar
    show (⟨1, 0, 3 * m + 5, m + 1, 3 * m + 4⟩ : Q) [fm]⊢
         ⟨0, 0, 3 * m + 5, m + 2, 3 * m + 4⟩
    simp [fm]
  -- Phase 6: R3,R2,R2 chain with 3m+5 rounds
  have h6 : ⟨(0 : ℕ), (0 : ℕ), 3 * m + 5, m + 2, 3 * m + 4⟩ [fm]⊢*
             ⟨(0 : ℕ), (0 : ℕ), 0, 4 * m + 7, 6 * m + 9⟩ := by
    rw [show 3 * m + 5 = 0 + (3 * m + 5) from by ring,
        show m + 2 = (m + 1) + 1 from by ring]
    have := r3r2r2_chain (3 * m + 5) 0 (m + 1) (3 * m + 4)
    rw [show m + 1 + (3 * m + 5) + 1 = 4 * m + 7 from by ring,
        show 3 * m + 4 + (3 * m + 5) = 6 * m + 9 from by ring] at this
    exact this
  -- Compose
  apply stepStar_stepPlus_stepPlus h1
  apply step_stepStar_stepPlus h2
  apply stepStar_trans (step_stepStar h3)
  apply stepStar_trans h4
  apply stepStar_trans h5
  exact h6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 3⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, 0, 2 * k + 3, 3 * k + 3⟩) 0
  intro k
  exists k + 1
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have h := main_even m
    rw [show 2 * (m + m) + 3 = 4 * m + 3 from by ring,
        show 3 * (m + m) + 3 = 6 * m + 3 from by ring,
        show 2 * (m + m + 1) + 3 = 4 * m + 5 from by ring,
        show 3 * (m + m + 1) + 3 = 6 * m + 6 from by ring]
    exact h
  · subst hm
    have h := main_odd m
    rw [show 2 * (2 * m + 1) + 3 = 4 * m + 5 from by ring,
        show 3 * (2 * m + 1) + 3 = 6 * m + 6 from by ring,
        show 2 * (2 * m + 1 + 1) + 3 = 4 * m + 7 from by ring,
        show 3 * (2 * m + 1 + 1) + 3 = 6 * m + 9 from by ring]
    exact h

end Sz22_2003_unofficial_1237
