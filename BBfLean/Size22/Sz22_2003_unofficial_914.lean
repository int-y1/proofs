import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #914: [4/15, 3/14, 55/2, 49/5, 75/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  1  0  1
 0  0 -1  2  0
 0  1  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude
-/

namespace Sz22_2003_unofficial_914

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+2, d, e⟩
  | _ => none

-- Phase 1: R3 chain - convert a to c and e
theorem r3_chain : ∀ k, ∀ a c e, ⟨a + k, (0 : ℕ), c, (0 : ℕ), e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · simp; exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    have h : ⟨(a + k) + 1, (0 : ℕ), c, (0 : ℕ), e⟩ [fm]⊢ ⟨a + k, 0, c + 1, 0, e + 1⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h)
    apply stepStar_trans (ih a (c + 1) (e + 1))
    rw [show c + 1 + k = c + (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]; exists 0

-- Phase 2: R4 chain - convert c to d (each c gives 2 d)
theorem r4_chain : ∀ k, ∀ c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d, e⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    have h : ⟨(0 : ℕ), (0 : ℕ), (c + k) + 1, d, e⟩ [fm]⊢ ⟨0, 0, c + k, d + 2, e⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h)
    apply stepStar_trans (ih c (d + 2) e)
    rw [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]; exists 0

-- Phase 1+2 combined: (a, 0, 0, 0, e) -> (0, 0, 0, 2a, e+a)
theorem phases12 (a e : ℕ) : ⟨a, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢* ⟨0, 0, 0, 2 * a, e + a⟩ := by
  have h1 := r3_chain a 0 0 e; simp at h1
  apply stepStar_trans h1
  have h2 := r4_chain a 0 0 (e + a); simp at h2; exact h2

-- Phase 3: One drain round from b=0
theorem round_b0 : ∀ d e, ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 4, e + 1⟩ [fm]⊢* ⟨0, 3, 0, d, e⟩ := by
  intro d e; execute fm 7

-- Phase 3: One drain round from b >= 1
theorem round_bge1 : ∀ b d e, ⟨(0 : ℕ), b + 1, (0 : ℕ), d + 4, e + 1⟩ [fm]⊢* ⟨0, b + 4, 0, d, e⟩ := by
  intro b d e
  have h1 : ⟨(0 : ℕ), b + 1, (0 : ℕ), d + 4, e + 1⟩ [fm]⊢ ⟨0, b + 2, 2, d + 4, e⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar h1)
  have h2 : ⟨(0 : ℕ), b + 2, (2 : ℕ), d + 4, e⟩ [fm]⊢ ⟨2, b + 1, 1, d + 4, e⟩ := by
    show ⟨0, (b + 1) + 1, 1 + 1, d + 4, e⟩ [fm]⊢ ⟨0 + 2, b + 1, 1, d + 4, e⟩; simp [fm]
  apply stepStar_trans (step_stepStar h2)
  have h3 : ⟨(2 : ℕ), b + 1, (1 : ℕ), d + 4, e⟩ [fm]⊢ ⟨4, b, 0, d + 4, e⟩ := by
    show ⟨2, b + 1, 0 + 1, d + 4, e⟩ [fm]⊢ ⟨2 + 2, b, 0, d + 4, e⟩; simp [fm]
  apply stepStar_trans (step_stepStar h3)
  have h4 : ⟨(4 : ℕ), b, (0 : ℕ), d + 4, e⟩ [fm]⊢* ⟨0, b + 4, 0, d, e⟩ := by execute fm 4
  exact h4

-- Phase 3: Combined drain rounds
theorem combined_rounds : ∀ K, ∀ d e,
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 4 * (K + 1), e + (K + 1)⟩ [fm]⊢* ⟨0, 3 * (K + 1), 0, d, e⟩ := by
  intro K; induction' K with K ih <;> intro d e
  · rw [show d + 4 * 1 = d + 4 from by ring, show e + 1 = e + 1 from rfl,
        show (3 : ℕ) * 1 = 3 from by ring]
    exact round_b0 d e
  · rw [show d + 4 * (K + 1 + 1) = (d + 4) + 4 * (K + 1) from by ring,
        show e + (K + 1 + 1) = (e + 1) + (K + 1) from by ring]
    apply stepStar_trans (ih (d + 4) (e + 1))
    show ⟨0, 3 * (K + 1), 0, d + 4, e + 1⟩ [fm]⊢* ⟨0, 3 * (K + 1 + 1), 0, d, e⟩
    rw [show (3 : ℕ) * (K + 1) = (3 * K + 3 - 1) + 1 from by omega]
    apply stepStar_trans (round_bge1 (b := 3 * K + 3 - 1) (d := d) (e := e))
    rw [show 3 * K + 3 - 1 + 4 = 3 * (K + 1 + 1) from by omega]; exists 0

-- Phase 4: buildup chain (R3/R1 alternating, converting b to a)
theorem buildup : ⟨a + 1, b + 1, (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢* ⟨a + 2, b, 0, 0, e + 1⟩ := by
  have h1 : ⟨a + 1, b + 1, (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢ ⟨a, b + 1, 1, 0, e + 1⟩ := by
    show ⟨a + 1, b + 1, 0, 0, e⟩ [fm]⊢ ⟨a, b + 1, 0 + 1, 0, e + 1⟩; simp [fm]
  apply stepStar_trans (step_stepStar h1)
  have h2 : ⟨a, b + 1, (1 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢ ⟨a + 2, b, 0, 0, e + 1⟩ := by
    show ⟨a, b + 1, 0 + 1, 0, e + 1⟩ [fm]⊢ ⟨a + 2, b, 0, 0, e + 1⟩; simp [fm]
  exact step_stepStar h2

theorem buildup_chain : ∀ k, ∀ a e, ⟨a + 1, k, (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · simp; exists 0
  · show ⟨a + 1, k + 1, 0, 0, e⟩ [fm]⊢* _
    apply stepStar_trans (buildup (a := a) (b := k) (e := e))
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (e + 1))
    rw [show a + 1 + 1 + k = a + 1 + (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]; exists 0

-- Endgame remainder 0: (0, b+3, 0, 0, e+1) -> (b+6, 0, 0, 0, e+b+2)
theorem endgame_r0 : ∀ b e, ⟨(0 : ℕ), b + 3, (0 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢* ⟨b + 6, 0, 0, 0, e + b + 2⟩ := by
  intro b e
  have h1 : ⟨(0 : ℕ), b + 3, (0 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢ ⟨0, b + 4, 2, 0, e⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar h1)
  have h2 : ⟨(0 : ℕ), b + 4, (2 : ℕ), (0 : ℕ), e⟩ [fm]⊢ ⟨2, b + 3, 1, 0, e⟩ := by
    show ⟨0, (b + 3) + 1, 1 + 1, 0, e⟩ [fm]⊢ ⟨0 + 2, b + 3, 1, 0, e⟩; simp [fm]
  apply stepStar_trans (step_stepStar h2)
  have h3 : ⟨(2 : ℕ), b + 3, (1 : ℕ), (0 : ℕ), e⟩ [fm]⊢ ⟨4, b + 2, 0, 0, e⟩ := by
    show ⟨2, (b + 2) + 1, 0 + 1, 0, e⟩ [fm]⊢ ⟨2 + 2, b + 2, 0, 0, e⟩; simp [fm]
  apply stepStar_trans (step_stepStar h3)
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (buildup_chain (b + 2) 3 e)
  rw [show 3 + 1 + (b + 2) = b + 6 from by ring,
      show e + (b + 2) = e + b + 2 from by ring]; exists 0

-- Endgame remainder 2: (0, b+3, 0, 2, e+1) -> (b+6, 0, 0, 0, e+b+4)
theorem endgame_r2 : ∀ b e, ⟨(0 : ℕ), b + 3, (0 : ℕ), (2 : ℕ), e + 1⟩ [fm]⊢* ⟨b + 6, 0, 0, 0, e + b + 4⟩ := by
  intro b e
  have h1 : ⟨(0 : ℕ), b + 3, (0 : ℕ), (2 : ℕ), e + 1⟩ [fm]⊢ ⟨0, b + 4, 2, 2, e⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar h1)
  have h2 : ⟨(0 : ℕ), b + 4, (2 : ℕ), (2 : ℕ), e⟩ [fm]⊢ ⟨2, b + 3, 1, 2, e⟩ := by
    show ⟨0, (b + 3) + 1, 1 + 1, 2, e⟩ [fm]⊢ ⟨0 + 2, b + 3, 1, 2, e⟩; simp [fm]
  apply stepStar_trans (step_stepStar h2)
  have h3 : ⟨(2 : ℕ), b + 3, (1 : ℕ), (2 : ℕ), e⟩ [fm]⊢ ⟨4, b + 2, 0, 2, e⟩ := by
    show ⟨2, (b + 2) + 1, 0 + 1, 2, e⟩ [fm]⊢ ⟨2 + 2, b + 2, 0, 2, e⟩; simp [fm]
  apply stepStar_trans (step_stepStar h3)
  have h4 : ⟨(4 : ℕ), b + 2, (0 : ℕ), (2 : ℕ), e⟩ [fm]⊢* ⟨2, b + 4, 0, 0, e⟩ := by
    show ⟨(3 : ℕ) + 1, b + 2, 0, 1 + 1, e⟩ [fm]⊢* ⟨2, b + 4, 0, 0, e⟩
    execute fm 2
  apply stepStar_trans h4
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (buildup_chain (b + 4) 1 e)
  rw [show 1 + 1 + (b + 4) = b + 6 from by ring,
      show e + (b + 4) = e + b + 4 from by ring]; exists 0

-- Phase 1+2: (A+1, 0, 0, 0, e) ⊢⁺ (0, 0, 0, 2*A+2, e+A+1)
theorem phases12_from1 (A e : ℕ) : ⟨A + 1, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * A + 2, e + A + 1⟩ := by
  have h1 : ⟨A + 1, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢ ⟨A, 0, 1, 0, e + 1⟩ := by simp [fm]
  apply step_stepStar_stepPlus h1
  -- now goal: (A, 0, 1, 0, e+1) ⊢* (0, 0, 0, 2*A+2, e+A+1)
  -- R3 chain A more times: (A, 0, 1, 0, e+1) -> (0, 0, 1+A, 0, e+1+A)
  have h2 : ⟨A, (0 : ℕ), (1 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢* ⟨0, 0, A + 1, 0, e + A + 1⟩ := by
    have := r3_chain A 0 1 (e + 1)
    rw [show (1 : ℕ) + A = A + 1 from by ring, show e + 1 + A = e + A + 1 from by ring] at this
    convert this using 2; ring_nf
  apply stepStar_trans h2
  -- R4 chain
  have h3 := r4_chain (A + 1) 0 0 (e + A + 1); simp at h3
  apply stepStar_trans h3
  rw [show 2 * (A + 1) = 2 * A + 2 from by ring]; exists 0

-- Transition for even a: (2*(k+1), 0, 0, 0, e) ⊢⁺ (3*k+6, 0, 0, 0, e+4*k+2)
theorem trans_even (k e : ℕ) :
    ⟨2 * (k + 1), (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢⁺ ⟨3 * k + 6, 0, 0, 0, e + 4 * k + 2⟩ := by
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phases12_from1 (2 * k + 1) e)
  rw [show 2 * (2 * k + 1) + 2 = 0 + 4 * (k + 1) from by ring,
      show e + (2 * k + 1) + 1 = (e + k + 1) + (k + 1) from by ring]
  -- Drain rounds
  apply stepStar_trans (combined_rounds k 0 (e + k + 1))
  rw [show 3 * (k + 1) = (3 * k) + 3 from by ring,
      show e + k + 1 = (e + k) + 1 from by ring]
  -- Endgame r0
  apply stepStar_trans (endgame_r0 (3 * k) (e + k))
  rw [show 3 * k + 6 = 3 * k + 6 from by ring,
      show e + k + (3 * k) + 2 = e + 4 * k + 2 from by ring]; exists 0

-- Transition for odd a, k=0: (1, 0, 0, 0, e) ⊢⁺ (3, 0, 0, 0, e+1)
theorem trans_odd_0 (e : ℕ) :
    ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢⁺ ⟨3, 0, 0, 0, e + 1⟩ := by
  execute fm 9

-- Transition for odd a, k >= 1: (2*k+3, 0, 0, 0, e) ⊢⁺ (3*k+6, 0, 0, 0, e+4*k+5)
-- Here a = 2(k+1)+1 = 2k+3, odd.
-- a' = (3*(2k+3)+3)/2 = (6k+12)/2 = 3k+6
-- e' = e + 2*(2k+3) - 1 = e + 4k + 5
theorem trans_odd_kge1 (k e : ℕ) :
    ⟨2 * k + 3, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢⁺ ⟨3 * k + 6, 0, 0, 0, e + 4 * k + 5⟩ := by
  rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phases12_from1 (2 * k + 2) e)
  rw [show 2 * (2 * k + 2) + 2 = 2 + 4 * (k + 1) from by ring,
      show e + (2 * k + 2) + 1 = (e + k + 2) + (k + 1) from by ring]
  -- Drain rounds: K+1 = k+1 rounds, remainder = 2
  apply stepStar_trans (combined_rounds k 2 (e + k + 2))
  rw [show 3 * (k + 1) = (3 * k) + 3 from by ring,
      show e + k + 2 = (e + k + 1) + 1 from by ring]
  -- Endgame r2
  apply stepStar_trans (endgame_r2 (3 * k) (e + k + 1))
  rw [show 3 * k + 6 = 3 * k + 6 from by ring,
      show e + k + 1 + (3 * k) + 4 = e + 4 * k + 5 from by ring]; exists 0

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e⟩)
  · intro c ⟨a, e, hq⟩; subst hq
    rcases Nat.even_or_odd (a + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- even case: a+1 = 2k, so k >= 1
      have hk1 : k ≥ 1 := by omega
      obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk1
      rw [show a + 1 = 2 * (k' + 1) from by omega]
      exact ⟨⟨3 * k' + 6, 0, 0, 0, e + 4 * k' + 2⟩,
        ⟨3 * k' + 5, e + 4 * k' + 2, by ring_nf⟩, trans_even k' e⟩
    · -- odd case: a+1 = 2k+1
      rcases k with _ | k
      · -- k=0: a+1=1
        rw [show a + 1 = 1 from by omega]
        exact ⟨⟨3, 0, 0, 0, e + 1⟩, ⟨2, e + 1, by ring_nf⟩, trans_odd_0 e⟩
      · -- k >= 1: a+1 = 2(k+1)+1 = 2k+3
        rw [show a + 1 = 2 * k + 3 from by omega]
        exact ⟨⟨3 * k + 6, 0, 0, 0, e + 4 * k + 5⟩,
          ⟨3 * k + 5, e + 4 * k + 5, by ring_nf⟩, trans_odd_kge1 k e⟩
  · exact ⟨0, 0, rfl⟩
