import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1607: [77/15, 18/91, 13/3, 5/11, 45/2]

This Fractran program doesn't halt.

Canonical states: (A+1, 0, 0, 0, n+1, 2n+2) with quadratic growth in A.
Transition: (A+1, 0, 0, 0, n+1, 2n+2) -> (A+n+2, 0, 0, 0, n+2, 2n+4).

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1607

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a+1, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+2, c+1, d, e, f⟩
  | _ => none

-- R4 chain: e transfers to c
theorem r4_chain : ∀ k, ∀ A C F,
    ⟨A, 0, C, 0, k, F⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0, F⟩ := by
  intro k; induction' k with k ih <;> intro A C F
  · exists 0
  · step fm
    have := ih A (C + 1) F
    rw [show C + 1 + k = C + (k + 1) from by ring] at this
    exact this

-- R3 chain: b transfers to f
theorem r3_chain : ∀ k, ∀ A E F,
    ⟨A, k, 0, 0, E, F⟩ [fm]⊢* ⟨A, 0, 0, 0, E, F + k⟩ := by
  intro k; induction' k with k ih <;> intro A E F
  · exists 0
  · step fm
    have := ih A E (F + 1)
    rw [show F + 1 + k = F + (k + 1) from by ring] at this
    exact this

-- R2 drain: d and f both decrease, a and b increase
theorem r2_drain : ∀ k, ∀ A B E F,
    ⟨A, B, 0, k, E, F + k⟩ [fm]⊢* ⟨A + k, B + 2 * k, 0, 0, E, F⟩ := by
  intro k; induction' k with k ih <;> intro A B E F
  · exists 0
  · rw [show F + (k + 1) = (F + k) + 1 from by ring]
    have hstep : ⟨A, B, 0, k + 1, E, (F + k) + 1⟩ [fm]⊢ ⟨A + 1, B + 2, 0, k, E, F + k⟩ := by
      simp [fm]
    have := ih (A + 1) (B + 2) E F
    rw [show A + 1 + k = A + (k + 1) from by ring,
        show B + 2 + 2 * k = B + 2 * (k + 1) from by ring] at this
    exact stepStar_trans (step_stepStar hstep) this

-- R2-R1-R1 chain: each cycle reduces c by 2
-- From (X, 0, C + 2k, D+1, E, F+k) to (X+k, 0, C, D+k+1, E+2k, F)
theorem r2r1r1_chain : ∀ k, ∀ C X D E F,
    ⟨X, 0, C + 2 * k, D + 1, E, F + k⟩ [fm]⊢* ⟨X + k, 0, C, D + k + 1, E + 2 * k, F⟩ := by
  intro k; induction' k with k ih <;> intro C X D E F
  · simp; exists 0
  · rw [show F + (k + 1) = (F + k) + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k + 1) + 1 from by ring]
    have hs1 : ⟨X, 0, (C + 2 * k + 1) + 1, D + 1, E, (F + k) + 1⟩ [fm]⊢
        ⟨X + 1, 2, (C + 2 * k + 1) + 1, D, E, F + k⟩ := by simp [fm]
    have hs2 : ⟨X + 1, 2, (C + 2 * k + 1) + 1, D, E, F + k⟩ [fm]⊢
        ⟨X + 1, 1, C + 2 * k + 1, D + 1, E + 1, F + k⟩ := by
      rw [show (2 : ℕ) = 1 + 1 from by ring]; simp [fm]
    have hs3 : ⟨X + 1, 1, C + 2 * k + 1, D + 1, E + 1, F + k⟩ [fm]⊢
        ⟨X + 1, 0, C + 2 * k, D + 2, E + 2, F + k⟩ := by
      rw [show C + 2 * k + 1 = (C + 2 * k) + 1 from by ring]; simp [fm]
    have h3steps : ⟨X, 0, (C + 2 * k + 1) + 1, D + 1, E, (F + k) + 1⟩ [fm]⊢*
        ⟨X + 1, 0, C + 2 * k, D + 2, E + 2, F + k⟩ :=
      stepStar_trans (step_stepStar hs1)
        (stepStar_trans (step_stepStar hs2) (step_stepStar hs3))
    have := ih C (X + 1) (D + 1) (E + 2) F
    rw [show D + 2 = (D + 1) + 1 from by ring] at h3steps
    rw [show X + 1 + k = X + (k + 1) from by ring,
        show D + 1 + k + 1 = D + (k + 1) + 1 from by ring,
        show E + 2 + 2 * k = E + 2 * (k + 1) from by ring] at this
    exact stepStar_trans h3steps this

-- Middle phase for even n (n = 2k):
-- From (A, 0, 2k, 2, 2, 2n+2) = (A, 0, 2k, 2, 2, 4k+2)
-- After r2r1r1 chain with k iterations: (A+k, 0, 0, k+2, 2k+2, 3k+2)
-- After r2_drain with k+2: (A+2k+2, 2k+4, 0, 0, 2k+2, 2k)
theorem middle_even (k : ℕ) : ∀ A,
    ⟨A, 0, 2 * k, 2, 2, 4 * k + 2⟩ [fm]⊢*
    ⟨A + 2 * k + 2, 2 * k + 4, 0, 0, 2 * k + 2, 2 * k⟩ := by
  intro A
  have h1 := r2r1r1_chain k 0 A 1 2 (3 * k + 2)
  rw [show (0 : ℕ) + 2 * k = 2 * k from by ring,
      show (3 * k + 2) + k = 4 * k + 2 from by ring,
      show 1 + k + 1 = k + 2 from by ring,
      show (2 : ℕ) + 2 * k = 2 * k + 2 from by ring] at h1
  have h2 := r2_drain (k + 2) (A + k) 0 (2 * k + 2) (2 * k)
  rw [show (2 * k) + (k + 2) = 3 * k + 2 from by ring,
      show A + k + (k + 2) = A + 2 * k + 2 from by ring,
      show 0 + 2 * (k + 2) = 2 * k + 4 from by ring] at h2
  exact stepStar_trans h1 h2

-- Middle phase for odd n (n = 2k+1):
-- From (A, 0, 2k+1, 2, 2, 4k+4)
-- After r2r1r1 chain with k iterations: (A+k, 0, 1, k+2, 2k+2, 3k+4)
-- Then R2: (A+k+1, 2, 1, k+1, 2k+2, 3k+3)
-- Then R1: (A+k+1, 1, 0, k+2, 2k+3, 3k+3)
-- Then R2 needs d >= 1, f >= 1: (A+k+2, 3, 0, k+1, 2k+3, 3k+2)
-- After r2_drain with k+1: (A+2k+3, 2k+5, 0, 0, 2k+3, 2k+1)
theorem middle_odd (k : ℕ) : ∀ A,
    ⟨A, 0, 2 * k + 1, 2, 2, 4 * k + 4⟩ [fm]⊢*
    ⟨A + 2 * k + 3, 2 * k + 5, 0, 0, 2 * k + 3, 2 * k + 1⟩ := by
  intro A
  have h1 := r2r1r1_chain k 1 A 1 2 (3 * k + 4)
  rw [show (1 : ℕ) + 2 * k = 2 * k + 1 from by ring,
      show (3 * k + 4) + k = 4 * k + 4 from by ring,
      show 1 + k + 1 = k + 2 from by ring,
      show (2 : ℕ) + 2 * k = 2 * k + 2 from by ring] at h1
  -- Now at (A+k, 0, 1, k+2, 2+2k, 3k+4)
  -- R2 step: d=k+2 >= 1, f=3k+4 >= 1
  have hs1 : ∀ X E F,
      ⟨X, 0, 1, (k + 1) + 1, E, (F + 1) + 1⟩ [fm]⊢ ⟨X + 1, 2, 1, k + 1, E, F + 1⟩ := by
    intro X E F; simp [fm]
  -- R1 step: b=2, c=1
  have hs2 : ∀ X E F,
      ⟨X + 1, 2, 1, k + 1, E, F + 1⟩ [fm]⊢ ⟨X + 1, 1, 0, k + 2, E + 1, F + 1⟩ := by
    intro X E F; rw [show (2 : ℕ) = 1 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]; simp [fm]
  -- R2 step: b=1, c=0, d=k+2 >= 1, f >= 1
  have hs3 : ∀ X E F,
      ⟨X + 1, 1, 0, (k + 1) + 1, E + 1, (F) + 1⟩ [fm]⊢ ⟨X + 2, 3, 0, k + 1, E + 1, F⟩ := by
    intro X E F; rw [show (1 : ℕ) = 0 + 1 from by ring]; simp [fm]
  have h2 : ⟨A + k, 0, 1, k + 2, 2 * k + 2, 3 * k + 4⟩ [fm]⊢*
      ⟨A + k + 2, 3, 0, k + 1, 2 * k + 3, 3 * k + 2⟩ := by
    rw [show k + 2 = (k + 1) + 1 from by ring,
        show 3 * k + 4 = (3 * k + 2 + 1) + 1 from by ring]
    exact stepStar_trans (step_stepStar (hs1 (A + k) (2 * k + 2) (3 * k + 2)))
      (stepStar_trans (step_stepStar (hs2 (A + k) (2 * k + 2) (3 * k + 2)))
        (by rw [show k + 2 = (k + 1) + 1 from by ring]
            exact step_stepStar (hs3 (A + k) (2 * k + 2) (3 * k + 2))))
  have h3 := r2_drain (k + 1) (A + k + 2) 3 (2 * k + 3) (2 * k + 1)
  rw [show (2 * k + 1) + (k + 1) = 3 * k + 2 from by ring,
      show A + k + 2 + (k + 1) = A + 2 * k + 3 from by ring,
      show 3 + 2 * (k + 1) = 2 * k + 5 from by ring] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

-- Main transition for even e: e = 2k+1 (so n+1 = 2k+1, n = 2k)
-- (A+1, 0, 0, 0, 2k+1, 4k+2) ->+ (A+2k+2, 0, 0, 0, 2k+2, 4k+4)
theorem main_trans_even (k : ℕ) (A : ℕ) :
    ⟨A + 1, 0, 0, 0, 2 * k + 1, 4 * k + 2⟩ [fm]⊢⁺
    ⟨A + 2 * k + 2, 0, 0, 0, 2 * k + 2, 4 * k + 4⟩ := by
  -- Phase 1: R4 chain
  have p1 := r4_chain (2 * k + 1) (A + 1) 0 (4 * k + 2)
  rw [show (0 : ℕ) + (2 * k + 1) = 2 * k + 1 from by ring] at p1
  -- Phase 2: R5
  have p2 : ⟨A + 1, 0, 2 * k + 1, 0, 0, 4 * k + 2⟩ [fm]⊢*
      ⟨A, 2, 2 * k + 2, 0, 0, 4 * k + 2⟩ := by
    step fm; finish
  -- Phase 3: R1 x 2
  have p3 : ⟨A, 2, 2 * k + 2, 0, 0, 4 * k + 2⟩ [fm]⊢*
      ⟨A, 0, 2 * k, 2, 2, 4 * k + 2⟩ := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; finish
  -- Phase 4: Middle (even case, n = 2k)
  have p4 := middle_even k A
  -- Phase 5: R3 drain
  have p5 := r3_chain (2 * k + 4) (A + 2 * k + 2) (2 * k + 2) (2 * k)
  rw [show (2 * k) + (2 * k + 4) = 4 * k + 4 from by ring] at p5
  have pall : ⟨A + 1, 0, 0, 0, 2 * k + 1, 4 * k + 2⟩ [fm]⊢*
      ⟨A + 2 * k + 2, 0, 0, 0, 2 * k + 2, 4 * k + 4⟩ :=
    stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4 p5)))
  exact stepStar_stepPlus pall (by simp [Q])

-- Main transition for odd e: e = 2k+2 (so n+1 = 2k+2, n = 2k+1)
-- (A+1, 0, 0, 0, 2k+2, 4k+4) ->+ (A+2k+3, 0, 0, 0, 2k+3, 4k+6)
theorem main_trans_odd (k : ℕ) (A : ℕ) :
    ⟨A + 1, 0, 0, 0, 2 * k + 2, 4 * k + 4⟩ [fm]⊢⁺
    ⟨A + 2 * k + 3, 0, 0, 0, 2 * k + 3, 4 * k + 6⟩ := by
  -- Phase 1: R4 chain
  have p1 := r4_chain (2 * k + 2) (A + 1) 0 (4 * k + 4)
  rw [show (0 : ℕ) + (2 * k + 2) = 2 * k + 2 from by ring] at p1
  -- Phase 2: R5
  have p2 : ⟨A + 1, 0, 2 * k + 2, 0, 0, 4 * k + 4⟩ [fm]⊢*
      ⟨A, 2, 2 * k + 3, 0, 0, 4 * k + 4⟩ := by
    step fm; finish
  -- Phase 3: R1 x 2
  have p3 : ⟨A, 2, 2 * k + 3, 0, 0, 4 * k + 4⟩ [fm]⊢*
      ⟨A, 0, 2 * k + 1, 2, 2, 4 * k + 4⟩ := by
    rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; finish
  -- Phase 4: Middle (odd case, n = 2k+1)
  have p4 := middle_odd k A
  -- Phase 5: R3 drain
  have p5 := r3_chain (2 * k + 5) (A + 2 * k + 3) (2 * k + 3) (2 * k + 1)
  rw [show (2 * k + 1) + (2 * k + 5) = 4 * k + 6 from by ring] at p5
  have pall : ⟨A + 1, 0, 0, 0, 2 * k + 2, 4 * k + 4⟩ [fm]⊢*
      ⟨A + 2 * k + 3, 0, 0, 0, 2 * k + 3, 4 * k + 6⟩ :=
    stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4 p5)))
  exact stepStar_stepPlus pall (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1, 2⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A n, q = ⟨A + 1, 0, 0, 0, n + 1, 2 * n + 2⟩)
  · rintro q ⟨A, n, rfl⟩
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      refine ⟨⟨A + 2 * k + 2, 0, 0, 0, 2 * k + 2, 4 * k + 4⟩,
              ⟨A + 2 * k + 1, 2 * k + 1, by simp [Q]; ring⟩, ?_⟩
      rw [show k + k + 1 = 2 * k + 1 from by ring,
          show 2 * (k + k) + 2 = 4 * k + 2 from by ring]
      exact main_trans_even k A
    · subst hk
      refine ⟨⟨A + 2 * k + 3, 0, 0, 0, 2 * k + 3, 4 * k + 6⟩,
              ⟨A + 2 * k + 2, 2 * k + 2, by simp [Q]; ring⟩, ?_⟩
      rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
          show 2 * (2 * k + 1) + 2 = 4 * k + 4 from by ring]
      exact main_trans_odd k A
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_1607
