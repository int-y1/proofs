import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #912: [4/15, 3/14, 55/2, 49/5, 20/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  1  0  1
 0  0 -1  2  0
 2  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_912

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

-- R3 drain: (a+k, 0, c, 0, e) ⊢* (a, 0, c+k, 0, e+k)
theorem r3_drain : ∀ k, ∀ a c e,
    ⟨a + k, (0 : ℕ), c, (0 : ℕ), e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 1))
    rw [show c + 1 + k = c + (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]; exists 0

-- R4 chain: (0, 0, c+k, d, e) ⊢* (0, 0, c, d+2k, e)
theorem r4_chain : ∀ k, ∀ c d e,
    ⟨(0 : ℕ), (0 : ℕ), c + k, d, e⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 2) e)
    rw [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]; exists 0

-- Spiral round B=0: (0, 0, 0, d+4, e+1) ⊢* (0, 3, 0, d, e)
theorem spiral_round_b0 : ∀ d e,
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 4, e + 1⟩ [fm]⊢* ⟨0, 3, 0, d, e⟩ := by
  intro d e; execute fm 6

-- Spiral round B≥1: (0, b+1, 0, d+4, e+1) ⊢* (0, b+4, 0, d, e)
theorem spiral_round_b1 : ∀ b d e,
    ⟨(0 : ℕ), b + 1, (0 : ℕ), d + 4, e + 1⟩ [fm]⊢* ⟨0, b + 4, 0, d, e⟩ := by
  intro b d e; execute fm 6

-- Spiral chain: (0, b, 0, d+4k, e+k) ⊢* (0, b+3k, 0, d, e)
theorem spiral : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b, (0 : ℕ), d + 4 * k, e + k⟩ [fm]⊢* ⟨0, b + 3 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + 4 * (k + 1) = (d + 4 * k) + 4 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    rcases b with _ | b
    · apply stepStar_trans (spiral_round_b0 (d + 4 * k) (e + k))
      apply stepStar_trans (ih 3 d e)
      rw [show 3 + 3 * k = 0 + 3 * (k + 1) from by ring]; exists 0
    · apply stepStar_trans (spiral_round_b1 b (d + 4 * k) (e + k))
      apply stepStar_trans (ih (b + 4) d e)
      rw [show b + 4 + 3 * k = (b + 1) + 3 * (k + 1) from by ring]; exists 0

-- Tail D=0: (0, b+1, 0, 0, e+1) ⊢* (4, b, 0, 0, e)
theorem tail_d0 : ∀ b e,
    ⟨(0 : ℕ), b + 1, (0 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢* ⟨4, b, 0, 0, e⟩ := by
  intro b e; execute fm 2

-- Tail D=2 B=0: (0, 0, 0, 2, e+1) ⊢* (3, 0, 0, 0, e+1)
theorem tail_d2_b0 : ∀ e,
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), e + 1⟩ [fm]⊢* ⟨3, 0, 0, 0, e + 1⟩ := by
  intro e; execute fm 6

-- Tail D=2 B≥1: (0, b+1, 0, 2, e+1) ⊢* (3, b+1, 0, 0, e+1)
theorem tail_d2_b1 : ∀ b e,
    ⟨(0 : ℕ), b + 1, (0 : ℕ), (2 : ℕ), e + 1⟩ [fm]⊢* ⟨3, b + 1, 0, 0, e + 1⟩ := by
  intro b e; execute fm 6

-- R3/R1 interleave: (a+1, k, 0, 0, e) ⊢* (a+k+1, 0, 0, 0, e+k)
theorem r3r1_chain : ∀ k, ∀ a e,
    ⟨a + 1, k, (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    rw [show a + 1 + k + 1 = a + (k + 1) + 1 from by ring,
        show e + 1 + k = e + (k + 1) from by ring]; exists 0

-- Main transition for even A=2*(m+1): (2*(m+1), 0, 0, 0, e) ⊢⁺ (3*m+6, 0, 0, 0, e+4*m+2)
theorem trans_even (m e : ℕ) :
    ⟨2 * m + 2, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢⁺
    ⟨3 * m + 6, 0, 0, 0, e + 4 * m + 2⟩ := by
  -- First R3 step for ⊢⁺
  apply step_stepStar_stepPlus
  · show fm ⟨2 * m + 2, 0, 0, 0, e⟩ = some ⟨2 * m + 1, 0, 1, 0, e + 1⟩
    rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]; simp [fm]
  -- R3 drain remaining 2*m+1 steps
  have h1 : ⟨2 * m + 1, (0 : ℕ), (1 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢*
      ⟨0, 0, 2 * m + 2, 0, e + 2 * m + 2⟩ := by
    have := r3_drain (2 * m + 1) 0 1 (e + 1)
    rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring,
        show 1 + (2 * m + 1) = 2 * m + 2 from by ring,
        show e + 1 + (2 * m + 1) = e + 2 * m + 2 from by ring] at this
    exact this
  -- R4 chain
  have h2 : ⟨(0 : ℕ), (0 : ℕ), 2 * m + 2, (0 : ℕ), e + 2 * m + 2⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * m + 4, e + 2 * m + 2⟩ := by
    have := r4_chain (2 * m + 2) 0 0 (e + 2 * m + 2)
    rw [show 0 + (2 * m + 2) = 2 * m + 2 from by ring,
        show 0 + 2 * (2 * m + 2) = 4 * m + 4 from by ring] at this
    exact this
  -- Spiral (m+1 rounds): (0, 0, 0, 4*(m+1), e+2*(m+1)) ⊢* (0, 3*(m+1), 0, 0, e+(m+1))
  have h3 : ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * m + 4, e + 2 * m + 2⟩ [fm]⊢*
      ⟨0, 3 * m + 3, 0, 0, e + m + 1⟩ := by
    have := spiral (m + 1) 0 0 (e + m + 1)
    rw [show 0 + 4 * (m + 1) = 4 * m + 4 from by ring,
        show (e + m + 1) + (m + 1) = e + 2 * m + 2 from by ring,
        show 0 + 3 * (m + 1) = 3 * m + 3 from by ring] at this
    exact this
  -- Tail D=0: (0, 3m+3, 0, 0, e+m+1) ⊢* (4, 3m+2, 0, 0, e+m)
  have h4 : ⟨(0 : ℕ), 3 * m + 3, (0 : ℕ), (0 : ℕ), e + m + 1⟩ [fm]⊢*
      ⟨4, 3 * m + 2, 0, 0, e + m⟩ := by
    rw [show 3 * m + 3 = (3 * m + 2) + 1 from by ring,
        show e + m + 1 = (e + m) + 1 from by ring]
    exact tail_d0 (3 * m + 2) (e + m)
  -- R3/R1 chain: (4, 3m+2, 0, 0, e+m) ⊢* (3m+6, 0, 0, 0, e+4m+2)
  have h5 : ⟨(4 : ℕ), 3 * m + 2, (0 : ℕ), (0 : ℕ), e + m⟩ [fm]⊢*
      ⟨3 * m + 6, 0, 0, 0, e + 4 * m + 2⟩ := by
    have := r3r1_chain (3 * m + 2) 3 (e + m)
    rw [show 3 + 1 = (4 : ℕ) from by ring,
        show 3 + (3 * m + 2) + 1 = 3 * m + 6 from by ring,
        show e + m + (3 * m + 2) = e + 4 * m + 2 from by ring] at this
    exact this
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

-- Main transition for odd A=2*m+1: (2*m+1, 0, 0, 0, e) ⊢⁺ (3*m+3, 0, 0, 0, e+4*m+1)
theorem trans_odd (m e : ℕ) :
    ⟨2 * m + 1, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢⁺
    ⟨3 * m + 3, 0, 0, 0, e + 4 * m + 1⟩ := by
  -- First R3 step for ⊢⁺
  apply step_stepStar_stepPlus
  · show fm ⟨2 * m + 1, 0, 0, 0, e⟩ = some ⟨2 * m, 0, 1, 0, e + 1⟩
    rw [show 2 * m + 1 = (2 * m) + 1 from by ring]; simp [fm]
  -- R3 drain remaining 2*m steps
  have h1 : ⟨2 * m, (0 : ℕ), (1 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢*
      ⟨0, 0, 2 * m + 1, 0, e + 2 * m + 1⟩ := by
    have := r3_drain (2 * m) 0 1 (e + 1)
    rw [show 0 + 2 * m = 2 * m from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring,
        show e + 1 + 2 * m = e + 2 * m + 1 from by ring] at this
    exact this
  -- R4 chain
  have h2 : ⟨(0 : ℕ), (0 : ℕ), 2 * m + 1, (0 : ℕ), e + 2 * m + 1⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * m + 2, e + 2 * m + 1⟩ := by
    have := r4_chain (2 * m + 1) 0 0 (e + 2 * m + 1)
    rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring,
        show 0 + 2 * (2 * m + 1) = 4 * m + 2 from by ring] at this
    exact this
  -- Spiral (m rounds): (0, 0, 0, 2+4m, e+m+1+m) ⊢* (0, 3m, 0, 2, e+m+1)
  have h3 : ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * m + 2, e + 2 * m + 1⟩ [fm]⊢*
      ⟨0, 3 * m, 0, 2, e + m + 1⟩ := by
    have := spiral m 0 2 (e + m + 1)
    rw [show 2 + 4 * m = 4 * m + 2 from by ring,
        show (e + m + 1) + m = e + 2 * m + 1 from by ring,
        show 0 + 3 * m = 3 * m from by ring] at this
    exact this
  -- Tail D=2
  have h4 : ⟨(0 : ℕ), 3 * m, (0 : ℕ), (2 : ℕ), e + m + 1⟩ [fm]⊢*
      ⟨3, 3 * m, 0, 0, e + m + 1⟩ := by
    rcases m with _ | m'
    · -- m=0
      exact tail_d2_b0 e
    · -- m≥1: 3*(m'+1) = 3*m'+3 = (3*m'+2)+1
      rw [show 3 * (m' + 1) = (3 * m' + 2) + 1 from by ring,
          show e + (m' + 1) + 1 = (e + m' + 1) + 1 from by ring]
      have := tail_d2_b1 (3 * m' + 2) (e + m' + 1)
      rw [show 3 * m' + 2 + 1 = 3 * (m' + 1) from by ring,
          show (e + m' + 1) + 1 = e + (m' + 1) + 1 from by ring] at this
      exact this
  -- R3/R1 chain: (3, 3m, 0, 0, e+m+1) ⊢* (3m+3, 0, 0, 0, e+4m+1)
  have h5 : ⟨(3 : ℕ), 3 * m, (0 : ℕ), (0 : ℕ), e + m + 1⟩ [fm]⊢*
      ⟨3 * m + 3, 0, 0, 0, e + 4 * m + 1⟩ := by
    have := r3r1_chain (3 * m) 2 (e + m + 1)
    rw [show 2 + 1 = (3 : ℕ) from by ring,
        show 2 + 3 * m + 1 = 3 * m + 3 from by ring,
        show e + m + 1 + 3 * m = e + 4 * m + 1 from by ring] at this
    exact this
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e⟩)
  · intro c ⟨a, e, hq⟩; subst hq
    rcases Nat.even_or_odd (a + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- a+1 = 2*m (even), need m ≥ 1
      rcases m with _ | m'
      · omega
      · -- a+1 = 2*(m'+1) = 2*m'+2
        have ha : a + 1 = 2 * m' + 2 := by omega
        rw [ha]
        exact ⟨⟨3 * m' + 6, 0, 0, 0, e + 4 * m' + 2⟩,
          ⟨3 * m' + 5, e + 4 * m' + 2, by ring_nf⟩,
          trans_even m' e⟩
    · -- a+1 = 2*m+1 (odd)
      have ha : a + 1 = 2 * m + 1 := by omega
      rw [ha]
      exact ⟨⟨3 * m + 3, 0, 0, 0, e + 4 * m + 1⟩,
        ⟨3 * m + 2, e + 4 * m + 1, by ring_nf⟩,
        trans_odd m e⟩
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_912
