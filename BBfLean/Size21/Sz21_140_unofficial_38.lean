import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #38: [35/6, 28/55, 121/2, 3/7, 5/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  1 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_38

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: (0, b, 0, d+k, e) →* (0, b+k, 0, d, e)
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b d

-- R3 repeated: (a+k, 0, 0, d, e) →* (a, 0, 0, d, e+2*k)
theorem a_to_e : ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+2*k⟩ := by
  have many_step : ∀ k a e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+2*k⟩ := by
    intro k; induction' k with k h <;> intro a e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a e

-- R2 chain with leftover: (a, 0, c+k, d, E+k) →* (a+2*k, 0, c, d+k, E)
theorem r2_chain : ⟨a, 0, c+k, d, E+k⟩ [fm]⊢* ⟨a+2*k, 0, c, d+k, E⟩ := by
  have many_step : ∀ k a c d E, ⟨a, 0, c+k, d, E+k⟩ [fm]⊢* ⟨a+2*k, 0, c, d+k, E⟩ := by
    intro k; induction' k with k h <;> intro a c d E
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _ _ _)
    ring_nf; finish
  exact many_step k a c d E

-- R1R1R2 round: 3 steps
-- (2, B+2, C, D, E+1) →⁺ (2, B, C+1, D+3, E)
theorem r1r1r2_one : ⟨2, B+2, C, D, E+1⟩ [fm]⊢⁺ ⟨2, B, C+1, D+3, E⟩ := by
  rw [show B + 2 = (B + 1) + 1 from by ring]
  step fm
  step fm
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm
  finish

-- R1R1R2 rounds by induction: k rounds
-- (2, B+2*k, C, D, E+k) →* (2, B, C+k, D+3*k, E)
theorem r1r1r2_rounds : ∀ k, ∀ C D E, ⟨2, B+2*k, C, D, E+k⟩ [fm]⊢* ⟨2, B, C+k, D+3*k, E⟩ := by
  intro k; induction' k with k h <;> intro C D E
  · exists 0
  rw [show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  have h1 : ⟨2, (B + 2 * k) + 2, C, D, (E + k) + 1⟩ [fm]⊢⁺ ⟨2, B + 2 * k, C + 1, D + 3, E + k⟩ :=
    @r1r1r2_one (B + 2 * k) C D (E + k)
  apply stepStar_trans (stepPlus_stepStar h1)
  have h2 := h (C + 1) (D + 3) E
  refine stepStar_trans h2 ?_
  ring_nf; finish

-- Even case: d = 2m
-- (0, 0, 0, 2m, 2m+2+E) →⁺ (0, 0, 0, 4m+1, 4m+4+E)
theorem main_trans_even (m E : ℕ) :
    ⟨0, 0, 0, 2 * m, 2 * m + 2 + E⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m + 1, 4 * m + 4 + E⟩ := by
  -- Phase 1: R4 * 2m → (0, 2m, 0, 0, 2m+2+E)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2 * m, 0, 0, 2 * m + 2 + E⟩)
  · have h := @d_to_b 0 0 (2 * m) (2 * m + 2 + E)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 step
  -- State: (0, 2m, 0, 0, 2m+2+E). Need to show e = (...)+1 for R5.
  rw [show 2 * m + 2 + E = (2 * m + 1 + E) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * m, 0, 0, (2 * m + 1 + E) + 1⟩ = some ⟨0, 2 * m, 1, 0, 2 * m + 1 + E⟩
    simp [fm]
  -- Phase 3: R2 one step → (2, 2m, 0, 1, 2m+E)
  rw [show 2 * m + 1 + E = (2 * m + E) + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨2, 2 * m, 0, 1, 2 * m + E⟩)
  · have : fm ⟨0, 2 * m, 0 + 1, 0, (2 * m + E) + 1⟩ = some ⟨0 + 2, 2 * m, 0, 0 + 1, 2 * m + E⟩ := by
      simp [fm]
    exact step_stepStar this
  -- Phase 4: R1R1R2 * m rounds → (2, 0, m, 1+3m, m+E)
  -- r1r1r2_rounds: (2, B+2k, C, D, E'+k) →* (2, B, C+k, D+3k, E')
  -- With B=0, k=m, C=0, D=1, E'=m+E
  rw [show 2 * m + E = (m + E) + m from by ring]
  apply stepStar_trans (c₂ := ⟨2, 0, m, 1 + 3 * m, m + E⟩)
  · have h := @r1r1r2_rounds 0 m 0 1 (m + E)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 5: R2 chain * m → (2+2m, 0, 0, 1+4m, E)
  -- r2_chain: (a, 0, c+k, d, E'+k) →* (a+2k, 0, c, d+k, E')
  -- With a=2, c=0, k=m, d=1+3m, E'=E
  rw [show m + E = E + m from by ring]
  apply stepStar_trans (c₂ := ⟨2 + 2 * m, 0, 0, 1 + 3 * m + m, E⟩)
  · have h := @r2_chain 2 0 m (1 + 3 * m) E
    simp only [Nat.zero_add] at h; exact h
  -- Phase 6: R3 chain * (2+2m) → (0, 0, 0, 4m+1, E+2*(2+2m))
  rw [show 1 + 3 * m + m = 4 * m + 1 from by ring]
  have h := @a_to_e 0 (2 + 2 * m) (4 * m + 1) E
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Odd case: d = 2m+1
-- (0, 0, 0, 2m+1, 2m+3+E) →⁺ (0, 0, 0, 4m+3, 4m+6+E)
theorem main_trans_odd (m E : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, 2 * m + 3 + E⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m + 3, 4 * m + 6 + E⟩ := by
  -- Phase 1: R4 * (2m+1) → (0, 2m+1, 0, 0, 2m+3+E)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2 * m + 1, 0, 0, 2 * m + 3 + E⟩)
  · have h := @d_to_b 0 0 (2 * m + 1) (2 * m + 3 + E)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 step
  rw [show 2 * m + 3 + E = (2 * m + 2 + E) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * m + 1, 0, 0, (2 * m + 2 + E) + 1⟩ = some ⟨0, 2 * m + 1, 1, 0, 2 * m + 2 + E⟩
    simp [fm]
  -- Phase 3: R2 one step → (2, 2m+1, 0, 1, 2m+1+E)
  rw [show 2 * m + 2 + E = (2 * m + 1 + E) + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨2, 2 * m + 1, 0, 1, 2 * m + 1 + E⟩)
  · have : fm ⟨0, 2 * m + 1, 0 + 1, 0, (2 * m + 1 + E) + 1⟩ = some ⟨0 + 2, 2 * m + 1, 0, 0 + 1, 2 * m + 1 + E⟩ := by
      simp [fm]
    exact step_stepStar this
  -- Phase 4: R1R1R2 * m rounds → (2, 1, m, 1+3m, m+1+E)
  -- B=1, k=m
  rw [show (2 : ℕ) * m + 1 = 1 + 2 * m from by ring]
  rw [show 1 + 2 * m + E = (m + 1 + E) + m from by ring]
  apply stepStar_trans (c₂ := ⟨2, 1, m, 1 + 3 * m, m + 1 + E⟩)
  · have h := @r1r1r2_rounds 1 m 0 1 (m + 1 + E)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 5: R1 once → (1, 0, m+1, 2+3m, m+1+E)
  apply stepStar_trans (c₂ := ⟨1, 0, m + 1, 2 + 3 * m, m + 1 + E⟩)
  · have : fm ⟨1 + 1, 0 + 1, m, 1 + 3 * m, m + 1 + E⟩ = some ⟨1, 0, m + 1, (1 + 3 * m) + 1, m + 1 + E⟩ := by
      simp [fm]
    rw [show (1 + 3 * m) + 1 = 2 + 3 * m from by ring] at this
    exact step_stepStar this
  -- Phase 6: R2 chain * (m+1) → (2m+3, 0, 0, 4m+3, E)
  rw [show m + 1 + E = E + (m + 1) from by ring]
  apply stepStar_trans (c₂ := ⟨1 + 2 * (m + 1), 0, 0, 2 + 3 * m + (m + 1), E⟩)
  · have h := @r2_chain 1 0 (m + 1) (2 + 3 * m) E
    simp only [Nat.zero_add] at h; exact h
  -- Phase 7: R3 chain * (2m+3) → (0, 0, 0, 4m+3, E+2*(2m+3))
  rw [show 2 + 3 * m + (m + 1) = 4 * m + 3 from by ring,
      show 1 + 2 * (m + 1) = 2 * m + 3 from by ring]
  have h := @a_to_e 0 (2 * m + 3) (4 * m + 3) E
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Main transition combining both parities
theorem main_trans (d E : ℕ) :
    ⟨0, 0, 0, d, d + 2 + E⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 1, 2 * d + 4 + E⟩ := by
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    have h := main_trans_even m E
    convert h using 1; ring_nf
  · subst hm
    have h := main_trans_odd m E
    convert h using 1; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) → (0,0,0,0,2) in 1 step via R3
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  -- C(d, E) = (0, 0, 0, d, d+2+E), transition: C(d, E) →⁺ C(2d+1, E+1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, E⟩ ↦ ⟨0, 0, 0, d, d + 2 + E⟩) ⟨0, 0⟩
  intro ⟨d, E⟩
  exact ⟨⟨2 * d + 1, E + 1⟩, by convert main_trans d E using 1; ring_nf⟩

end Sz21_140_unofficial_38
