import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #21: [28/15, 3/22, 175/2, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  1  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_21

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: (0,0,c,d+k,e) →* (0,0,c,d,e+k)
theorem d_to_e : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R1/R2 chain: (a, 1, k+1, d, E+k+1) →* (a+k+2, 0, 0, d+k+1, E+1)
theorem r1r2_chain : ∀ k, ∀ a d E, ⟨a, 1, k + 1, d, E + k + 1⟩ [fm]⊢* ⟨a + k + 2, 0, 0, d + k + 1, E + 1⟩ := by
  intro k; induction' k with k h <;> intro a d E
  · step fm; ring_nf; finish
  rw [show k + 1 + 1 = (k + 1) + 1 from by ring,
      show E + (k + 1) + 1 = E + (k + 1) + 1 from rfl]
  step fm
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2 repeated: (a+k, b, 0, d, k) →* (a, b+k, 0, d, 0)
theorem a_e_to_b : ∀ k, ∀ a b d, ⟨a + k, b, 0, d, k⟩ [fm]⊢* ⟨a, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3R1R1 rounds (even b): (A+1, 2*k, 0, D, 0) →* (A+1+3*k, 0, 0, D+3*k, 0)
theorem r3r1r1_even : ∀ k, ∀ A D, ⟨A + 1, 2 * k, 0, D, 0⟩ [fm]⊢* ⟨A + 1 + 3 * k, 0, 0, D + 3 * k, 0⟩ := by
  intro k; induction' k with k h <;> intro A D
  · simp; exists 0
  rw [show 2 * (k + 1) = (2 * k) + 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show A + 4 = (A + 3) + 1 from by ring]
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3R1R1 rounds (odd b): (A+1, 2*k+1, 0, D, 0) →* (A+1+3*k, 1, 0, D+3*k, 0)
theorem r3r1r1_odd : ∀ k, ∀ A D, ⟨A + 1, 2 * k + 1, 0, D, 0⟩ [fm]⊢* ⟨A + 1 + 3 * k, 1, 0, D + 3 * k, 0⟩ := by
  intro k; induction' k with k h <;> intro A D
  · simp; exists 0
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show A + 4 = (A + 3) + 1 from by ring]
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3 repeated: (a+k, 0, c, d, 0) →* (a, 0, c+2*k, d+k, 0)
theorem a_to_c : ∀ k, ∀ a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d + k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · simp; exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition (even case): c = C+2M+3, d = C+4M+3 (n = d-c = 2M)
-- (0, 0, C+2M+3, C+4M+3, 0) →⁺ (0, 0, 2C+6M+8, 2C+8M+9, 0)
theorem main_trans_even (C M : ℕ) :
    ⟨0, 0, C + 2 * M + 3, C + 4 * M + 3, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * C + 6 * M + 8, 2 * C + 8 * M + 9, 0⟩ := by
  -- Phase A: R4 x (C+4M+3)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, C + 2 * M + 3, 0, C + 4 * M + 3⟩)
  · have h1 := @d_to_e (C + 4 * M + 3) (C + 2 * M + 3) 0 0
    simp only [Nat.zero_add] at h1; convert h1 using 2
  -- Phase B: R5
  apply step_stepStar_stepPlus
    (c₂ := ⟨0, 1, C + 2 * M + 2, 0, C + 4 * M + 3⟩)
  · show fm ⟨0, 0, (C + 2 * M + 2) + 1, 0, C + 4 * M + 3⟩ =
         some ⟨0, 1, C + 2 * M + 2, 0, C + 4 * M + 3⟩
    simp [fm]
  -- Phase B': R1/R2 chain: →* (C+2M+3, 0, 0, C+2M+2, 2M+2)
  apply stepStar_trans (c₂ := ⟨C + 2 * M + 3, 0, 0, C + 2 * M + 2, 2 * M + 2⟩)
  · have h2 := @r1r2_chain (C + 2 * M + 1) 0 0 (2 * M + 1)
    convert h2 using 2; ring_nf
  -- Phase C: R2 x (2M+2): →* (C+1, 2M+2, 0, C+2M+2, 0)
  apply stepStar_trans (c₂ := ⟨C + 1, 2 * M + 2, 0, C + 2 * M + 2, 0⟩)
  · have h3 := @a_e_to_b (2 * M + 2) (C + 1) 0 (C + 2 * M + 2)
    convert h3 using 2; ring_nf
  -- Phase D: R3R1R1 even (M+1 rounds): →* (C+3M+4, 0, 0, C+5M+5, 0)
  apply stepStar_trans (c₂ := ⟨C + 3 * M + 4, 0, 0, C + 5 * M + 5, 0⟩)
  · rw [show 2 * M + 2 = 2 * (M + 1) from by ring]
    have h4 := @r3r1r1_even (M + 1) C (C + 2 * M + 2)
    convert h4 using 2; ring_nf
  -- Phase E: R3 drain
  have h5 := @a_to_c (C + 3 * M + 4) 0 0 (C + 5 * M + 5)
  simp only [Nat.zero_add] at h5
  refine stepStar_trans h5 ?_; ring_nf; finish

-- Main transition (odd case): c = C+2M+4, d = C+4M+5 (n = d-c = 2M+1)
-- (0, 0, C+2M+4, C+4M+5, 0) →⁺ (0, 0, 2C+6M+11, 2C+8M+13, 0)
theorem main_trans_odd (C M : ℕ) :
    ⟨0, 0, C + 2 * M + 4, C + 4 * M + 5, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * C + 6 * M + 11, 2 * C + 8 * M + 13, 0⟩ := by
  -- Phase A: R4
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, C + 2 * M + 4, 0, C + 4 * M + 5⟩)
  · have h1 := @d_to_e (C + 4 * M + 5) (C + 2 * M + 4) 0 0
    simp only [Nat.zero_add] at h1; convert h1 using 2
  -- Phase B: R5
  apply step_stepStar_stepPlus
    (c₂ := ⟨0, 1, C + 2 * M + 3, 0, C + 4 * M + 5⟩)
  · show fm ⟨0, 0, (C + 2 * M + 3) + 1, 0, C + 4 * M + 5⟩ =
         some ⟨0, 1, C + 2 * M + 3, 0, C + 4 * M + 5⟩
    simp [fm]
  -- Phase B': R1/R2 chain: →* (C+2M+4, 0, 0, C+2M+3, 2M+3)
  apply stepStar_trans (c₂ := ⟨C + 2 * M + 4, 0, 0, C + 2 * M + 3, 2 * M + 3⟩)
  · have h2 := @r1r2_chain (C + 2 * M + 2) 0 0 (2 * M + 2)
    convert h2 using 2; ring_nf
  -- Phase C: R2 x (2M+3): →* (C+1, 2M+3, 0, C+2M+3, 0)
  apply stepStar_trans (c₂ := ⟨C + 1, 2 * M + 3, 0, C + 2 * M + 3, 0⟩)
  · have h3 := @a_e_to_b (2 * M + 3) (C + 1) 0 (C + 2 * M + 3)
    convert h3 using 2; ring_nf
  -- Phase D: R3R1R1 odd (M+1 rounds): →* (C+3M+4, 1, 0, C+5M+6, 0)
  apply stepStar_trans (c₂ := ⟨C + 3 * M + 4, 1, 0, C + 5 * M + 6, 0⟩)
  · rw [show 2 * M + 3 = 2 * (M + 1) + 1 from by ring]
    have h4 := @r3r1r1_odd (M + 1) C (C + 2 * M + 3)
    convert h4 using 2; ring_nf
  -- Phase D': R3 R1 R3: →* (C+3M+4, 0, 3, C+5M+9, 0)
  apply stepStar_trans (c₂ := ⟨C + 3 * M + 4, 0, 3, C + 5 * M + 9, 0⟩)
  · rw [show C + 3 * M + 4 = (C + 3 * M + 3) + 1 from by ring]
    step fm  -- R3
    rw [show C + 5 * M + 6 + 1 = (C + 5 * M + 7) from by ring]
    step fm  -- R1
    rw [show C + 3 * M + 3 + 2 = (C + 3 * M + 4) + 1 from by ring,
        show C + 5 * M + 7 + 1 = C + 5 * M + 8 from by ring]
    step fm  -- R3
    ring_nf; finish
  -- Phase E: R3 drain
  have h5 := @a_to_c (C + 3 * M + 4) 0 3 (C + 5 * M + 9)
  simp only [Nat.zero_add] at h5
  refine stepStar_trans h5 ?_; ring_nf; finish

-- Combined main transition
theorem main_trans (c d : ℕ) (hc : c ≥ 5) (hd : d ≥ c) (hcd : 2 * c ≥ d + 3) :
    ⟨0, 0, c, d, 0⟩ [fm]⊢⁺ ⟨0, 0, c + d + 2, 2 * d + 3, 0⟩ := by
  rcases Nat.even_or_odd (d - c) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hd_eq : d = c + 2 * m := by omega
    subst hd_eq
    obtain ⟨C, rfl⟩ : ∃ C, c = C + (2 * m + 3) := ⟨c - (2 * m + 3), by omega⟩
    have := main_trans_even C m
    convert this using 1; ring_nf
  · have hd_eq : d = c + 2 * m + 1 := by omega
    subst hd_eq
    obtain ⟨C, rfl⟩ : ∃ C, c = C + (2 * m + 4) := ⟨c - (2 * m + 4), by omega⟩
    have := main_trans_odd C m
    convert this using 1; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 5, 0⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c, d, 0⟩ ∧ c ≥ 5 ∧ d ≥ c ∧ 2 * c ≥ d + 3)
  · intro q ⟨c, d, hq, hc, hd, hcd⟩
    subst hq
    exact ⟨⟨0, 0, c + d + 2, 2 * d + 3, 0⟩,
           ⟨c + d + 2, 2 * d + 3, rfl, by omega, by omega, by omega⟩,
           main_trans c d hc hd hcd⟩
  · exact ⟨5, 5, rfl, by omega, by omega, by omega⟩
