import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz21_140_unofficial #19: [27/35, 5/33, 14/3, 11/7, 21/2]

Vector representation:
```
 0  3 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_19

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- d_to_e: move d to e
theorem d_to_e : ∀ k, ∀ a d e, ⟨a, 0, 0, d+k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- b_to_ad: move b to a and d
theorem b_to_ad : ∀ k, ∀ a b d, ⟨a, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+k, b, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- r3r1_pair: one (R3+R1) step
theorem r3r1_pair : ⟨a, b+1, c+1, 0, 0⟩ [fm]⊢* ⟨a+1, b+3, c, 0, 0⟩ := by
  step fm; step fm; finish

-- r3r1_chain: iterated (R3+R1)
theorem r3r1_chain : ∀ k, ∀ a b, ⟨a, b+1, k, 0, 0⟩ [fm]⊢* ⟨a+k, b+1+2*k, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  rw [show (k : ℕ) + 1 = k + 1 from rfl]
  apply stepStar_trans (@r3r1_pair a b k)
  rw [show b + 3 = (b + 2) + 1 from by ring]
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- bc_to_canonical: process b and c to canonical form
theorem bc_to_canonical : ∀ C, ∀ A B, ⟨A, B+1, C, 0, 0⟩ [fm]⊢* ⟨A+B+3*C+1, 0, 0, B+2*C+1, 0⟩ := by
  intro C A B
  apply stepStar_trans (r3r1_chain C A B)
  have h := b_to_ad (B+1+2*C) (A+C) 0 0
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- c_to_canonical: process c (when b=0) to canonical form
theorem c_to_canonical : ∀ C, ∀ A, ⟨A+1, 0, C+1, 0, 0⟩ [fm]⊢* ⟨A+3*C+4, 0, 0, 2*C+4, 0⟩ := by
  intro C A
  apply stepStar_trans (c₂ := ⟨A, 1, C+1, 1, 0⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 4, C, 0, 0⟩)
  · rw [show (C : ℕ) + 1 = C + 1 from rfl]; step fm; finish
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r3r1_chain C A 3)
  rw [show 3 + 1 + 2 * C = (2 * C + 4) from by ring]
  have h := b_to_ad (2*C+4) (A+C) 0 0
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- inner_round_c0: one inner round when C=0
theorem inner_round_c0 : ∀ A E, ⟨A+1, 0, 0, 0, E+4⟩ [fm]⊢* ⟨A, 0, 3, 0, E⟩ := by
  intro A E
  apply stepStar_trans (c₂ := ⟨A, 1, 0, 1, E + 4⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 0, 1, 1, E + 3⟩)
  · rw [show E + 4 = (E + 3) + 1 from by ring]; step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 3, 0, 0, E + 3⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 2, 1, 0, E + 2⟩)
  · rw [show E + 3 = (E + 2) + 1 from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 1, 2, 0, E + 1⟩)
  · rw [show E + 2 = (E + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm; finish
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show E + 1 = E + 1 from rfl]
  step fm; ring_nf; finish

-- inner_round_cpos: one inner round when C >= 1
theorem inner_round_cpos : ∀ A C E, ⟨A+1, 0, C+1, 0, E+4⟩ [fm]⊢* ⟨A, 0, C+4, 0, E⟩ := by
  intro A C E
  apply stepStar_trans (c₂ := ⟨A, 1, C+1, 1, E + 4⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 4, C, 0, E + 4⟩)
  · rw [show (C : ℕ) + 1 = C + 1 from rfl]; step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 3, C + 1, 0, E + 3⟩)
  · rw [show (4 : ℕ) = 3 + 1 from by ring,
        show E + 4 = (E + 3) + 1 from by ring]
    step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 2, C + 2, 0, E + 2⟩)
  · rw [show (3 : ℕ) = 2 + 1 from by ring,
        show E + 3 = (E + 2) + 1 from by ring]
    step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 1, C + 3, 0, E + 1⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring,
        show E + 2 = (E + 1) + 1 from by ring]
    step fm; finish
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show E + 1 = E + 1 from rfl]
  step fm; ring_nf; finish

-- inner_round: combined inner round
theorem inner_round : ∀ A C E, ⟨A+1, 0, C, 0, E+4⟩ [fm]⊢* ⟨A, 0, C+3, 0, E⟩ := by
  intro A C E
  rcases C with _ | C
  · exact inner_round_c0 A E
  · have h := inner_round_cpos A C E
    rw [show C + 4 = (C + 1) + 3 from by ring] at h
    exact h

-- inner_rounds: multiple inner rounds
theorem inner_rounds : ∀ q, ∀ A C E, ⟨A+q, 0, C, 0, E+4*q⟩ [fm]⊢* ⟨A, 0, C+3*q, 0, E⟩ := by
  intro q; induction' q with q ih <;> intro A C E
  · simp; exists 0
  rw [show A + (q + 1) = (A + q) + 1 from by ring,
      show E + 4 * (q + 1) = (E + 4 * q) + 4 from by ring]
  apply stepStar_trans (inner_round (A + q) C (E + 4 * q))
  apply stepStar_trans (ih A (C + 3) E)
  rw [show C + 3 + 3 * q = C + 3 * (q + 1) from by ring]
  finish

-- base_e1_c0: base case E=1, C=0
theorem base_e1_c0 : ∀ A, ⟨A+1, 0, 0, 0, 1⟩ [fm]⊢* ⟨A+3, 0, 0, 3, 0⟩ := by
  intro A
  step fm; step fm; step fm
  rw [show (3 : ℕ) = 0 + 3 from by ring]
  have h := b_to_ad 3 A 0 0
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- base_e2_c0: base case E=2, C=0
theorem base_e2_c0 : ∀ A, ⟨A+1, 0, 0, 0, 2⟩ [fm]⊢* ⟨A+5, 0, 0, 4, 0⟩ := by
  intro A
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; step fm
  rw [show (4 : ℕ) = 0 + 4 from by ring]
  have h := b_to_ad 4 (A+1) 0 0
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- base_e3_c0: base case E=3, C=0
theorem base_e3_c0 : ∀ A, ⟨A+1, 0, 0, 0, 3⟩ [fm]⊢* ⟨A+7, 0, 0, 5, 0⟩ := by
  intro A
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  step fm; step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; step fm
  rw [show (5 : ℕ) = 0 + 5 from by ring]
  have h := b_to_ad 5 (A+2) 0 0
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- base_e1_cpos: base case E=1, C >= 1
theorem base_e1_cpos : ∀ C A, ⟨A+1, 0, C+1, 0, 1⟩ [fm]⊢* ⟨A+3*C+6, 0, 0, 2*C+5, 0⟩ := by
  intro C A
  apply stepStar_trans (c₂ := ⟨A, 1, C+1, 1, 1⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 4, C, 0, 1⟩)
  · rw [show (C : ℕ) + 1 = C + 1 from rfl]; step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 3, C + 1, 0, 0⟩)
  · rw [show (4 : ℕ) = 3 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    step fm; ring_nf; finish
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  have h := bc_to_canonical (C+1) A 2
  refine stepStar_trans h ?_
  ring_nf; finish

-- base_e2_cpos: base case E=2, C >= 1
theorem base_e2_cpos : ∀ C A, ⟨A+1, 0, C+1, 0, 2⟩ [fm]⊢* ⟨A+3*C+8, 0, 0, 2*C+6, 0⟩ := by
  intro C A
  apply stepStar_trans (c₂ := ⟨A, 1, C+1, 1, 2⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 4, C, 0, 2⟩)
  · rw [show (C : ℕ) + 1 = C + 1 from rfl]; step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 3, C + 1, 0, 1⟩)
  · rw [show (4 : ℕ) = 3 + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
    step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 2, C + 2, 0, 0⟩)
  · rw [show (3 : ℕ) = 2 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    step fm; ring_nf; finish
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  have h := bc_to_canonical (C+2) A 1
  refine stepStar_trans h ?_
  ring_nf; finish

-- base_e3_cpos: base case E=3, C >= 1
theorem base_e3_cpos : ∀ C A, ⟨A+1, 0, C+1, 0, 3⟩ [fm]⊢* ⟨A+3*C+10, 0, 0, 2*C+7, 0⟩ := by
  intro C A
  apply stepStar_trans (c₂ := ⟨A, 1, C+1, 1, 3⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 4, C, 0, 3⟩)
  · rw [show (C : ℕ) + 1 = C + 1 from rfl]; step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 3, C + 1, 0, 2⟩)
  · rw [show (4 : ℕ) = 3 + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
    step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 2, C + 2, 0, 1⟩)
  · rw [show (3 : ℕ) = 2 + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
    step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 1, C + 3, 0, 0⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    step fm; ring_nf; finish
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  have h := bc_to_canonical (C+3) A 0
  refine stepStar_trans h ?_
  ring_nf; finish

-- main_trans: main transition with invariant preservation
theorem main_trans (a d : ℕ) (hBound : 4 * (a + 1) ≥ d + 1) :
    ∃ a' d', (⟨a+1, 0, 0, d, 0⟩ : Q) [fm]⊢⁺ ⟨a'+1, 0, 0, d', 0⟩ ∧ 4 * (a' + 1) ≥ d' + 1 := by
  rcases d with _ | d
  · refine ⟨a, 2, ?_, by omega⟩
    apply step_stepStar_stepPlus (c₂ := ⟨a, 1, 0, 1, 0⟩)
    · show fm ⟨a + 1, 0, 0, 0, 0⟩ = some ⟨a, 1, 0, 1, 0⟩; simp [fm]
    step fm; finish
  · obtain ⟨q, r, hr_lt, hdr⟩ : ∃ q r, r < 4 ∧ d + 1 = r + 4 * q := by
      exact ⟨(d+1)/4, (d+1)%4, Nat.mod_lt _ (by omega), by omega⟩
    have haq : a + 1 ≥ q + 1 := by omega
    have hA_val : a + 1 - q ≥ 1 := by omega
    -- Phase 1: d_to_e
    have h1 : (⟨a+1, 0, 0, d+1, 0⟩ : Q) [fm]⊢* ⟨a+1, 0, 0, 0, d+1⟩ := by
      have h := d_to_e (d+1) (a+1) 0 0
      simp only [Nat.zero_add] at h; exact h
    -- Phase 2: inner_rounds
    rw [hdr] at h1
    rw [show a + 1 = (a + 1 - q) + q from by omega] at h1
    have h2 := inner_rounds q (a + 1 - q) 0 r
    have h12' := stepStar_trans h1 h2
    simp only [Nat.zero_add] at h12'
    rw [show (a + 1 - q) + q = a + 1 from by omega] at h12'
    rw [show a + 1 - q = (a - q) + 1 from by omega] at h12'
    rw [hdr]
    -- Phase 3: base case by remainder
    rcases Nat.eq_zero_or_pos r with hr0 | hr_pos
    · subst hr0; simp only [Nat.zero_add] at h12' ⊢
      have hq_pos : q ≥ 1 := by omega
      rw [show 3 * q = (3 * q - 1) + 1 from by omega] at h12'
      have h_c := c_to_canonical (3 * q - 1) (a - q)
      have h_all := stepStar_trans h12' h_c
      refine ⟨(a - q) + 3 * (3 * q - 1) + 3, 2 * (3 * q - 1) + 4, ?_, ?_⟩
      · rw [show (a - q) + 3 * (3 * q - 1) + 3 + 1 = (a - q) + 3 * (3 * q - 1) + 4 from by ring]
        exact stepStar_stepPlus h_all (by simp [Q]; omega)
      · omega
    · rcases Nat.eq_zero_or_pos q with hq0 | hq_pos
      · subst hq0; simp only [Nat.sub_zero, Nat.mul_zero, Nat.add_zero] at h12' ⊢
        have : r ≥ 1 := hr_pos; have : r ≤ 3 := by omega
        interval_cases r
        · refine ⟨a + 2, 3, ?_, by omega⟩
          rw [show a + 2 + 1 = a + 3 from by ring]
          exact stepStar_stepPlus_stepPlus h12'
            (stepStar_stepPlus (base_e1_c0 a) (by simp [Q]))
        · refine ⟨a + 4, 4, ?_, by omega⟩
          rw [show a + 4 + 1 = a + 5 from by ring]
          exact stepStar_stepPlus_stepPlus h12'
            (stepStar_stepPlus (base_e2_c0 a) (by simp [Q]))
        · refine ⟨a + 6, 5, ?_, by omega⟩
          rw [show a + 6 + 1 = a + 7 from by ring]
          exact stepStar_stepPlus_stepPlus h12'
            (stepStar_stepPlus (base_e3_c0 a) (by simp [Q]))
      · rw [show 3 * q = (3 * q - 1) + 1 from by omega] at h12'
        have hr_ge : r ≥ 1 := hr_pos
        interval_cases r
        · have h_b := base_e1_cpos (3 * q - 1) (a - q)
          have h_all := stepStar_trans h12' h_b
          refine ⟨(a - q) + 3 * (3 * q - 1) + 5, 2 * (3 * q - 1) + 5, ?_, ?_⟩
          · rw [show (a - q) + 3 * (3 * q - 1) + 5 + 1 = (a - q) + 3 * (3 * q - 1) + 6 from by ring]
            exact stepStar_stepPlus h_all (by simp [Q]; omega)
          · omega
        · have h_b := base_e2_cpos (3 * q - 1) (a - q)
          have h_all := stepStar_trans h12' h_b
          refine ⟨(a - q) + 3 * (3 * q - 1) + 7, 2 * (3 * q - 1) + 6, ?_, ?_⟩
          · rw [show (a - q) + 3 * (3 * q - 1) + 7 + 1 = (a - q) + 3 * (3 * q - 1) + 8 from by ring]
            exact stepStar_stepPlus h_all (by simp [Q]; omega)
          · omega
        · have h_b := base_e3_cpos (3 * q - 1) (a - q)
          have h_all := stepStar_trans h12' h_b
          refine ⟨(a - q) + 3 * (3 * q - 1) + 9, 2 * (3 * q - 1) + 7, ?_, ?_⟩
          · rw [show (a - q) + 3 * (3 * q - 1) + 9 + 1 = (a - q) + 3 * (3 * q - 1) + 10 from by ring]
            exact stepStar_stepPlus h_all (by simp [Q]; omega)
          · omega

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a+1, 0, 0, d, 0⟩ ∧ 4 * (a + 1) ≥ d + 1)
  · intro c ⟨a, d, hc, hBound⟩
    subst hc
    have ⟨a', d', h_plus, h_inv⟩ := main_trans a d hBound
    exact ⟨⟨a'+1, 0, 0, d', 0⟩, ⟨a', d', rfl, h_inv⟩, h_plus⟩
  · exact ⟨0, 0, rfl, by omega⟩
