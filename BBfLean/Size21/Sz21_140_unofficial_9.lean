import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #9: [1/45, 25/77, 98/5, 3/7, 55/2]

Vector representation:
```
 0 -2 -1  0  0
 0  0  2 -1 -1
 1  0 -1  2  0
 0  1  0 -1  0
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_9

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R5/R1 pairs (even b)
theorem r5_r1_even : ∀ k, ∀ a e, ⟨a+k, 2*k, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih a (e + 1))
  ring_nf; finish

-- R5/R1 pairs (odd b)
theorem r5_r1_odd : ∀ k, ∀ a e, ⟨a+k, 2*k+1, 0, 0, e⟩ [fm]⊢* ⟨a, 1, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih a (e + 1))
  ring_nf; finish

-- R3 chain (b=0)
theorem r3_chain_b0 : ∀ k, ∀ a c d, ⟨a, 0, c+k, d, 0⟩ [fm]⊢* ⟨a+k, 0, c, d+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (a + 1) c (d + 2))
  ring_nf; finish

-- R3 chain (b=1)
theorem r3_chain_b1 : ∀ k, ∀ a c d, ⟨a, 1, c+k, d, 0⟩ [fm]⊢* ⟨a+k, 1, c, d+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (a + 1) c (d + 2))
  ring_nf; finish

-- R4 chain: d → b
theorem r4_chain : ∀ k, ∀ a b d, ⟨a, b, 0, d+k, 0⟩ [fm]⊢* ⟨a, b+k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a (b + 1) d)
  ring_nf; finish

-- R2R2R3 rounds (b=0)
theorem r2r2r3_b0 : ∀ m, ∀ A C E, ⟨A, 0, C, 2, E+2*m⟩ [fm]⊢* ⟨A+m, 0, C+3*m, 2, E⟩ := by
  intro m; induction' m with m ih <;> intro A C E
  · simp; exists 0
  rw [show E + 2 * (m + 1) = (E + 2 * m) + 2 from by ring]
  step fm; step fm
  rw [show C + 2 + 2 = (C + 3) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (A + 1) (C + 3) E)
  ring_nf; finish

-- R2R2R3 rounds (b=1)
theorem r2r2r3_b1 : ∀ m, ∀ A C E, ⟨A, 1, C, 2, E+2*m⟩ [fm]⊢* ⟨A+m, 1, C+3*m, 2, E⟩ := by
  intro m; induction' m with m ih <;> intro A C E
  · simp; exists 0
  rw [show E + 2 * (m + 1) = (E + 2 * m) + 2 from by ring]
  step fm; step fm
  rw [show C + 2 + 2 = (C + 3) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (A + 1) (C + 3) E)
  ring_nf; finish

-- Mid phase (odd e, b=0)
theorem mid_odd_b0 (m : ℕ) :
    ⟨A, 0, 0, 2, 2*m+1⟩ [fm]⊢* ⟨A+4*m+2, 6*m+5, 0, 0, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨A+m, 0, 3*m, 2, 1⟩)
  · have h := r2r2r3_b0 m A 0 1
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * m = 2 * m + 1 from by ring] at h; exact h
  step fm
  apply stepStar_trans (c₂ := ⟨A+4*m+2, 0, 0, 6*m+5, 0⟩)
  · have h := r3_chain_b0 (3*m+2) (A+m) 0 1
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  have h := r4_chain (6*m+5) (A+4*m+2) 0 0
  simp only [Nat.zero_add] at h; exact h

-- Mid phase (even e, b=0)
theorem mid_even_b0 (m : ℕ) :
    ⟨A, 0, 0, 2, 2*m⟩ [fm]⊢* ⟨A+4*m, 6*m+2, 0, 0, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨A+m, 0, 3*m, 2, 0⟩)
  · have h := r2r2r3_b0 m A 0 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (c₂ := ⟨A+4*m, 0, 0, 6*m+2, 0⟩)
  · have h := r3_chain_b0 (3*m) (A+m) 0 2
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  have h := r4_chain (6*m+2) (A+4*m) 0 0
  simp only [Nat.zero_add] at h; exact h

-- Mid phase (odd e, b=1)
theorem mid_odd_b1 (m : ℕ) :
    ⟨A, 1, 0, 2, 2*m+1⟩ [fm]⊢* ⟨A+4*m+2, 6*m+6, 0, 0, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨A+m, 1, 3*m, 2, 1⟩)
  · have h := r2r2r3_b1 m A 0 1
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * m = 2 * m + 1 from by ring] at h; exact h
  step fm
  apply stepStar_trans (c₂ := ⟨A+4*m+2, 1, 0, 6*m+5, 0⟩)
  · have h := r3_chain_b1 (3*m+2) (A+m) 0 1
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  have h := r4_chain (6*m+5) (A+4*m+2) 1 0
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_; ring_nf; finish

-- Mid phase (even e, b=1)
theorem mid_even_b1 (m : ℕ) :
    ⟨A, 1, 0, 2, 2*m⟩ [fm]⊢* ⟨A+4*m, 6*m+3, 0, 0, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨A+m, 1, 3*m, 2, 0⟩)
  · have h := r2r2r3_b1 m A 0 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (c₂ := ⟨A+4*m, 1, 0, 6*m+2, 0⟩)
  · have h := r3_chain_b1 (3*m) (A+m) 0 2
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  have h := r4_chain (6*m+2) (A+4*m) 1 0
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_; ring_nf; finish

-- b=4m transition
theorem main_ee (a m : ℕ) :
    ⟨a+2*m+1, 4*m, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+4*m+3, 6*m+5, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 0, 0, 2*m⟩)
  · have h := r5_r1_even (2*m) (a+1) 0
    simp only [Nat.zero_add] at h
    rw [show 2 * (2 * m) = 4 * m from by ring,
        show a + 1 + 2 * m = a + 2 * m + 1 from by ring] at h; exact h
  apply step_stepStar_stepPlus
  · show fm ⟨a+1, 0, 0, 0, 2*m⟩ = some ⟨a, 0, 1, 0, 2*m+1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨a+1, 0, 0, 2, 2*m+1⟩)
  · step fm; finish
  have h := @mid_odd_b0 (a+1) m
  rw [show a + 1 + 4 * m + 2 = a + 4 * m + 3 from by ring] at h; exact h

-- b=4m+2 transition
theorem main_eo (a m : ℕ) :
    ⟨a+2*m+2, 4*m+2, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+4*m+5, 6*m+8, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 0, 0, 2*m+1⟩)
  · have h := r5_r1_even (2*m+1) (a+1) 0
    simp only [Nat.zero_add] at h
    rw [show 2 * (2 * m + 1) = 4 * m + 2 from by ring,
        show a + 1 + (2 * m + 1) = a + 2 * m + 2 from by ring] at h; exact h
  apply step_stepStar_stepPlus
  · show fm ⟨a+1, 0, 0, 0, 2*m+1⟩ = some ⟨a, 0, 1, 0, 2*m+2⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨a+1, 0, 0, 2, 2*m+2⟩)
  · step fm; finish
  have h := @mid_even_b0 (a+1) (m+1)
  rw [show 2 * (m + 1) = 2 * m + 2 from by ring,
      show a + 1 + 4 * (m + 1) = a + 4 * m + 5 from by ring,
      show 6 * (m + 1) + 2 = 6 * m + 8 from by ring] at h; exact h

-- b=4m+1 transition
theorem main_oe (a m : ℕ) :
    ⟨a+2*m+1, 4*m+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+4*m+3, 6*m+6, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 1, 0, 0, 2*m⟩)
  · have h := r5_r1_odd (2*m) (a+1) 0
    simp only [Nat.zero_add] at h
    rw [show 2 * (2 * m) + 1 = 4 * m + 1 from by ring,
        show a + 1 + 2 * m = a + 2 * m + 1 from by ring] at h; exact h
  apply step_stepStar_stepPlus
  · show fm ⟨a+1, 1, 0, 0, 2*m⟩ = some ⟨a, 1, 1, 0, 2*m+1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨a+1, 1, 0, 2, 2*m+1⟩)
  · step fm; finish
  have h := @mid_odd_b1 (a+1) m
  rw [show a + 1 + 4 * m + 2 = a + 4 * m + 3 from by ring] at h; exact h

-- b=4m+3 transition
theorem main_oo (a m : ℕ) :
    ⟨a+2*m+2, 4*m+3, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+4*m+5, 6*m+9, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 1, 0, 0, 2*m+1⟩)
  · have h := r5_r1_odd (2*m+1) (a+1) 0
    simp only [Nat.zero_add] at h
    rw [show 2 * (2 * m + 1) + 1 = 4 * m + 3 from by ring,
        show a + 1 + (2 * m + 1) = a + 2 * m + 2 from by ring] at h; exact h
  apply step_stepStar_stepPlus
  · show fm ⟨a+1, 1, 0, 0, 2*m+1⟩ = some ⟨a, 1, 1, 0, 2*m+2⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨a+1, 1, 0, 2, 2*m+2⟩)
  · step fm; finish
  have h := @mid_even_b1 (a+1) (m+1)
  rw [show 2 * (m + 1) = 2 * m + 2 from by ring,
      show a + 1 + 4 * (m + 1) = a + 4 * m + 5 from by ring,
      show 6 * (m + 1) + 3 = 6 * m + 9 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 5, 0, 0, 0⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a b, q = ⟨a, b, 0, 0, 0⟩ ∧ a ≥ 2 ∧ b < 2 * a)
  · intro c ⟨a, b, hq, ha, hb⟩; subst hq
    rcases Nat.even_or_odd b with ⟨K, hK⟩ | ⟨K, hK⟩
    · rcases Nat.even_or_odd K with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hb4 : b = 4 * m := by omega
        subst hb4
        have hk : 2 * m < a := by omega
        have ha'_eq : a = (a - 2 * m - 1) + 2 * m + 1 := by omega
        rw [ha'_eq]
        exact ⟨_, ⟨_, _, rfl, by omega, by omega⟩, main_ee _ m⟩
      · have hb4 : b = 4 * m + 2 := by omega
        subst hb4
        have hk : 2 * m + 1 < a := by omega
        have ha'_eq : a = (a - 2 * m - 2) + 2 * m + 2 := by omega
        rw [ha'_eq]
        exact ⟨_, ⟨_, _, rfl, by omega, by omega⟩, main_eo _ m⟩
    · rcases Nat.even_or_odd K with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hb4 : b = 4 * m + 1 := by omega
        subst hb4
        have hk : 2 * m < a := by omega
        have ha'_eq : a = (a - 2 * m - 1) + 2 * m + 1 := by omega
        rw [ha'_eq]
        exact ⟨_, ⟨_, _, rfl, by omega, by omega⟩, main_oe _ m⟩
      · have hb4 : b = 4 * m + 3 := by omega
        subst hb4
        have hk : 2 * m + 1 < a := by omega
        have ha'_eq : a = (a - 2 * m - 2) + 2 * m + 2 := by omega
        rw [ha'_eq]
        exact ⟨_, ⟨_, _, rfl, by omega, by omega⟩, main_oo _ m⟩
  · exact ⟨3, 5, rfl, by omega, by omega⟩

end Sz21_140_unofficial_9
