import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz21_140_unofficial #79: [5/6, 4/35, 77/2, 9/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  1  1
 0  2  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_79

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R3 chain: a → d,e
theorem r3_chain : ∀ k, ∀ a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+k, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 chain: d → b
theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3/R2 chain: c → a,e
theorem r3r2_chain : ∀ k, ∀ a c e, ⟨a+1, 0, c+k, 0, e⟩ [fm]⊢* ⟨a+1+k, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Middle round: 5 steps, b -= 3, c += 2, e -= 1
theorem middle_round : ∀ b c E, ⟨0, b+3, c, 0, E+1⟩ [fm]⊢* ⟨0, b, c+2, 0, E⟩ := by
  intro b c E
  step fm; step fm; step fm; step fm; step fm
  finish

-- Middle rounds by induction
theorem middle_rounds : ∀ k, ∀ b c E, ⟨0, b+3*k, c, 0, E+k⟩ [fm]⊢* ⟨0, b, c+2*k, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro b c E
  · exists 0
  rw [show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring,
      show E + (k + 1) = (E + 1) + k from by ring]
  apply stepStar_trans (ih _ _ _)
  have hr := middle_round b (c + 2 * k) E
  rw [show c + 2 * k + 2 = c + 2 * (k + 1) from by ring] at hr
  exact hr

-- Tail for b_rem=0
theorem tail0 (c E : ℕ) : ⟨0, 0, c+1, 0, E+1⟩ [fm]⊢⁺ ⟨c+3, 0, 0, 0, E+c⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨1, 0, c+1, 1, E⟩)
  · show fm ⟨0, 0, c+1, 0, E+1⟩ = some ⟨1, 0, c+1, 1, E⟩; simp [fm]
  apply stepStar_trans
  · have : fm ⟨1, 0, c+1, 1, E⟩ = some ⟨3, 0, c, 0, E⟩ := by simp [fm]
    exact step_stepStar this
  have h := r3r2_chain c 2 0 E
  simp at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Tail for b_rem=1
theorem tail1 (c E : ℕ) : ⟨0, 1, c, 0, E+1⟩ [fm]⊢⁺ ⟨c+2, 0, 0, 0, E+c⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨1, 1, c, 1, E⟩)
  · show fm ⟨0, 1, c, 0, E+1⟩ = some ⟨1, 1, c, 1, E⟩; simp [fm]
  apply stepStar_trans
  · have : fm ⟨1, 1, c, 1, E⟩ = some ⟨0, 0, c+1, 1, E⟩ := by simp [fm]
    exact step_stepStar this
  apply stepStar_trans
  · have : fm ⟨0, 0, c+1, 1, E⟩ = some ⟨2, 0, c, 0, E⟩ := by simp [fm]
    exact step_stepStar this
  have h := r3r2_chain c 1 0 E
  simp at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Tail for b_rem=2
theorem tail2 (c E : ℕ) : ⟨0, 2, c, 0, E+1⟩ [fm]⊢⁺ ⟨c+2, 0, 0, 0, E+1+c⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨1, 2, c, 1, E⟩)
  · show fm ⟨0, 2, c, 0, E+1⟩ = some ⟨1, 2, c, 1, E⟩; simp [fm]
  apply stepStar_trans
  · have : fm ⟨1, 2, c, 1, E⟩ = some ⟨0, 1, c+1, 1, E⟩ := by simp [fm]
    exact step_stepStar this
  apply stepStar_trans
  · have : fm ⟨0, 1, c+1, 1, E⟩ = some ⟨2, 1, c, 0, E⟩ := by simp [fm]
    exact step_stepStar this
  apply stepStar_trans
  · have : fm ⟨2, 1, c, 0, E⟩ = some ⟨1, 0, c+1, 0, E⟩ := by simp [fm]
    exact step_stepStar this
  apply stepStar_trans
  · have : fm ⟨1, 0, c+1, 0, E⟩ = some ⟨0, 0, c+1, 1, E+1⟩ := by simp [fm]
    exact step_stepStar this
  apply stepStar_trans
  · have : fm ⟨0, 0, c+1, 1, E+1⟩ = some ⟨2, 0, c, 0, E+1⟩ := by simp [fm]
    exact step_stepStar this
  have h := r3r2_chain c 1 0 (E+1)
  simp at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Case a ≡ 0 (mod 3): a = 3(m+1)
theorem case_mod0 (m e : ℕ) : ⟨3*m+3, 0, 0, 0, e+1⟩ [fm]⊢⁺ ⟨4*m+6, 0, 0, 0, e+5*m+4⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 3*m+3, e+3*m+4⟩)
  · have h := r3_chain (3*m+3) 0 0 (e+1)
    simp at h; rw [show e + 1 + (3 * m + 3) = e + 3 * m + 4 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 6*m+6, 0, 0, e+3*m+4⟩)
  · have h := r4_chain (3*m+3) 0 0 (e+3*m+4)
    simp at h; rw [show 2 * (3 * m + 3) = 6 * m + 6 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 4*m+4, 0, e+m+2⟩)
  · have h := middle_rounds (2*m+2) 0 0 (e+m+2)
    simp at h
    rw [show 3 * (2 * m + 2) = 6 * m + 6 from by ring,
        show e + m + 2 + (2 * m + 2) = e + 3 * m + 4 from by ring,
        show 2 * (2 * m + 2) = 4 * m + 4 from by ring] at h; exact h
  rw [show (4 : ℕ) * m + 4 = (4 * m + 3) + 1 from by ring,
      show e + m + 2 = (e + m + 1) + 1 from by omega,
      show (4 : ℕ) * m + 6 = (4 * m + 3) + 3 from by ring,
      show e + 5 * m + 4 = (e + m + 1) + (4 * m + 3) from by ring]
  exact tail0 (4*m+3) (e+m+1)

-- Case a ≡ 1 (mod 3): a = 3m+4
theorem case_mod1 (m e : ℕ) : ⟨3*m+4, 0, 0, 0, e+1⟩ [fm]⊢⁺ ⟨4*m+6, 0, 0, 0, e+5*m+7⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 3*m+4, e+3*m+5⟩)
  · have h := r3_chain (3*m+4) 0 0 (e+1)
    simp at h; rw [show e + 1 + (3 * m + 4) = e + 3 * m + 5 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 6*m+8, 0, 0, e+3*m+5⟩)
  · have h := r4_chain (3*m+4) 0 0 (e+3*m+5)
    simp at h; rw [show 2 * (3 * m + 4) = 6 * m + 8 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2, 4*m+4, 0, e+m+3⟩)
  · have h := middle_rounds (2*m+2) 2 0 (e+m+3)
    simp at h
    rw [show 2 + 3 * (2 * m + 2) = 6 * m + 8 from by ring,
        show e + m + 3 + (2 * m + 2) = e + 3 * m + 5 from by ring,
        show 2 * (2 * m + 2) = 4 * m + 4 from by ring] at h; exact h
  rw [show e + m + 3 = (e + m + 2) + 1 from by omega,
      show (4 : ℕ) * m + 6 = (4 * m + 4) + 2 from by ring,
      show e + 5 * m + 7 = (e + m + 2) + 1 + (4 * m + 4) from by ring]
  exact tail2 (4*m+4) (e+m+2)

-- Case a ≡ 2 (mod 3): a = 3m+2
theorem case_mod2 (m e : ℕ) : ⟨3*m+2, 0, 0, 0, e+1⟩ [fm]⊢⁺ ⟨4*m+4, 0, 0, 0, e+5*m+3⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 3*m+2, e+3*m+3⟩)
  · have h := r3_chain (3*m+2) 0 0 (e+1)
    simp at h; rw [show e + 1 + (3 * m + 2) = e + 3 * m + 3 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 6*m+4, 0, 0, e+3*m+3⟩)
  · have h := r4_chain (3*m+2) 0 0 (e+3*m+3)
    simp at h; rw [show 2 * (3 * m + 2) = 6 * m + 4 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, 4*m+2, 0, e+m+2⟩)
  · have h := middle_rounds (2*m+1) 1 0 (e+m+2)
    simp at h
    rw [show 1 + 3 * (2 * m + 1) = 6 * m + 4 from by ring,
        show e + m + 2 + (2 * m + 1) = e + 3 * m + 3 from by ring,
        show 2 * (2 * m + 1) = 4 * m + 2 from by ring] at h; exact h
  rw [show e + m + 2 = (e + m + 1) + 1 from by omega,
      show (4 : ℕ) * m + 4 = (4 * m + 2) + 2 from by ring,
      show e + 5 * m + 3 = (e + m + 1) + (4 * m + 2) from by ring]
  exact tail1 (4*m+2) (e+m+1)

-- Combined transition
theorem main_trans : ∀ a e, a ≥ 2 → e ≥ 1 →
    ∃ a' e', a' ≥ 2 ∧ e' ≥ 1 ∧ ⟨a, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a', 0, 0, 0, e'⟩ := by
  intro a e ha he
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hmod := Nat.div_add_mod a 3
  set q := a / 3
  set r := a % 3
  have hr : r < 3 := Nat.mod_lt a (by omega)
  interval_cases r
  · rcases q with _ | k
    · omega
    rw [show a = 3 * k + 3 from by omega]
    exact ⟨4*k+6, e'+5*k+4, by omega, by omega, case_mod0 k e'⟩
  · rcases q with _ | k
    · omega
    rw [show a = 3 * k + 4 from by omega]
    exact ⟨4*k+6, e'+5*k+7, by omega, by omega, case_mod1 k e'⟩
  · rw [show a = 3 * q + 2 from by omega]
    exact ⟨4*q+4, e'+5*q+3, by omega, by omega, case_mod2 q e'⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 2 ∧ e ≥ 1)
  · intro c ⟨a, e, hq, ha, he⟩; subst hq
    obtain ⟨a', e', ha', he', htrans⟩ := main_trans a e ha he
    exact ⟨⟨a', 0, 0, 0, e'⟩, ⟨a', e', rfl, ha', he'⟩, htrans⟩
  · exact ⟨2, 1, rfl, by omega, by omega⟩
