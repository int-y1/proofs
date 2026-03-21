import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz21_140_unofficial #126: [9/10, 4/21, 77/2, 5/7, 14/11]

Vector representation:
```
-1  2 -1  0  0
 2 -1  0 -1  0
-1  0  0  1  1
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_126

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R3 chain: drain a into d,e
theorem r3_chain : ∀ k, ∀ a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+k, e+k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 chain: drain d into c
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c+k, d, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3,R2 chain: drain b into a,e
theorem r3r2_chain : ∀ k, ∀ a e, ⟨a+1, k, 0, 0, e⟩ [fm]⊢* ⟨a+1+k, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- 5-step round: R5, R1, R2, R1, R1
theorem five_step_round : ∀ k, ∀ b c e, ⟨0, b, c+3*k, 0, e+k⟩ [fm]⊢* ⟨0, b+5*k, c, 0, e⟩ := by
  intro k; induction' k with k h <;> intro b c e
  · exists 0
  rw [show c + 3 * (k + 1) = (c + 3 * k) + 2 + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  rw [show (c + 3 * k) + 2 + 1 = ((c + 3 * k) + 2) + 1 from by ring]
  step fm
  step fm
  rw [show (c + 3 * k) + 2 = (c + 3 * k + 1) + 1 from by ring]
  step fm
  rw [show c + 3 * k + 1 = (c + 3 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Tail for c=1
theorem tail_c1 : ∀ b e, ⟨0, b, 1, 0, e+1⟩ [fm]⊢* ⟨2, b+1, 0, 0, e⟩ := by
  intro b e
  step fm
  step fm
  step fm
  finish

-- Tail for c=2
theorem tail_c2 : ∀ b e, ⟨0, b, 2, 0, e+1⟩ [fm]⊢* ⟨1, b+3, 0, 0, e⟩ := by
  intro b e
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  step fm
  step fm
  step fm
  finish

-- Case a = 3k+1
theorem trans_mod1 : ∀ k, ∀ e, ⟨3*k+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨5*k+3, 0, 0, 0, 7*k+e+1⟩ := by
  intro k e
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 3*k+1, e+(3*k+1)⟩)
  · have h := r3_chain (3*k+1) 0 0 e; simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3*k+1, 0, e+(3*k+1)⟩)
  · have h := r4_chain (3*k+1) 0 0 (e+(3*k+1)); simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 5*k, 1, 0, e+2*k+1⟩)
  · have h := five_step_round k 0 1 (e+2*k+1)
    rw [show 1 + 3 * k = 3 * k + 1 from by ring,
        show e + 2 * k + 1 + k = e + (3 * k + 1) from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 5*k+1, 0, 0, e+2*k⟩)
  · rw [show e + 2 * k + 1 = (e + 2 * k) + 1 from by ring]
    have h := tail_c1 (5*k) (e+2*k)
    rw [show 5 * k + 1 = 5 * k + 1 from rfl] at h; exact h
  apply step_stepStar_stepPlus
  · show fm ⟨2, 5*k+1, 0, 0, e+2*k⟩ = some ⟨1, 5*k+1, 0, 1, e+2*k+1⟩
    rw [show (2 : ℕ) = 1 + 1 from rfl]; simp [fm]
  rw [show 5 * k + 1 = (5 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨5*k+3, 0, 0, 0, 7*k+e+1⟩)
  · have h := r3r2_chain (5*k) 2 (e+2*k+1)
    rw [show 2 + 1 + 5 * k = 5 * k + 3 from by ring,
        show e + 2 * k + 1 + 5 * k = 7 * k + e + 1 from by ring] at h
    exact h
  finish

-- Case a = 3k+2
theorem trans_mod2 : ∀ k, ∀ e, ⟨3*k+2, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨5*k+4, 0, 0, 0, 7*k+e+4⟩ := by
  intro k e
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 3*k+2, e+(3*k+2)⟩)
  · have h := r3_chain (3*k+2) 0 0 e; simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3*k+2, 0, e+(3*k+2)⟩)
  · have h := r4_chain (3*k+2) 0 0 (e+(3*k+2)); simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 5*k, 2, 0, e+2*k+2⟩)
  · have h := five_step_round k 0 2 (e+2*k+2)
    rw [show 2 + 3 * k = 3 * k + 2 from by ring,
        show e + 2 * k + 2 + k = e + (3 * k + 2) from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 5*k+3, 0, 0, e+2*k+1⟩)
  · rw [show e + 2 * k + 2 = (e + 2 * k + 1) + 1 from by ring]
    have h := tail_c2 (5*k) (e+2*k+1)
    rw [show 5 * k + 3 = 5 * k + 3 from rfl] at h; exact h
  apply step_stepStar_stepPlus
  · show fm ⟨1, 5*k+3, 0, 0, e+2*k+1⟩ = some ⟨0, 5*k+3, 0, 1, e+2*k+2⟩
    simp [fm]
  rw [show 5 * k + 3 = (5 * k + 2) + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨5*k+4, 0, 0, 0, 7*k+e+4⟩)
  · have h := r3r2_chain (5*k+2) 1 (e+2*k+2)
    rw [show 1 + 1 + (5 * k + 2) = 5 * k + 4 from by ring,
        show e + 2 * k + 2 + (5 * k + 2) = 7 * k + e + 4 from by ring] at h
    exact h
  finish

-- Case a = 3(k+1)
theorem trans_mod0 : ∀ k, ∀ e, ⟨3*k+3, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨5*k+7, 0, 0, 0, 7*k+e+5⟩ := by
  intro k e
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 3*k+3, e+(3*k+3)⟩)
  · have h := r3_chain (3*k+3) 0 0 e; simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3*k+3, 0, e+(3*k+3)⟩)
  · have h := r4_chain (3*k+3) 0 0 (e+(3*k+3)); simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 5*k+5, 0, 0, e+2*k+2⟩)
  · have h := five_step_round (k+1) 0 0 (e+2*k+2)
    rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring,
        show e + 2 * k + 2 + (k + 1) = e + (3 * k + 3) from by ring,
        show 5 * (k + 1) = 5 * k + 5 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  rw [show e + 2 * k + 2 = (e + 2 * k + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨3, 5*k+4, 0, 0, e+2*k+1⟩)
  · rw [show 5 * k + 5 = (5 * k + 4) + 1 from by ring]
    step fm
    rw [show (5 * k + 4) + 1 = (5 * k + 4) + 1 from rfl]
    step fm
    finish
  apply step_stepStar_stepPlus
  · show fm ⟨3, 5*k+4, 0, 0, e+2*k+1⟩ = some ⟨2, 5*k+4, 0, 1, e+2*k+2⟩
    rw [show (3 : ℕ) = 2 + 1 from rfl]; simp [fm]
  rw [show 5 * k + 4 = (5 * k + 3) + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨5*k+7, 0, 0, 0, 7*k+e+5⟩)
  · have h := r3r2_chain (5*k+3) 3 (e+2*k+2)
    rw [show 3 + 1 + (5 * k + 3) = 5 * k + 7 from by ring,
        show e + 2 * k + 2 + (5 * k + 3) = 7 * k + e + 5 from by ring] at h
    exact h
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 1)
  · intro c ⟨a, e, hq, ha⟩
    subst hq
    have hdiv := (Nat.div_add_mod a 3).symm
    set r := a % 3
    have hr : r < 3 := Nat.mod_lt _ (by omega)
    interval_cases r
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ a / 3)
      rw [show a = 3 * k + 3 from by omega]
      exact ⟨_, ⟨5*k+7, 7*k+e+5, rfl, by omega⟩, trans_mod0 k e⟩
    · rw [show a = 3 * (a / 3) + 1 from by omega]
      exact ⟨_, ⟨5*(a/3)+3, 7*(a/3)+e+1, rfl, by omega⟩, trans_mod1 (a/3) e⟩
    · rw [show a = 3 * (a / 3) + 2 from by omega]
      exact ⟨_, ⟨5*(a/3)+4, 7*(a/3)+e+4, rfl, by omega⟩, trans_mod2 (a/3) e⟩
  · exact ⟨1, 0, rfl, by omega⟩
