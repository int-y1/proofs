import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz21_140_unofficial #53: [35/6, 55/2, 8/77, 3/5, 7/3]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  1
 3  0  0 -1 -1
 0  1 -1  0  0
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_53

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- c_to_b: move c to b
theorem c_to_b : ∀ k, ∀ b c e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k h <;> intro b c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- r2_chain: move a to c and e
theorem r2_chain : ∀ k, ∀ c d e, ⟨k, 0, c, d, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e + k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- d_drain: R3 then R2x3 repeated
theorem d_drain : ∀ k, ∀ C E, ⟨0, 0, C, k, E + 1⟩ [fm]⊢* ⟨0, 0, C + 3 * k, 0, E + 2 * k + 1⟩ := by
  intro k; induction' k with k h <;> intro C E
  · simp; exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- rounds_r1r3: generalized R1x3+R3 rounds with remainder r
theorem rounds_r1r3 : ∀ k, ∀ r C D E, ⟨3, 3 * k + r, C, D, E + k⟩ [fm]⊢* ⟨3, r, C + 3 * k, D + 2 * k, E⟩ := by
  intro k; induction' k with k h <;> intro r C D E
  · simp; exists 0
  rw [show 3 * (k + 1) + r = (3 * k + r) + 1 + 1 + 1 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show D + 3 = (D + 2) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- main_trans_0: c ≡ 0 (mod 3)
theorem main_trans_0 (q e : ℕ) (he : e ≥ q) :
    ⟨0, 0, 3 * q + 1, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 9 * q + 3, 0, e + 3 * q + 3⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3 * q + 1, 0, 0, e + 1⟩)
  · have h := @c_to_b (3 * q + 1) 0 0 (e + 1)
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨0, 3 * q, 0, 1, e + 1⟩)
  · show fm ⟨0, (3 * q) + 1, 0, 0, e + 1⟩ = some ⟨0, 3 * q, 0, 1, e + 1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨3, 3 * q, 0, 0, e⟩)
  · have : ⟨0, 3 * q, 0, 0 + 1, e + 1⟩ [fm]⊢ ⟨0 + 3, 3 * q, 0, 0, e⟩ := by simp [fm]
    simp only [Nat.zero_add] at this; exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨3, 0, 3 * q, 2 * q, e - q⟩)
  · have h := @rounds_r1r3 q 0 0 0 (e - q)
    simp only [Nat.zero_add] at h
    rw [show e - q + q = e from Nat.sub_add_cancel he] at h; exact h
  apply stepStar_trans (c₂ := ⟨0, 0, 3 * q + 3, 2 * q, e - q + 3⟩)
  · exact r2_chain 3 (3 * q) (2 * q) (e - q)
  have h := @d_drain (2 * q) (3 * q + 3) (e - q + 2)
  have h1 : e - q + 2 + 2 * (2 * q) + 1 = e + 3 * q + 3 := by omega
  have h2 : 3 * q + 3 + 3 * (2 * q) = 9 * q + 3 := by ring
  have h3 : e - q + 2 + 1 = e - q + 3 := by ring
  rw [h1, h2, h3] at h; exact h

-- main_trans_1: c ≡ 1 (mod 3)
theorem main_trans_1 (q e : ℕ) (he : e ≥ q) :
    ⟨0, 0, 3 * q + 2, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 9 * q + 6, 0, e + 3 * q + 4⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3 * q + 2, 0, 0, e + 1⟩)
  · have h := @c_to_b (3 * q + 2) 0 0 (e + 1)
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨0, 3 * q + 1, 0, 1, e + 1⟩)
  · show fm ⟨0, (3 * q + 1) + 1, 0, 0, e + 1⟩ = some ⟨0, 3 * q + 1, 0, 1, e + 1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨3, 3 * q + 1, 0, 0, e⟩)
  · have : ⟨0, 3 * q + 1, 0, 0 + 1, e + 1⟩ [fm]⊢ ⟨0 + 3, 3 * q + 1, 0, 0, e⟩ := by simp [fm]
    simp only [Nat.zero_add] at this; exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨3, 1, 3 * q, 2 * q, e - q⟩)
  · have h := @rounds_r1r3 q 1 0 0 (e - q)
    simp only [Nat.zero_add] at h
    rw [show e - q + q = e from Nat.sub_add_cancel he] at h; exact h
  apply stepStar_trans (c₂ := ⟨0, 0, 3 * q + 3, 2 * q + 1, e - q + 2⟩)
  · step fm; step fm; step fm; ring_nf; finish
  have h := @d_drain (2 * q + 1) (3 * q + 3) (e - q + 1)
  have h1 : e - q + 1 + 2 * (2 * q + 1) + 1 = e + 3 * q + 4 := by omega
  have h2 : 3 * q + 3 + 3 * (2 * q + 1) = 9 * q + 6 := by ring
  have h3 : e - q + 1 + 1 = e - q + 2 := by ring
  rw [h1, h2, h3] at h; exact h

-- main_trans_2: c ≡ 2 (mod 3)
theorem main_trans_2 (q e : ℕ) (he : e ≥ q) :
    ⟨0, 0, 3 * q + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 9 * q + 9, 0, e + 3 * q + 5⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3 * q + 3, 0, 0, e + 1⟩)
  · have h := @c_to_b (3 * q + 3) 0 0 (e + 1)
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨0, 3 * q + 2, 0, 1, e + 1⟩)
  · show fm ⟨0, (3 * q + 2) + 1, 0, 0, e + 1⟩ = some ⟨0, 3 * q + 2, 0, 1, e + 1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨3, 3 * q + 2, 0, 0, e⟩)
  · have : ⟨0, 3 * q + 2, 0, 0 + 1, e + 1⟩ [fm]⊢ ⟨0 + 3, 3 * q + 2, 0, 0, e⟩ := by simp [fm]
    simp only [Nat.zero_add] at this; exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨3, 2, 3 * q, 2 * q, e - q⟩)
  · have h := @rounds_r1r3 q 2 0 0 (e - q)
    simp only [Nat.zero_add] at h
    rw [show e - q + q = e from Nat.sub_add_cancel he] at h; exact h
  apply stepStar_trans (c₂ := ⟨0, 0, 3 * q + 3, 2 * q + 2, e - q + 1⟩)
  · step fm; step fm; step fm; ring_nf; finish
  have h := @d_drain (2 * q + 2) (3 * q + 3) (e - q)
  have h1 : e - q + 2 * (2 * q + 2) + 1 = e + 3 * q + 5 := by omega
  have h2 : 3 * q + 3 + 3 * (2 * q + 2) = 9 * q + 9 := by ring
  have h3 : (e - q) + 1 = e - q + 1 := by ring
  rw [h1, h2, h3] at h; exact h

-- Combined main transition
theorem main_trans (c e : ℕ) (hce : c ≤ 3 * e + 2) :
    ⟨0, 0, c + 1, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 3 * c + 3, 0, e + c + 3⟩ := by
  have hq : e ≥ c / 3 := by omega
  have hmod := Nat.div_add_mod c 3
  set q := c / 3
  set r := c % 3
  have hr : r < 3 := Nat.mod_lt c (by omega)
  interval_cases r
  · have hc : c = 3 * q := by omega
    rw [hc, show 3 * (3 * q) + 3 = 9 * q + 3 from by ring]
    exact main_trans_0 q e hq
  · have hc : c = 3 * q + 1 := by omega
    rw [hc, show 3 * (3 * q + 1) + 3 = 9 * q + 6 from by ring,
        show e + (3 * q + 1) + 3 = e + 3 * q + 4 from by ring]
    exact main_trans_1 q e hq
  · have hc : c = 3 * q + 2 := by omega
    rw [hc, show 3 * (3 * q + 2) + 3 = 9 * q + 9 from by ring,
        show e + (3 * q + 2) + 3 = e + 3 * q + 5 from by ring]
    exact main_trans_2 q e hq

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c + 1, 0, e + 1⟩ ∧ c ≤ 3 * e + 2)
  · intro q ⟨c, e, hq, hce⟩
    subst hq
    exact ⟨⟨0, 0, 3 * c + 3, 0, e + c + 3⟩,
           ⟨3 * c + 2, e + c + 2, by ring_nf, by omega⟩,
           main_trans c e hce⟩
  · exact ⟨0, 0, rfl, by omega⟩

end Sz21_140_unofficial_53
