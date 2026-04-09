import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_halted_692 #12: [27/70, 25/2, 4/21, 7/5, 3/7]

Vector representation:
```
-1  3 -1 -1
-1  0  2  0
 2 -1  0 -1
 0  0 -1  1
 0  1  0 -1
```

This Fractran program halts in 113517251374 steps.

Author: Claude
-/

namespace Sz22_halted_692_12

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1⟩ => some ⟨a, b+3, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b+1, c, d+1⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

private theorem r4_gen : ∀ k c d, (⟨0, 0, c + k, d⟩ : Q) [fm]⊢^{k} ⟨0, 0, c, d + k⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · simp; rfl
  rw [show c + (k + 1) = (c + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨0, 0, (c + k) + 1, d⟩ = some ⟨0, 0, c + k, d + 1⟩; simp [fm]
  have h := ih c (d + 1)
  rw [show d + 1 + k = d + (1 + k) from by ring] at h; exact h

private theorem r4_sn : ∀ k d, (⟨0, 0, k, d⟩ : Q) [fm]⊢^{k} ⟨0, 0, 0, d + k⟩ := by
  intro k d; have h := r4_gen k 0 d; simp at h; exact h

private theorem bdrain_step : ∀ b c, (⟨0, b + 1, c + 1, 0⟩ : Q) [fm]⊢^{4} ⟨0, b, c + 4, 0⟩ := by
  intro b c
  apply stepNat_trans 1 3
  · show fm ⟨0, b + 1, c + 1, 0⟩ = some ⟨0, b + 1, c, 1⟩; simp [fm]
  apply stepNat_trans 1 2
  · show fm ⟨0, b + 1, c, 1⟩ = some ⟨2, b, c, 0⟩; simp [fm]
  apply stepNat_trans 1 1
  · show fm ⟨2, b, c, 0⟩ = some ⟨1, b, c + 2, 0⟩; simp [fm]
  show fm ⟨1, b, c + 2, 0⟩ = some ⟨0, b, c + 4, 0⟩; simp [fm]

private theorem bdrain_gen : ∀ k b c, (⟨0, b + k, c + 1, 0⟩ : Q) [fm]⊢^{4 * k} ⟨0, b, c + 1 + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · simp; rfl
  rw [show b + (k + 1) = (b + k) + 1 from by ring, show 4 * (k + 1) = 4 + 4 * k from by ring]
  apply stepNat_trans 4 (4 * k)
  · exact bdrain_step (b + k) c
  rw [show c + 4 = (c + 3) + 1 from by ring]
  have h := ih b (c + 3)
  rw [show c + 3 + 1 + 3 * k = c + 1 + 3 * (k + 1) from by ring] at h; exact h

private theorem bdrain_sn : ∀ k c, (⟨0, k, c + 1, 0⟩ : Q) [fm]⊢^{4 * k} ⟨0, 0, c + 1 + 3 * k, 0⟩ := by
  intro k c; have h := bdrain_gen k 0 c; simp at h; exact h

private theorem open_cycle : ∀ k b d, (⟨0, b + 1, 1, d + 7 * k⟩ : Q) [fm]⊢^{9 * k} ⟨0, b + 1 + 9 * k, 1, d⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · simp; rfl
  rw [show d + 7 * (k + 1) = (d + 7 * k) + 7 from by ring,
      show 9 * (k + 1) = 9 + 9 * k from by ring]
  apply stepNat_trans 9 (9 * k)
  · rw [show b + 1 = b + 1 from by ring]
    show stepNat fm 9 ⟨0, b + 1, 1, (d + 7 * k) + 7⟩ = some ⟨0, b + 10, 1, d + 7 * k⟩; rfl
  rw [show b + 10 = (b + 9) + 1 from by ring,
      show 9 + 9 * k = 9 * (k + 1) from by ring]
  have h := ih (b + 9) d
  rw [show b + 9 + 1 + 9 * k = b + 1 + 9 * (k + 1) from by ring] at h; exact h

private theorem tail_D0 : ∀ b, (⟨0, b + 1, 1, 0⟩ : Q) [fm]⊢^{7 * b + 8} ⟨0, 0, 0, 3 * b + 4⟩ := by
  intro b
  rw [show (7 * b + 8 : ℕ) = 4 + (4 * b + (3 * b + 4)) from by ring]
  apply stepNat_trans 4 (4 * b + (3 * b + 4))
  · show stepNat fm 4 ⟨0, b + 1, 1, 0⟩ = some ⟨0, b, 4, 0⟩; rfl
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepNat_trans (4 * b) (3 * b + 4) (bdrain_sn b 3)
  rw [show 3 + 1 + 3 * b = 3 * b + 4 from by ring]
  have h := r4_sn (3 * b + 4) 0
  rw [show 0 + (3 * b + 4) = 3 * b + 4 from by ring] at h; exact h

private theorem tail_D1 : ∀ b, (⟨0, b + 1, 1, 1⟩ : Q) [fm]⊢^{7 * b + 8} ⟨0, 0, 0, 3 * b + 5⟩ := by
  intro b
  rw [show (7 * b + 8 : ℕ) = 3 + (4 * b + (3 * b + 5)) from by ring]
  apply stepNat_trans 3 (4 * b + (3 * b + 5))
  · show stepNat fm 3 ⟨0, b + 1, 1, 1⟩ = some ⟨0, b, 5, 0⟩; rfl
  rw [show (5 : ℕ) = 4 + 1 from by ring]
  apply stepNat_trans (4 * b) (3 * b + 5) (bdrain_sn b 4)
  rw [show 4 + 1 + 3 * b = 3 * b + 5 from by ring]
  have h := r4_sn (3 * b + 5) 0
  rw [show 0 + (3 * b + 5) = 3 * b + 5 from by ring] at h; exact h

private theorem tail_D2 : ∀ b, (⟨0, b + 1, 1, 2⟩ : Q) [fm]⊢^{7 * b + 26} ⟨0, 0, 0, 3 * b + 11⟩ := by
  intro b
  rw [show (7 * b + 26 : ℕ) = 3 + (4 * (b + 3) + (3 * b + 11)) from by ring]
  apply stepNat_trans 3 (4 * (b + 3) + (3 * b + 11))
  · show stepNat fm 3 ⟨0, b + 1, 1, 2⟩ = some ⟨0, b + 3, 2, 0⟩; rfl
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepNat_trans (4 * (b + 3)) (3 * b + 11) (bdrain_sn (b + 3) 1)
  rw [show 1 + 1 + 3 * (b + 3) = 3 * b + 11 from by ring]
  have h := r4_sn (3 * b + 11) 0
  rw [show 0 + (3 * b + 11) = 3 * b + 11 from by ring] at h; exact h

private theorem tail_D3 : ∀ b, (⟨0, b + 1, 1, 3⟩ : Q) [fm]⊢^{7 * b + 26} ⟨0, 0, 0, 3 * b + 12⟩ := by
  intro b
  rw [show (7 * b + 26 : ℕ) = 6 + (4 * (b + 2) + (3 * b + 12)) from by ring]
  apply stepNat_trans 6 (4 * (b + 2) + (3 * b + 12))
  · show stepNat fm 6 ⟨0, b + 1, 1, 3⟩ = some ⟨0, b + 2, 6, 0⟩; rfl
  rw [show (6 : ℕ) = 5 + 1 from by ring]
  apply stepNat_trans (4 * (b + 2)) (3 * b + 12) (bdrain_sn (b + 2) 5)
  rw [show 5 + 1 + 3 * (b + 2) = 3 * b + 12 from by ring]
  have h := r4_sn (3 * b + 12) 0
  rw [show 0 + (3 * b + 12) = 3 * b + 12 from by ring] at h; exact h

private theorem tail_D4 : ∀ b, (⟨0, b + 1, 1, 4⟩ : Q) [fm]⊢^{7 * b + 44} ⟨0, 0, 0, 3 * b + 18⟩ := by
  intro b
  rw [show (7 * b + 44 : ℕ) = 6 + (4 * (b + 5) + (3 * b + 18)) from by ring]
  apply stepNat_trans 6 (4 * (b + 5) + (3 * b + 18))
  · show stepNat fm 6 ⟨0, b + 1, 1, 4⟩ = some ⟨0, b + 5, 3, 0⟩; rfl
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepNat_trans (4 * (b + 5)) (3 * b + 18) (bdrain_sn (b + 5) 2)
  rw [show 2 + 1 + 3 * (b + 5) = 3 * b + 18 from by ring]
  have h := r4_sn (3 * b + 18) 0
  rw [show 0 + (3 * b + 18) = 3 * b + 18 from by ring] at h; exact h

private theorem tail_D6 : ∀ b, (⟨0, b + 1, 1, 6⟩ : Q) [fm]⊢^{7 * b + 62} ⟨0, 0, 0, 3 * b + 25⟩ := by
  intro b
  rw [show (7 * b + 62 : ℕ) = 9 + (4 * (b + 7) + (3 * b + 25)) from by ring]
  apply stepNat_trans 9 (4 * (b + 7) + (3 * b + 25))
  · show stepNat fm 9 ⟨0, b + 1, 1, 6⟩ = some ⟨0, b + 7, 4, 0⟩; rfl
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepNat_trans (4 * (b + 7)) (3 * b + 25) (bdrain_sn (b + 7) 3)
  rw [show 3 + 1 + 3 * (b + 7) = 3 * b + 25 from by ring]
  have h := r4_sn (3 * b + 25) 0
  rw [show 0 + (3 * b + 25) = 3 * b + 25 from by ring] at h; exact h

private theorem macro_mod3_sn : ∀ q, (⟨0, 0, 0, 7 * q + 3⟩ : Q) [fm]⊢^{72 * q + 26} ⟨0, 0, 0, 27 * q + 10⟩ := by
  intro q
  rw [show (72 * q + 26 : ℕ) = 4 + (9 * q + (7 * (2 + 9 * q) + 8)) from by ring]
  apply stepNat_trans 4 (9 * q + (7 * (2 + 9 * q) + 8))
  · show stepNat fm 4 ⟨0, 0, 0, 7 * q + 3⟩ = some ⟨0, 3, 1, 7 * q⟩; rfl
  rw [show 7 * q = 0 + 7 * q from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  apply stepNat_trans (9 * q) (7 * (2 + 9 * q) + 8) (open_cycle q 2 0)
  rw [show 2 + 1 + 9 * q = (2 + 9 * q) + 1 from by ring]
  have h := tail_D0 (2 + 9 * q)
  rw [show 3 * (2 + 9 * q) + 4 = 27 * q + 10 from by ring] at h; exact h

private theorem macro_mod4_sn : ∀ q, (⟨0, 0, 0, 7 * q + 4⟩ : Q) [fm]⊢^{72 * q + 26} ⟨0, 0, 0, 27 * q + 11⟩ := by
  intro q
  rw [show (72 * q + 26 : ℕ) = 4 + (9 * q + (7 * (2 + 9 * q) + 8)) from by ring]
  apply stepNat_trans 4 (9 * q + (7 * (2 + 9 * q) + 8))
  · show stepNat fm 4 ⟨0, 0, 0, 7 * q + 4⟩ = some ⟨0, 3, 1, 7 * q + 1⟩; rfl
  rw [show 7 * q + 1 = 1 + 7 * q from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  apply stepNat_trans (9 * q) (7 * (2 + 9 * q) + 8) (open_cycle q 2 1)
  rw [show 2 + 1 + 9 * q = (2 + 9 * q) + 1 from by ring]
  have h := tail_D1 (2 + 9 * q)
  rw [show 3 * (2 + 9 * q) + 5 = 27 * q + 11 from by ring] at h; exact h

private theorem macro_mod5_sn : ∀ q, (⟨0, 0, 0, 7 * q + 5⟩ : Q) [fm]⊢^{72 * q + 44} ⟨0, 0, 0, 27 * q + 17⟩ := by
  intro q
  rw [show (72 * q + 44 : ℕ) = 4 + (9 * q + (7 * (2 + 9 * q) + 26)) from by ring]
  apply stepNat_trans 4 (9 * q + (7 * (2 + 9 * q) + 26))
  · show stepNat fm 4 ⟨0, 0, 0, 7 * q + 5⟩ = some ⟨0, 3, 1, 7 * q + 2⟩; rfl
  rw [show 7 * q + 2 = 2 + 7 * q from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  apply stepNat_trans (9 * q) (7 * (2 + 9 * q) + 26) (open_cycle q 2 2)
  rw [show 2 + 1 + 9 * q = (2 + 9 * q) + 1 from by ring]
  have h := tail_D2 (2 + 9 * q)
  rw [show 3 * (2 + 9 * q) + 11 = 27 * q + 17 from by ring] at h; exact h

private theorem macro_mod6_sn : ∀ q, (⟨0, 0, 0, 7 * q + 6⟩ : Q) [fm]⊢^{72 * q + 44} ⟨0, 0, 0, 27 * q + 18⟩ := by
  intro q
  rw [show (72 * q + 44 : ℕ) = 4 + (9 * q + (7 * (2 + 9 * q) + 26)) from by ring]
  apply stepNat_trans 4 (9 * q + (7 * (2 + 9 * q) + 26))
  · show stepNat fm 4 ⟨0, 0, 0, 7 * q + 6⟩ = some ⟨0, 3, 1, 7 * q + 3⟩; rfl
  rw [show 7 * q + 3 = 3 + 7 * q from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  apply stepNat_trans (9 * q) (7 * (2 + 9 * q) + 26) (open_cycle q 2 3)
  rw [show 2 + 1 + 9 * q = (2 + 9 * q) + 1 from by ring]
  have h := tail_D3 (2 + 9 * q)
  rw [show 3 * (2 + 9 * q) + 12 = 27 * q + 18 from by ring] at h; exact h

private theorem macro_mod0_sn : ∀ q, (⟨0, 0, 0, 7 * (q + 1)⟩ : Q) [fm]⊢^{72 * q + 62} ⟨0, 0, 0, 27 * q + 24⟩ := by
  intro q
  rw [show (72 * q + 62 : ℕ) = 4 + (9 * q + (7 * (2 + 9 * q) + 44)) from by ring]
  apply stepNat_trans 4 (9 * q + (7 * (2 + 9 * q) + 44))
  · rw [show 7 * (q + 1) = 7 * q + 7 from by ring]
    show stepNat fm 4 ⟨0, 0, 0, 7 * q + 7⟩ = some ⟨0, 3, 1, 7 * q + 4⟩; rfl
  rw [show 7 * q + 4 = 4 + 7 * q from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  apply stepNat_trans (9 * q) (7 * (2 + 9 * q) + 44) (open_cycle q 2 4)
  rw [show 2 + 1 + 9 * q = (2 + 9 * q) + 1 from by ring]
  have h := tail_D4 (2 + 9 * q)
  rw [show 3 * (2 + 9 * q) + 18 = 27 * q + 24 from by ring] at h; exact h

private theorem macro_mod2_sn : ∀ q, (⟨0, 0, 0, 7 * (q + 1) + 2⟩ : Q) [fm]⊢^{72 * q + 80} ⟨0, 0, 0, 27 * q + 31⟩ := by
  intro q
  rw [show (72 * q + 80 : ℕ) = 4 + (9 * q + (7 * (2 + 9 * q) + 62)) from by ring]
  apply stepNat_trans 4 (9 * q + (7 * (2 + 9 * q) + 62))
  · rw [show 7 * (q + 1) + 2 = 7 * q + 9 from by ring]
    show stepNat fm 4 ⟨0, 0, 0, 7 * q + 9⟩ = some ⟨0, 3, 1, 7 * q + 6⟩; rfl
  rw [show 7 * q + 6 = 6 + 7 * q from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  apply stepNat_trans (9 * q) (7 * (2 + 9 * q) + 62) (open_cycle q 2 6)
  rw [show 2 + 1 + 9 * q = (2 + 9 * q) + 1 from by ring]
  have h := tail_D6 (2 + 9 * q)
  rw [show 3 * (2 + 9 * q) + 25 = 27 * q + 31 from by ring] at h; exact h

private theorem exit_D5 : ∀ b, (⟨0, b + 1, 1, 5⟩ : Q) [fm]⊢^{6} ⟨0, b + 8, 0, 0⟩ := by
  intro b
  apply stepNat_trans 1 5
  · show fm ⟨0, b + 1, 1, 5⟩ = some ⟨2, b, 1, 4⟩; simp [fm]
  apply stepNat_trans 1 4
  · show fm ⟨2, b, 1, 4⟩ = some ⟨1, b + 3, 0, 3⟩; simp [fm]
  apply stepNat_trans 1 3
  · show fm ⟨1, b + 3, 0, 3⟩ = some ⟨0, b + 3, 2, 3⟩; simp [fm]
  apply stepNat_trans 1 2
  · show fm ⟨0, b + 3, 2, 3⟩ = some ⟨2, b + 2, 2, 2⟩; simp [fm]
  apply stepNat_trans 1 1
  · show fm ⟨2, b + 2, 2, 2⟩ = some ⟨1, b + 5, 1, 1⟩; simp [fm]
  show fm ⟨1, b + 5, 1, 1⟩ = some ⟨0, b + 8, 0, 0⟩; simp [fm]

private theorem macro_halt_sn : ∀ q, (⟨0, 0, 0, 7 * (q + 1) + 1⟩ : Q) [fm]⊢^{9 * q + 10} ⟨0, 9 * q + 10, 0, 0⟩ := by
  intro q
  have goal_eq : 9 * q + 10 = 4 + (9 * q + 6) := by ring
  conv_lhs => rw [goal_eq]
  apply stepNat_trans 4 (9 * q + 6)
  · rw [show 7 * (q + 1) + 1 = 7 * q + 8 from by ring]
    show stepNat fm 4 ⟨0, 0, 0, 7 * q + 8⟩ = some ⟨0, 3, 1, 7 * q + 5⟩; rfl
  rw [show 7 * q + 5 = 5 + 7 * q from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  apply stepNat_trans (9 * q) 6 (open_cycle q 2 5)
  rw [show 2 + 1 + 9 * q = (9 * q + 2) + 1 from by ring]
  have h := exit_D5 (9 * q + 2)
  rw [show 9 * q + 2 + 8 = 9 * q + 10 from by ring] at h; exact h

theorem fm_haltsIn : haltsIn fm c₀ 113517251374 := by
  apply stepNat_haltsIn_add (m := 3) (c₂ := ⟨0, 0, 0, 2⟩)
  · show stepNat fm 3 c₀ = some ⟨0, 0, 0, 2⟩; rfl
  apply stepNat_haltsIn_add (m := 8) (c₂ := ⟨0, 0, 0, 4⟩)
  · show stepNat fm 8 ⟨0, 0, 0, 2⟩ = some ⟨0, 0, 0, 4⟩; rfl
  apply stepNat_haltsIn_add (m := 26) (c₂ := ⟨0, 0, 0, 11⟩)
  · rw [show (4 : ℕ) = 7 * 0 + 4 from by ring, show (11 : ℕ) = 27 * 0 + 11 from by ring,
      show (26 : ℕ) = 72 * 0 + 26 from by ring]; exact macro_mod4_sn 0
  apply stepNat_haltsIn_add (m := 98) (c₂ := ⟨0, 0, 0, 38⟩)
  · rw [show (11 : ℕ) = 7 * 1 + 4 from by ring, show (38 : ℕ) = 27 * 1 + 11 from by ring,
      show (98 : ℕ) = 72 * 1 + 26 from by ring]; exact macro_mod4_sn 1
  apply stepNat_haltsIn_add (m := 386) (c₂ := ⟨0, 0, 0, 145⟩)
  · rw [show (38 : ℕ) = 7 * 5 + 3 from by ring, show (145 : ℕ) = 27 * 5 + 10 from by ring,
      show (386 : ℕ) = 72 * 5 + 26 from by ring]; exact macro_mod3_sn 5
  apply stepNat_haltsIn_add (m := 1484) (c₂ := ⟨0, 0, 0, 557⟩)
  · rw [show (145 : ℕ) = 7 * 20 + 5 from by ring, show (557 : ℕ) = 27 * 20 + 17 from by ring,
      show (1484 : ℕ) = 72 * 20 + 44 from by ring]; exact macro_mod5_sn 20
  apply stepNat_haltsIn_add (m := 5714) (c₂ := ⟨0, 0, 0, 2144⟩)
  · rw [show (557 : ℕ) = 7 * 79 + 4 from by ring, show (2144 : ℕ) = 27 * 79 + 11 from by ring,
      show (5714 : ℕ) = 72 * 79 + 26 from by ring]; exact macro_mod4_sn 79
  apply stepNat_haltsIn_add (m := 22040) (c₂ := ⟨0, 0, 0, 8266⟩)
  · rw [show (2144 : ℕ) = 7 * (305 + 1) + 2 from by ring,
      show (8266 : ℕ) = 27 * 305 + 31 from by ring,
      show (22040 : ℕ) = 72 * 305 + 80 from by ring]
    exact macro_mod2_sn 305
  apply stepNat_haltsIn_add (m := 85004) (c₂ := ⟨0, 0, 0, 31878⟩)
  · rw [show (8266 : ℕ) = 7 * 1180 + 6 from by ring, show (31878 : ℕ) = 27 * 1180 + 18 from by ring,
      show (85004 : ℕ) = 72 * 1180 + 44 from by ring]; exact macro_mod6_sn 1180
  apply stepNat_haltsIn_add (m := 327878) (c₂ := ⟨0, 0, 0, 122955⟩)
  · rw [show (31878 : ℕ) = 7 * (4553 + 1) from by ring,
      show (122955 : ℕ) = 27 * 4553 + 24 from by ring,
      show (327878 : ℕ) = 72 * 4553 + 62 from by ring]
    exact macro_mod0_sn 4553
  apply stepNat_haltsIn_add (m := 1264670) (c₂ := ⟨0, 0, 0, 474252⟩)
  · rw [show (122955 : ℕ) = 7 * (17564 + 1) from by ring,
      show (474252 : ℕ) = 27 * 17564 + 24 from by ring,
      show (1264670 : ℕ) = 72 * 17564 + 62 from by ring]
    exact macro_mod0_sn 17564
  apply stepNat_haltsIn_add (m := 4878008) (c₂ := ⟨0, 0, 0, 1829254⟩)
  · rw [show (474252 : ℕ) = 7 * (67749 + 1) + 2 from by ring,
      show (1829254 : ℕ) = 27 * 67749 + 31 from by ring,
      show (4878008 : ℕ) = 72 * 67749 + 80 from by ring]
    exact macro_mod2_sn 67749
  apply stepNat_haltsIn_add (m := 18815174) (c₂ := ⟨0, 0, 0, 7055691⟩)
  · rw [show (1829254 : ℕ) = 7 * (261321 + 1) from by ring,
      show (7055691 : ℕ) = 27 * 261321 + 24 from by ring,
      show (18815174 : ℕ) = 72 * 261321 + 62 from by ring]
    exact macro_mod0_sn 261321
  apply stepNat_haltsIn_add (m := 72572804) (c₂ := ⟨0, 0, 0, 27214803⟩)
  · rw [show (7055691 : ℕ) = 7 * 1007955 + 6 from by ring, show (27214803 : ℕ) = 27 * 1007955 + 18 from by ring,
      show (72572804 : ℕ) = 72 * 1007955 + 44 from by ring]; exact macro_mod6_sn 1007955
  apply stepNat_haltsIn_add (m := 279923678) (c₂ := ⟨0, 0, 0, 104971380⟩)
  · rw [show (27214803 : ℕ) = 7 * (3887828 + 1) from by ring,
      show (104971380 : ℕ) = 27 * 3887828 + 24 from by ring,
      show (279923678 : ℕ) = 72 * 3887828 + 62 from by ring]
    exact macro_mod0_sn 3887828
  apply stepNat_haltsIn_add (m := 1079705618) (c₂ := ⟨0, 0, 0, 404889607⟩)
  · rw [show (104971380 : ℕ) = 7 * 14995911 + 3 from by ring, show (404889607 : ℕ) = 27 * 14995911 + 10 from by ring,
      show (1079705618 : ℕ) = 72 * 14995911 + 26 from by ring]; exact macro_mod3_sn 14995911
  apply stepNat_haltsIn_add (m := 4164578810) (c₂ := ⟨0, 0, 0, 1561717054⟩)
  · rw [show (404889607 : ℕ) = 7 * 57841372 + 3 from by ring, show (1561717054 : ℕ) = 27 * 57841372 + 10 from by ring,
      show (4164578810 : ℕ) = 72 * 57841372 + 26 from by ring]; exact macro_mod3_sn 57841372
  apply stepNat_haltsIn_add (m := 16063375400) (c₂ := ⟨0, 0, 0, 6023765776⟩)
  · rw [show (1561717054 : ℕ) = 7 * (223102435 + 1) + 2 from by ring,
      show (6023765776 : ℕ) = 27 * 223102435 + 31 from by ring,
      show (16063375400 : ℕ) = 72 * 223102435 + 80 from by ring]
    exact macro_mod2_sn 223102435
  apply stepNat_haltsIn_add (m := 61958733686) (c₂ := ⟨0, 0, 0, 23234525133⟩)
  · rw [show (6023765776 : ℕ) = 7 * (860537967 + 1) from by ring,
      show (23234525133 : ℕ) = 27 * 860537967 + 24 from by ring,
      show (61958733686 : ℕ) = 72 * 860537967 + 62 from by ring]
    exact macro_mod0_sn 860537967
  refine ⟨⟨0, 29872960885, 0, 0⟩, ?_, rfl⟩
  rw [show (23234525133 : ℕ) = 7 * (3319217875 + 1) + 1 from by ring,
    show (29872960885 : ℕ) = 9 * 3319217875 + 10 from by ring]
  exact macro_halt_sn 3319217875

end Sz22_halted_692_12
