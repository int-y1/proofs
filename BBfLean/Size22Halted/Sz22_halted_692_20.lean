import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_halted_692 #20: [5/6, 343/2, 16/15, 3/7, 5/3]

Vector representation:
```
-1 -1  1  0
-1  0  0  3
 4 -1 -1  0
 0  1  0 -1
 0 -1  1  0
```

This Fractran program halts in 1463418236 steps.

Author: Claude
-/

namespace Sz22_halted_692_20

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+3⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+4, b, c, d⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | _ => none

private theorem r4_gen : ∀ k b d, (⟨0, b, 0, d + k⟩ : Q) [fm]⊢^{k} ⟨0, b + k, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · simp; rfl
  rw [show d + (k + 1) = (d + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨0, b, 0, (d + k) + 1⟩ = some ⟨0, b + 1, 0, d + k⟩; simp [fm]
  rw [show b + (1 + k) = (b + 1) + k from by ring]; exact ih (b + 1) d

private theorem r4_sn : ∀ k d, (⟨0, 0, 0, d + k⟩ : Q) [fm]⊢^{k} ⟨0, k, 0, d⟩ := by
  intro k d; have h := r4_gen k 0 d; simp at h; exact h

private theorem inner_chain_sn : ∀ q s c, (⟨0, 5 * q + s, c + 1, 0⟩ : Q) [fm]⊢^{5 * q} ⟨0, s, c + 1 + 3 * q, 0⟩ := by
  intro q; induction' q with q ih <;> intro s c
  · simp; rfl
  rw [show 5 * (q + 1) + s = (5 * q + s) + 5 from by ring, show 5 * (q + 1) = 5 + 5 * q from by ring]
  apply stepNat_trans 5 (5 * q)
  · show stepNat fm 5 ⟨0, (5 * q + s) + 5, c + 1, 0⟩ = some ⟨0, 5 * q + s, c + 4, 0⟩; rfl
  rw [show c + 4 = (c + 3) + 1 from by ring]
  have h := ih s (c + 3)
  rw [show c + 3 + 1 + 3 * q = c + 1 + 3 * (q + 1) from by ring] at h; exact h

private theorem drain_chain_sn : ∀ k c d, (⟨0, 0, k + c, d + 1⟩ : Q) [fm]⊢^{6 * k} ⟨0, 0, c, d + 1 + 11 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · simp; rfl
  rw [show (k + 1) + c = k + c + 1 from by ring, show 6 * (k + 1) = 6 + 6 * k from by ring]
  apply stepNat_trans 6 (6 * k)
  · show stepNat fm 6 ⟨0, 0, (k + c) + 1, d + 1⟩ = some ⟨0, 0, k + c, d + 12⟩; rfl
  rw [show d + 12 = (d + 11) + 1 from by ring]
  have h := ih c (d + 11)
  rw [show d + 11 + 1 + 11 * k = d + 1 + 11 * (k + 1) from by ring] at h; exact h

private theorem r5_sn : ∀ b, (⟨0, b + 1, 0, 0⟩ : Q) [fm]⊢^{1} ⟨0, b, 1, 0⟩ := by intro b; rfl

private theorem macro_mod3_sn : ∀ m, (⟨0, 0, 0, 5 * m + 3⟩ : Q) [fm]⊢^{28 * m + 15} ⟨0, 0, 0, 33 * m + 20⟩ := by
  intro m
  rw [show 5 * m + 3 = 0 + (5 * m + 3) from by ring,
    show 28 * m + 15 = (5 * m + 3) + (1 + (5 * m + (5 + 6 * (3 * m + 1)))) from by ring]
  apply stepNat_trans (5 * m + 3) (1 + (5 * m + (5 + 6 * (3 * m + 1)))) (r4_sn (5 * m + 3) 0)
  rw [show (5 * m + 3 : ℕ) = (5 * m + 2) + 1 from by ring]
  apply stepNat_trans 1 (5 * m + (5 + 6 * (3 * m + 1))) (r5_sn (5 * m + 2))
  apply stepNat_trans (5 * m) (5 + 6 * (3 * m + 1)) (inner_chain_sn m 2 0)
  rw [show 0 + 1 + 3 * m = (3 * m) + 1 from by ring]
  apply stepNat_trans 5 (6 * (3 * m + 1))
    (show stepNat fm 5 ⟨0, 2, (3 * m) + 1, 0⟩ = some ⟨0, 0, 3 * m + 1, 9⟩ from rfl)
  rw [show 3 * m + 1 = (3 * m + 1) + 0 from by ring, show (9 : ℕ) = 8 + 1 from by ring]
  have h := drain_chain_sn (3 * m + 1) 0 8
  rw [show 8 + 1 + 11 * (3 * m + 1) = 33 * m + 20 from by ring] at h; exact h

private theorem macro_mod0_sn : ∀ m, (⟨0, 0, 0, 5 * (m + 1)⟩ : Q) [fm]⊢^{28 * (m + 1) + 1} ⟨0, 0, 0, 33 * m + 36⟩ := by
  intro m
  rw [show 5 * (m + 1) = 0 + 5 * (m + 1) from by ring,
    show 28 * (m + 1) + 1 = 5 * (m + 1) + (1 + (5 * m + (5 + 6 * (3 * m + 3)))) from by ring]
  apply stepNat_trans (5 * (m + 1)) _ (r4_sn (5 * (m + 1)) 0)
  rw [show (5 * (m + 1) : ℕ) = (5 * m + 4) + 1 from by ring]
  apply stepNat_trans 1 _ (r5_sn (5 * m + 4))
  apply stepNat_trans (5 * m) _ (inner_chain_sn m 4 0)
  rw [show 0 + 1 + 3 * m = (3 * m) + 1 from by ring]
  apply stepNat_trans 5 _
    (show stepNat fm 5 ⟨0, 4, (3 * m) + 1, 0⟩ = some ⟨0, 0, 3 * m + 3, 3⟩ from rfl)
  rw [show 3 * m + 3 = (3 * m + 3) + 0 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  have h := drain_chain_sn (3 * m + 3) 0 2
  rw [show 2 + 1 + 11 * (3 * m + 3) = 33 * m + 36 from by ring] at h; exact h

private theorem macro_mod4_sn : ∀ m, (⟨0, 0, 0, 5 * m + 4⟩ : Q) [fm]⊢^{28 * m + 22} ⟨0, 0, 0, 33 * m + 28⟩ := by
  intro m
  rw [show 5 * m + 4 = 0 + (5 * m + 4) from by ring,
    show 28 * m + 22 = (5 * m + 4) + (1 + (5 * m + (5 + 6 * (3 * m + 2)))) from by ring]
  apply stepNat_trans (5 * m + 4) _ (r4_sn (5 * m + 4) 0)
  rw [show (5 * m + 4 : ℕ) = (5 * m + 3) + 1 from by ring]
  apply stepNat_trans 1 _ (r5_sn (5 * m + 3))
  apply stepNat_trans (5 * m) _ (inner_chain_sn m 3 0)
  rw [show 0 + 1 + 3 * m = (3 * m) + 1 from by ring]
  apply stepNat_trans 5 _
    (show stepNat fm 5 ⟨0, 3, (3 * m) + 1, 0⟩ = some ⟨0, 0, 3 * m + 2, 6⟩ from rfl)
  rw [show 3 * m + 2 = (3 * m + 2) + 0 from by ring, show (6 : ℕ) = 5 + 1 from by ring]
  have h := drain_chain_sn (3 * m + 2) 0 5
  rw [show 5 + 1 + 11 * (3 * m + 2) = 33 * m + 28 from by ring] at h; exact h

private theorem macro_mod2_sn : ∀ m, (⟨0, 0, 0, 5 * m + 2⟩ : Q) [fm]⊢^{28 * m + 8} ⟨0, 0, 0, 33 * m + 12⟩ := by
  intro m
  rw [show 5 * m + 2 = 0 + (5 * m + 2) from by ring,
    show 28 * m + 8 = (5 * m + 2) + (1 + (5 * m + (5 + 6 * (3 * m)))) from by ring]
  apply stepNat_trans (5 * m + 2) _ (r4_sn (5 * m + 2) 0)
  rw [show (5 * m + 2 : ℕ) = (5 * m + 1) + 1 from by ring]
  apply stepNat_trans 1 _ (r5_sn (5 * m + 1))
  apply stepNat_trans (5 * m) _ (inner_chain_sn m 1 0)
  rw [show 0 + 1 + 3 * m = (3 * m) + 1 from by ring]
  apply stepNat_trans 5 _
    (show stepNat fm 5 ⟨0, 1, (3 * m) + 1, 0⟩ = some ⟨0, 0, 3 * m, 12⟩ from rfl)
  rw [show (12 : ℕ) = 11 + 1 from by ring]
  have h := drain_chain_sn (3 * m) 0 11
  rw [show 11 + 1 + 11 * (3 * m) = 33 * m + 12 from by ring] at h; exact h

private theorem macro_halt_sn : ∀ m, (⟨0, 0, 0, 5 * m + 1⟩ : Q) [fm]⊢^{10 * m + 2} ⟨0, 0, 1 + 3 * m, 0⟩ := by
  intro m
  rw [show 5 * m + 1 = 0 + (5 * m + 1) from by ring,
    show 10 * m + 2 = (5 * m + 1) + (1 + 5 * m) from by ring]
  apply stepNat_trans (5 * m + 1) _ (r4_sn (5 * m + 1) 0)
  rw [show (5 * m + 1 : ℕ) = (5 * m + 0) + 1 from by ring]
  apply stepNat_trans 1 (5 * m) (r5_sn (5 * m + 0))
  have h := inner_chain_sn m 0 0
  rw [show 0 + 1 + 3 * m = 1 + 3 * m from by ring] at h; exact h

theorem fm_haltsIn : haltsIn fm c₀ 1463418236 := by
  apply stepNat_haltsIn_add (m := 1) (c₂ := ⟨0, 0, 0, 3⟩)
  · show fm c₀ = some ⟨0, 0, 0, 3⟩; rfl
  apply stepNat_haltsIn_add (m := 15) (c₂ := ⟨0, 0, 0, 20⟩)
  · exact macro_mod3_sn 0
  apply stepNat_haltsIn_add (m := 113) (c₂ := ⟨0, 0, 0, 135⟩)
  · rw [show (20 : ℕ) = 5 * (3 + 1) from by ring, show (135 : ℕ) = 33 * 3 + 36 from by ring,
      show (113 : ℕ) = 28 * (3 + 1) + 1 from by ring]; exact macro_mod0_sn 3
  apply stepNat_haltsIn_add (m := 757) (c₂ := ⟨0, 0, 0, 894⟩)
  · rw [show (135 : ℕ) = 5 * (26 + 1) from by ring, show (894 : ℕ) = 33 * 26 + 36 from by ring,
      show (757 : ℕ) = 28 * (26 + 1) + 1 from by ring]; exact macro_mod0_sn 26
  apply stepNat_haltsIn_add (m := 5006) (c₂ := ⟨0, 0, 0, 5902⟩)
  · rw [show (894 : ℕ) = 5 * 178 + 4 from by ring, show (5902 : ℕ) = 33 * 178 + 28 from by ring,
      show (5006 : ℕ) = 28 * 178 + 22 from by ring]; exact macro_mod4_sn 178
  apply stepNat_haltsIn_add (m := 33048) (c₂ := ⟨0, 0, 0, 38952⟩)
  · rw [show (5902 : ℕ) = 5 * 1180 + 2 from by ring, show (38952 : ℕ) = 33 * 1180 + 12 from by ring,
      show (33048 : ℕ) = 28 * 1180 + 8 from by ring]; exact macro_mod2_sn 1180
  apply stepNat_haltsIn_add (m := 218128) (c₂ := ⟨0, 0, 0, 257082⟩)
  · rw [show (38952 : ℕ) = 5 * 7790 + 2 from by ring, show (257082 : ℕ) = 33 * 7790 + 12 from by ring,
      show (218128 : ℕ) = 28 * 7790 + 8 from by ring]; exact macro_mod2_sn 7790
  apply stepNat_haltsIn_add (m := 1439656) (c₂ := ⟨0, 0, 0, 1696740⟩)
  · rw [show (257082 : ℕ) = 5 * 51416 + 2 from by ring, show (1696740 : ℕ) = 33 * 51416 + 12 from by ring,
      show (1439656 : ℕ) = 28 * 51416 + 8 from by ring]; exact macro_mod2_sn 51416
  apply stepNat_haltsIn_add (m := 9501745) (c₂ := ⟨0, 0, 0, 11198487⟩)
  · rw [show (1696740 : ℕ) = 5 * (339347 + 1) from by ring, show (11198487 : ℕ) = 33 * 339347 + 36 from by ring,
      show (9501745 : ℕ) = 28 * (339347 + 1) + 1 from by ring]; exact macro_mod0_sn 339347
  apply stepNat_haltsIn_add (m := 62711524) (c₂ := ⟨0, 0, 0, 73910013⟩)
  · rw [show (11198487 : ℕ) = 5 * 2239697 + 2 from by ring, show (73910013 : ℕ) = 33 * 2239697 + 12 from by ring,
      show (62711524 : ℕ) = 28 * 2239697 + 8 from by ring]; exact macro_mod2_sn 2239697
  apply stepNat_haltsIn_add (m := 413896071) (c₂ := ⟨0, 0, 0, 487806086⟩)
  · rw [show (73910013 : ℕ) = 5 * 14782002 + 3 from by ring, show (487806086 : ℕ) = 33 * 14782002 + 20 from by ring,
      show (413896071 : ℕ) = 28 * 14782002 + 15 from by ring]; exact macro_mod3_sn 14782002
  refine ⟨⟨0, 0, 292683652, 0⟩, ?_, rfl⟩
  rw [show (487806086 : ℕ) = 5 * 97561217 + 1 from by ring, show (292683652 : ℕ) = 1 + 3 * 97561217 from by ring,
    show (975612172 : ℕ) = 10 * 97561217 + 2 from by ring]
  exact macro_halt_sn 97561217

end Sz22_halted_692_20
