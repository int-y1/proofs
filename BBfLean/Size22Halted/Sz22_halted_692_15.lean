import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_halted_692 #15: [9/10, 125/6, 49/5, 2/7, 15/2]

Vector representation:
```
-1  2 -1  0
-1 -1  3  0
 0  0 -1  2
 1  0  0 -1
-1  1  1  0
```

This Fractran program halts in 83495859886 steps.

Author: Claude
-/

namespace Sz22_halted_692_15

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+1, c+1, d⟩
  | _ => none

private theorem r4_gen : ∀ k a d, (⟨a, 0, 0, d + k⟩ : Q) [fm]⊢^{k} ⟨a + k, 0, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · simp; rfl
  rw [show d + (k + 1) = (d + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨a, 0, 0, (d + k) + 1⟩ = some ⟨a + 1, 0, 0, d + k⟩; simp [fm]
  rw [show a + (1 + k) = (a + 1) + k from by ring]; exact ih (a + 1) d

private theorem r4_sn : ∀ k d, (⟨0, 0, 0, d + k⟩ : Q) [fm]⊢^{k} ⟨k, 0, 0, d⟩ := by
  intro k d; have h := r4_gen k 0 d; simp at h; exact h

private theorem r5r1_open_sn : ∀ a, (⟨a + 2, 0, 0, 0⟩ : Q) [fm]⊢^{2} ⟨a, 3, 0, 0⟩ := by
  intro a; show stepNat fm 2 ⟨a + 2, 0, 0, 0⟩ = some ⟨a, 3, 0, 0⟩; rfl

private theorem full_cycle_gen : ∀ k a b, (⟨a + 4 * k, b + 1, 0, 0⟩ : Q) [fm]⊢^{4 * k} ⟨a, b + 1 + 5 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · simp; rfl
  rw [show a + 4 * (k + 1) = (a + 4 * k) + 4 from by ring,
      show 4 * (k + 1) = 4 + 4 * k from by ring]
  apply stepNat_trans 4 (4 * k)
  · rw [show (a + 4 * k) + 4 = (a + 4 * k + 3) + 1 from by ring]
    show stepNat fm 4 ⟨(a + 4 * k + 3) + 1, b + 1, 0, 0⟩ = some ⟨a + 4 * k, b + 6, 0, 0⟩; rfl
  rw [show b + 6 = (b + 5) + 1 from by ring]
  have h := ih a (b + 5)
  rw [show b + 5 + 1 + 5 * k = b + 1 + 5 * (k + 1) from by ring] at h; exact h

private theorem full_cycle_sn : ∀ k a, (⟨a + 4 * k, 3, 0, 0⟩ : Q) [fm]⊢^{4 * k} ⟨a, 3 + 5 * k, 0, 0⟩ := by
  intro k a; have h := full_cycle_gen k a 2; simp at h
  rw [show 2 + 1 + 5 * k = 3 + 5 * k from by ring] at h; exact h

private theorem partial_r1_sn : ∀ b, (⟨1, b + 1, 0, 0⟩ : Q) [fm]⊢^{4} ⟨0, b, 0, 6⟩ := by
  intro b; show stepNat fm 4 ⟨1, b + 1, 0, 0⟩ = some ⟨0, b, 0, 6⟩; rfl

private theorem partial_r2_sn : ∀ b, (⟨2, b + 1, 0, 0⟩ : Q) [fm]⊢^{4} ⟨0, b + 2, 0, 4⟩ := by
  intro b; show stepNat fm 4 ⟨2, b + 1, 0, 0⟩ = some ⟨0, b + 2, 0, 4⟩; rfl

private theorem partial_r3_sn : ∀ b, (⟨3, b + 1, 0, 0⟩ : Q) [fm]⊢^{4} ⟨0, b + 4, 0, 2⟩ := by
  intro b; show stepNat fm 4 ⟨3, b + 1, 0, 0⟩ = some ⟨0, b + 4, 0, 2⟩; rfl

private theorem drain_b_gen : ∀ k b d, (⟨0, b + k, 0, d + 1⟩ : Q) [fm]⊢^{5 * k} ⟨0, b, 0, d + 1 + 5 * k⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · simp; rfl
  rw [show b + (k + 1) = (b + k) + 1 from by ring, show 5 * (k + 1) = 5 + 5 * k from by ring]
  apply stepNat_trans 5 (5 * k)
  · show stepNat fm 5 ⟨0, (b + k) + 1, 0, d + 1⟩ = some ⟨0, b + k, 0, d + 6⟩; rfl
  rw [show d + 6 = (d + 5) + 1 from by ring]
  have h := ih b (d + 5)
  rw [show d + 5 + 1 + 5 * k = d + 1 + (5 + 5 * k) from by ring] at h; exact h

private theorem drain_b_sn : ∀ k d, (⟨0, k, 0, d + 1⟩ : Q) [fm]⊢^{5 * k} ⟨0, 0, 0, d + 1 + 5 * k⟩ := by
  intro k d; have h := drain_b_gen k 0 d; simp at h; exact h

private theorem macro_r1_sn : ∀ q, (⟨0, 0, 0, 4 * q + 3⟩ : Q) [fm]⊢^{33 * q + 19} ⟨0, 0, 0, 25 * q + 16⟩ := by
  intro q
  rw [show (4 * q + 3 : ℕ) = 0 + (4 * q + 3) from by ring,
      show (33 * q + 19 : ℕ) = (4 * q + 3) + (2 + (4 * q + (4 + 5 * (5 * q + 2)))) from by ring]
  apply stepNat_trans (4 * q + 3) (2 + (4 * q + (4 + 5 * (5 * q + 2)))) (r4_sn (4 * q + 3) 0)
  rw [show (4 * q + 3 : ℕ) = (4 * q + 1) + 2 from by ring]
  apply stepNat_trans 2 (4 * q + (4 + 5 * (5 * q + 2))) (r5r1_open_sn (4 * q + 1))
  rw [show (4 * q + 1 : ℕ) = 1 + 4 * q from by ring]
  apply stepNat_trans (4 * q) (4 + 5 * (5 * q + 2))
  · exact full_cycle_sn q 1
  rw [show 3 + 5 * q = (5 * q + 2) + 1 from by ring]
  apply stepNat_trans 4 (5 * (5 * q + 2)) (partial_r1_sn (5 * q + 2))
  rw [show (6 : ℕ) = 5 + 1 from by ring]
  have h := drain_b_sn (5 * q + 2) 5
  rw [show 5 + 1 + 5 * (5 * q + 2) = 25 * q + 16 from by ring] at h; exact h

private theorem macro_r2_sn : ∀ q, (⟨0, 0, 0, 4 * q + 4⟩ : Q) [fm]⊢^{33 * q + 30} ⟨0, 0, 0, 25 * q + 24⟩ := by
  intro q
  rw [show (4 * q + 4 : ℕ) = 0 + (4 * q + 4) from by ring,
      show (33 * q + 30 : ℕ) = (4 * q + 4) + (2 + (4 * q + (4 + 5 * (5 * q + 4)))) from by ring]
  apply stepNat_trans (4 * q + 4) (2 + (4 * q + (4 + 5 * (5 * q + 4)))) (r4_sn (4 * q + 4) 0)
  rw [show (4 * q + 4 : ℕ) = (4 * q + 2) + 2 from by ring]
  apply stepNat_trans 2 (4 * q + (4 + 5 * (5 * q + 4))) (r5r1_open_sn (4 * q + 2))
  rw [show (4 * q + 2 : ℕ) = 2 + 4 * q from by ring]
  apply stepNat_trans (4 * q) (4 + 5 * (5 * q + 4))
  · exact full_cycle_sn q 2
  rw [show 3 + 5 * q = (5 * q + 2) + 1 from by ring]
  apply stepNat_trans 4 (5 * (5 * q + 4)) (partial_r2_sn (5 * q + 2))
  rw [show (5 * q + 2 + 2 : ℕ) = 5 * q + 4 from by ring, show (4 : ℕ) = 3 + 1 from by ring]
  have h := drain_b_sn (5 * q + 4) 3
  rw [show 3 + 1 + 5 * (5 * q + 4) = 25 * q + 24 from by ring] at h; exact h

private theorem macro_r3_sn : ∀ q, (⟨0, 0, 0, 4 * q + 5⟩ : Q) [fm]⊢^{33 * q + 41} ⟨0, 0, 0, 25 * q + 32⟩ := by
  intro q
  rw [show (4 * q + 5 : ℕ) = 0 + (4 * q + 5) from by ring,
      show (33 * q + 41 : ℕ) = (4 * q + 5) + (2 + (4 * q + (4 + 5 * (5 * q + 6)))) from by ring]
  apply stepNat_trans (4 * q + 5) (2 + (4 * q + (4 + 5 * (5 * q + 6)))) (r4_sn (4 * q + 5) 0)
  rw [show (4 * q + 5 : ℕ) = (4 * q + 3) + 2 from by ring]
  apply stepNat_trans 2 (4 * q + (4 + 5 * (5 * q + 6))) (r5r1_open_sn (4 * q + 3))
  rw [show (4 * q + 3 : ℕ) = 3 + 4 * q from by ring]
  apply stepNat_trans (4 * q) (4 + 5 * (5 * q + 6))
  · exact full_cycle_sn q 3
  rw [show 3 + 5 * q = (5 * q + 2) + 1 from by ring]
  apply stepNat_trans 4 (5 * (5 * q + 6)) (partial_r3_sn (5 * q + 2))
  rw [show (5 * q + 2 + 4 : ℕ) = 5 * q + 6 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  have h := drain_b_sn (5 * q + 6) 1
  rw [show 1 + 1 + 5 * (5 * q + 6) = 25 * q + 32 from by ring] at h; exact h

private theorem macro_halt_sn : ∀ q, (⟨0, 0, 0, 4 * q + 2⟩ : Q) [fm]⊢^{8 * q + 4} ⟨0, 3 + 5 * q, 0, 0⟩ := by
  intro q
  rw [show (4 * q + 2 : ℕ) = 0 + (4 * q + 2) from by ring,
      show (8 * q + 4 : ℕ) = (4 * q + 2) + (2 + 4 * q) from by ring]
  apply stepNat_trans (4 * q + 2) (2 + 4 * q) (r4_sn (4 * q + 2) 0)
  rw [show (4 * q + 2 : ℕ) = (4 * q) + 2 from by ring]
  apply stepNat_trans 2 (4 * q) (r5r1_open_sn (4 * q))
  have h := full_cycle_sn q 0; simp at h
  convert h using 2

theorem fm_haltsIn : haltsIn fm c₀ 83495859886 := by
  apply stepNat_haltsIn_add (m := 7) (c₂ := ⟨0, 0, 0, 7⟩)
  · show stepNat fm 7 c₀ = some ⟨0, 0, 0, 7⟩; rfl
  apply stepNat_haltsIn_add (m := 52) (c₂ := ⟨0, 0, 0, 41⟩)
  · rw [show (7 : ℕ) = 4 * 1 + 3 from by ring, show (41 : ℕ) = 25 * 1 + 16 from by ring,
      show (52 : ℕ) = 33 * 1 + 19 from by ring]; exact macro_r1_sn 1
  apply stepNat_haltsIn_add (m := 338) (c₂ := ⟨0, 0, 0, 257⟩)
  · rw [show (41 : ℕ) = 4 * 9 + 5 from by ring, show (257 : ℕ) = 25 * 9 + 32 from by ring,
      show (338 : ℕ) = 33 * 9 + 41 from by ring]; exact macro_r3_sn 9
  apply stepNat_haltsIn_add (m := 2120) (c₂ := ⟨0, 0, 0, 1607⟩)
  · rw [show (257 : ℕ) = 4 * 63 + 5 from by ring, show (1607 : ℕ) = 25 * 63 + 32 from by ring,
      show (2120 : ℕ) = 33 * 63 + 41 from by ring]; exact macro_r3_sn 63
  apply stepNat_haltsIn_add (m := 13252) (c₂ := ⟨0, 0, 0, 10041⟩)
  · rw [show (1607 : ℕ) = 4 * 401 + 3 from by ring, show (10041 : ℕ) = 25 * 401 + 16 from by ring,
      show (13252 : ℕ) = 33 * 401 + 19 from by ring]; exact macro_r1_sn 401
  apply stepNat_haltsIn_add (m := 82838) (c₂ := ⟨0, 0, 0, 62757⟩)
  · rw [show (10041 : ℕ) = 4 * 2509 + 5 from by ring, show (62757 : ℕ) = 25 * 2509 + 32 from by ring,
      show (82838 : ℕ) = 33 * 2509 + 41 from by ring]; exact macro_r3_sn 2509
  apply stepNat_haltsIn_add (m := 517745) (c₂ := ⟨0, 0, 0, 392232⟩)
  · rw [show (62757 : ℕ) = 4 * 15688 + 5 from by ring, show (392232 : ℕ) = 25 * 15688 + 32 from by ring,
      show (517745 : ℕ) = 33 * 15688 + 41 from by ring]; exact macro_r3_sn 15688
  apply stepNat_haltsIn_add (m := 3235911) (c₂ := ⟨0, 0, 0, 2451449⟩)
  · rw [show (392232 : ℕ) = 4 * 98057 + 4 from by ring, show (2451449 : ℕ) = 25 * 98057 + 24 from by ring,
      show (3235911 : ℕ) = 33 * 98057 + 30 from by ring]; exact macro_r2_sn 98057
  apply stepNat_haltsIn_add (m := 20224454) (c₂ := ⟨0, 0, 0, 15321557⟩)
  · rw [show (2451449 : ℕ) = 4 * 612861 + 5 from by ring, show (15321557 : ℕ) = 25 * 612861 + 32 from by ring,
      show (20224454 : ℕ) = 33 * 612861 + 41 from by ring]; exact macro_r3_sn 612861
  apply stepNat_haltsIn_add (m := 126402845) (c₂ := ⟨0, 0, 0, 95759732⟩)
  · rw [show (15321557 : ℕ) = 4 * 3830388 + 5 from by ring, show (95759732 : ℕ) = 25 * 3830388 + 32 from by ring,
      show (126402845 : ℕ) = 33 * 3830388 + 41 from by ring]; exact macro_r3_sn 3830388
  apply stepNat_haltsIn_add (m := 790017786) (c₂ := ⟨0, 0, 0, 598498324⟩)
  · rw [show (95759732 : ℕ) = 4 * 23939932 + 4 from by ring, show (598498324 : ℕ) = 25 * 23939932 + 24 from by ring,
      show (790017786 : ℕ) = 33 * 23939932 + 30 from by ring]; exact macro_r2_sn 23939932
  apply stepNat_haltsIn_add (m := 4937611170) (c₂ := ⟨0, 0, 0, 3740614524⟩)
  · rw [show (598498324 : ℕ) = 4 * 149624580 + 4 from by ring, show (3740614524 : ℕ) = 25 * 149624580 + 24 from by ring,
      show (4937611170 : ℕ) = 33 * 149624580 + 30 from by ring]; exact macro_r2_sn 149624580
  apply stepNat_haltsIn_add (m := 30860069820) (c₂ := ⟨0, 0, 0, 23378840774⟩)
  · rw [show (3740614524 : ℕ) = 4 * 935153630 + 4 from by ring, show (23378840774 : ℕ) = 25 * 935153630 + 24 from by ring,
      show (30860069820 : ℕ) = 33 * 935153630 + 30 from by ring]; exact macro_r2_sn 935153630
  refine ⟨⟨0, 29223550968, 0, 0⟩, ?_, rfl⟩
  rw [show (23378840774 : ℕ) = 4 * 5844710193 + 2 from by ring, show (29223550968 : ℕ) = 3 + 5 * 5844710193 from by ring,
    show (46757681548 : ℕ) = 8 * 5844710193 + 4 from by ring]
  exact macro_halt_sn 5844710193

end Sz22_halted_692_15
