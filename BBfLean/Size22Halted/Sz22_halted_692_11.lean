import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_halted_692 #11: [9/10, 4/21, 343/2, 5/7, 14/5]

Vector representation:
```
-1  2 -1  0
 2 -1  0 -1
-1  0  0  3
 0  0  1 -1
 1  0 -1  1
```

This Fractran program halts in 213713825473 steps.

Author: Claude
-/

namespace Sz22_halted_692_11

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b+1, c, d+1⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+3⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+1, b, c, d+1⟩
  | _ => none

private theorem r4_gen : ∀ k c d, (⟨0, 0, c, d + k⟩ : Q) [fm]⊢^{k} ⟨0, 0, c + k, d⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · simp; rfl
  rw [show d + (k + 1) = (d + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨0, 0, c, (d + k) + 1⟩ = some ⟨0, 0, c + 1, d + k⟩; simp [fm]
  rw [show c + (1 + k) = (c + 1) + k from by ring]; exact ih (c + 1) d

private theorem r4_sn : ∀ k d, (⟨0, 0, 0, d + k⟩ : Q) [fm]⊢^{k} ⟨0, 0, k, d⟩ := by
  intro k d; have h := r4_gen k 0 d; simp at h; exact h

private theorem r3_drain_sn : ∀ k a d, (⟨a + k, 0, 0, d⟩ : Q) [fm]⊢^{k} ⟨a, 0, 0, d + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · simp; rfl
  rw [show a + (k + 1) = (a + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨(a + k) + 1, 0, 0, d⟩ = some ⟨a + k, 0, 0, d + 3⟩; simp [fm]
  rw [show d + 3 * (1 + k) = d + 3 + 3 * k from by ring]; exact ih a (d + 3)

private theorem inner_chain_sn : ∀ k b c, (⟨0, b, c + 4 * k, 0⟩ : Q) [fm]⊢^{5 * k} ⟨0, b + 5 * k, c, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · simp; rfl
  rw [show c + 4 * (k + 1) = (c + 4 * k) + 4 from by ring, show 5 * (k + 1) = 5 + 5 * k from by ring]
  apply stepNat_trans 5 (5 * k)
  · rw [show (5 : ℕ) = 1 + (1 + (1 + (1 + 1))) from by ring]
    apply stepNat_trans 1 _
    · show fm ⟨0, b, (c + 4 * k) + 4, 0⟩ = some ⟨1, b, (c + 4 * k) + 3, 1⟩; simp [fm]
    apply stepNat_trans 1 _
    · show fm ⟨1, b, (c + 4 * k) + 3, 1⟩ = some ⟨0, b + 2, (c + 4 * k) + 2, 1⟩; simp [fm]
    apply stepNat_trans 1 _
    · show fm ⟨0, b + 2, (c + 4 * k) + 2, 1⟩ = some ⟨2, b + 1, (c + 4 * k) + 2, 0⟩; simp [fm]
    apply stepNat_trans 1 1
    · show fm ⟨2, b + 1, (c + 4 * k) + 2, 0⟩ = some ⟨1, b + 3, (c + 4 * k) + 1, 0⟩; simp [fm]
    show fm ⟨1, b + 3, (c + 4 * k) + 1, 0⟩ = some ⟨0, b + 5, c + 4 * k, 0⟩; simp [fm]
  have h := ih (b + 5) c
  rw [show b + 5 + 5 * k = b + (5 + 5 * k) from by ring] at h; exact h

private theorem drain_chain_sn : ∀ k a b, (⟨a + 1, b + 3 * k, 0, 0⟩ : Q) [fm]⊢^{4 * k} ⟨a + 1 + 5 * k, b, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · simp; rfl
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring, show 4 * (k + 1) = 4 + 4 * k from by ring]
  apply stepNat_trans 4 (4 * k)
  · rw [show (4 : ℕ) = 1 + (1 + (1 + 1)) from by ring]
    apply stepNat_trans 1 _
    · show fm ⟨a + 1, (b + 3 * k) + 3, 0, 0⟩ = some ⟨a, (b + 3 * k) + 3, 0, 3⟩; simp [fm]
    apply stepNat_trans 1 _
    · show fm ⟨a, (b + 3 * k) + 3, 0, 3⟩ = some ⟨a + 2, (b + 3 * k) + 2, 0, 2⟩; simp [fm]
    apply stepNat_trans 1 1
    · show fm ⟨a + 2, (b + 3 * k) + 2, 0, 2⟩ = some ⟨a + 4, (b + 3 * k) + 1, 0, 1⟩; simp [fm]
    show fm ⟨a + 4, (b + 3 * k) + 1, 0, 1⟩ = some ⟨a + 6, b + 3 * k, 0, 0⟩; simp [fm]
  rw [show a + 6 = (a + 5) + 1 from by ring, show a + 1 + 5 * (k + 1) = (a + 5) + 1 + 5 * k from by ring]
  exact ih (a + 5) b

private theorem boundary_r3_sn : ∀ b, (⟨0, b, 3, 0⟩ : Q) [fm]⊢^{4} ⟨1, b + 3, 0, 0⟩ := by
  intro b
  rw [show (4 : ℕ) = 1 + (1 + (1 + 1)) from by ring]
  apply stepNat_trans 1 _
  · show fm ⟨0, b, 3, 0⟩ = some ⟨1, b, 2, 1⟩; simp [fm]
  apply stepNat_trans 1 _
  · show fm ⟨1, b, 2, 1⟩ = some ⟨0, b + 2, 1, 1⟩; simp [fm]
  apply stepNat_trans 1 1
  · show fm ⟨0, b + 2, 1, 1⟩ = some ⟨2, b + 1, 1, 0⟩; simp [fm]
  show fm ⟨2, b + 1, 1, 0⟩ = some ⟨1, b + 3, 0, 0⟩; simp [fm]

private theorem boundary_r2_sn : ∀ b, (⟨0, b, 2, 0⟩ : Q) [fm]⊢^{3} ⟨2, b + 1, 0, 0⟩ := by
  intro b
  rw [show (3 : ℕ) = 1 + (1 + 1) from by ring]
  apply stepNat_trans 1 _
  · show fm ⟨0, b, 2, 0⟩ = some ⟨1, b, 1, 1⟩; simp [fm]
  apply stepNat_trans 1 1
  · show fm ⟨1, b, 1, 1⟩ = some ⟨0, b + 2, 0, 1⟩; simp [fm]
  show fm ⟨0, b + 2, 0, 1⟩ = some ⟨2, b + 1, 0, 0⟩; simp [fm]

private theorem boundary_r1_sn : ∀ b, (⟨0, b + 1, 1, 0⟩ : Q) [fm]⊢^{2} ⟨3, b, 0, 0⟩ := by
  intro b
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepNat_trans 1 1
  · show fm ⟨0, b + 1, 1, 0⟩ = some ⟨1, b + 1, 0, 1⟩; simp [fm]
  show fm ⟨1, b + 1, 0, 1⟩ = some ⟨3, b, 0, 0⟩; simp [fm]

private theorem macro_r3_sn : ∀ m, (⟨0, 0, 0, 12 * m + 3⟩ : Q) [fm]⊢^{72 * m + 17} ⟨0, 0, 0, 75 * m + 18⟩ := by
  intro m
  rw [show 12 * m + 3 = 0 + (12 * m + 3) from by ring,
    show 72 * m + 17 = (12 * m + 3) + (15 * m + (4 + (4 * (5 * m + 1) + (25 * m + 6)))) from by ring]
  apply stepNat_trans (12 * m + 3) _ (r4_sn (12 * m + 3) 0)
  rw [show (12 * m + 3 : ℕ) = 3 + 4 * (3 * m) from by ring]
  rw [show 15 * m + (4 + (4 * (5 * m + 1) + (25 * m + 6))) = 5 * (3 * m) + (4 + (4 * (5 * m + 1) + (25 * m + 6))) from by ring]
  apply stepNat_trans (5 * (3 * m)) _
  · have h := inner_chain_sn (3 * m) 0 3
    rw [show 3 + 4 * (3 * m) = 3 + 4 * (3 * m) from rfl,
      show 0 + 5 * (3 * m) = 15 * m from by ring] at h; exact h
  apply stepNat_trans 4 _
  · exact boundary_r3_sn (15 * m)
  rw [show (1 : ℕ) = 0 + 1 from by ring, show 15 * m + 3 = 0 + 3 * (5 * m + 1) from by ring]
  apply stepNat_trans (4 * (5 * m + 1)) (25 * m + 6)
  · have h := drain_chain_sn (5 * m + 1) 0 0
    rw [show 0 + 1 + 5 * (5 * m + 1) = 25 * m + 6 from by ring] at h; exact h
  have h := r3_drain_sn (25 * m + 6) 0 0
  rw [show 0 + (25 * m + 6) = 25 * m + 6 from by ring,
    show 0 + 3 * (25 * m + 6) = 75 * m + 18 from by ring] at h; exact h

private theorem macro_r2_sn : ∀ m, (⟨0, 0, 0, 12 * m + 6⟩ : Q) [fm]⊢^{72 * m + 34} ⟨0, 0, 0, 75 * m + 36⟩ := by
  intro m
  rw [show 12 * m + 6 = 0 + (12 * m + 6) from by ring,
    show 72 * m + 34 = (12 * m + 6) + (15 * m + 5 + (3 + (4 * (5 * m + 2) + (25 * m + 12)))) from by ring]
  apply stepNat_trans (12 * m + 6) _ (r4_sn (12 * m + 6) 0)
  rw [show (12 * m + 6 : ℕ) = 2 + 4 * (3 * m + 1) from by ring]
  rw [show 15 * m + 5 + (3 + (4 * (5 * m + 2) + (25 * m + 12))) = 5 * (3 * m + 1) + (3 + (4 * (5 * m + 2) + (25 * m + 12))) from by ring]
  apply stepNat_trans (5 * (3 * m + 1)) _
  · have h := inner_chain_sn (3 * m + 1) 0 2
    rw [show 2 + 4 * (3 * m + 1) = 2 + 4 * (3 * m + 1) from rfl,
      show 0 + 5 * (3 * m + 1) = 15 * m + 5 from by ring] at h; exact h
  apply stepNat_trans 3 _
  · exact boundary_r2_sn (15 * m + 5)
  rw [show 15 * m + 5 + 1 = 15 * m + 6 from by ring,
    show (2 : ℕ) = 1 + 1 from by ring, show 15 * m + 6 = 0 + 3 * (5 * m + 2) from by ring]
  apply stepNat_trans (4 * (5 * m + 2)) (25 * m + 12)
  · have h := drain_chain_sn (5 * m + 2) 1 0
    rw [show 1 + 1 + 5 * (5 * m + 2) = 25 * m + 12 from by ring] at h; exact h
  have h := r3_drain_sn (25 * m + 12) 0 0
  rw [show 0 + (25 * m + 12) = 25 * m + 12 from by ring,
    show 0 + 3 * (25 * m + 12) = 75 * m + 36 from by ring] at h; exact h

private theorem macro_r1_sn : ∀ m, (⟨0, 0, 0, 12 * m + 9⟩ : Q) [fm]⊢^{72 * m + 51} ⟨0, 0, 0, 75 * m + 54⟩ := by
  intro m
  rw [show 12 * m + 9 = 0 + (12 * m + 9) from by ring,
    show 72 * m + 51 = (12 * m + 9) + (15 * m + 10 + (2 + (4 * (5 * m + 3) + (25 * m + 18)))) from by ring]
  apply stepNat_trans (12 * m + 9) _ (r4_sn (12 * m + 9) 0)
  rw [show (12 * m + 9 : ℕ) = 1 + 4 * (3 * m + 2) from by ring]
  rw [show 15 * m + 10 + (2 + (4 * (5 * m + 3) + (25 * m + 18))) = 5 * (3 * m + 2) + (2 + (4 * (5 * m + 3) + (25 * m + 18))) from by ring]
  apply stepNat_trans (5 * (3 * m + 2)) _
  · have h := inner_chain_sn (3 * m + 2) 0 1
    rw [show 1 + 4 * (3 * m + 2) = 1 + 4 * (3 * m + 2) from rfl,
      show 0 + 5 * (3 * m + 2) = 15 * m + 10 from by ring] at h; exact h
  apply stepNat_trans 2 _
  · rw [show (15 * m + 10 : ℕ) = (15 * m + 9) + 1 from by ring]
    exact boundary_r1_sn (15 * m + 9)
  rw [show (3 : ℕ) = 2 + 1 from by ring, show (15 * m + 9 : ℕ) = 0 + 3 * (5 * m + 3) from by ring]
  apply stepNat_trans (4 * (5 * m + 3)) (25 * m + 18)
  · have h := drain_chain_sn (5 * m + 3) 2 0
    rw [show 2 + 1 + 5 * (5 * m + 3) = 25 * m + 18 from by ring] at h; exact h
  have h := r3_drain_sn (25 * m + 18) 0 0
  rw [show 0 + (25 * m + 18) = 25 * m + 18 from by ring,
    show 0 + 3 * (25 * m + 18) = 75 * m + 54 from by ring] at h; exact h

private theorem macro_halt_sn : ∀ q, (⟨0, 0, 0, 4 * q⟩ : Q) [fm]⊢^{9 * q} ⟨0, 5 * q, 0, 0⟩ := by
  intro q
  rw [show 4 * q = 0 + (4 * q) from by ring, show 9 * q = (4 * q) + 5 * q from by ring]
  apply stepNat_trans (4 * q) (5 * q) (r4_sn (4 * q) 0)
  rw [show (4 * q : ℕ) = 0 + 4 * q from by ring]
  have h := inner_chain_sn q 0 0
  rw [show 0 + 4 * q = 0 + 4 * q from rfl, show 0 + 5 * q = 5 * q from by ring] at h; exact h

theorem fm_haltsIn : haltsIn fm c₀ 213713825473 := by
  apply stepNat_haltsIn_add (m := 1) (c₂ := ⟨0, 0, 0, 3⟩)
  · show fm c₀ = some ⟨0, 0, 0, 3⟩; rfl
  apply stepNat_haltsIn_add (m := 17) (c₂ := ⟨0, 0, 0, 18⟩)
  · rw [show (3 : ℕ) = 12 * 0 + 3 from by ring,
      show (18 : ℕ) = 75 * 0 + 18 from by ring,
      show (17 : ℕ) = 72 * 0 + 17 from by ring]
    exact macro_r3_sn 0
  apply stepNat_haltsIn_add (m := 106) (c₂ := ⟨0, 0, 0, 111⟩)
  · rw [show (18 : ℕ) = 12 * 1 + 6 from by ring,
      show (111 : ℕ) = 75 * 1 + 36 from by ring,
      show (106 : ℕ) = 72 * 1 + 34 from by ring]
    exact macro_r2_sn 1
  apply stepNat_haltsIn_add (m := 665) (c₂ := ⟨0, 0, 0, 693⟩)
  · rw [show (111 : ℕ) = 12 * 9 + 3 from by ring,
      show (693 : ℕ) = 75 * 9 + 18 from by ring,
      show (665 : ℕ) = 72 * 9 + 17 from by ring]
    exact macro_r3_sn 9
  apply stepNat_haltsIn_add (m := 4155) (c₂ := ⟨0, 0, 0, 4329⟩)
  · rw [show (693 : ℕ) = 12 * 57 + 9 from by ring,
      show (4329 : ℕ) = 75 * 57 + 54 from by ring,
      show (4155 : ℕ) = 72 * 57 + 51 from by ring]
    exact macro_r1_sn 57
  apply stepNat_haltsIn_add (m := 25971) (c₂ := ⟨0, 0, 0, 27054⟩)
  · rw [show (4329 : ℕ) = 12 * 360 + 9 from by ring,
      show (27054 : ℕ) = 75 * 360 + 54 from by ring,
      show (25971 : ℕ) = 72 * 360 + 51 from by ring]
    exact macro_r1_sn 360
  apply stepNat_haltsIn_add (m := 162322) (c₂ := ⟨0, 0, 0, 169086⟩)
  · rw [show (27054 : ℕ) = 12 * 2254 + 6 from by ring,
      show (169086 : ℕ) = 75 * 2254 + 36 from by ring,
      show (162322 : ℕ) = 72 * 2254 + 34 from by ring]
    exact macro_r2_sn 2254
  apply stepNat_haltsIn_add (m := 1014514) (c₂ := ⟨0, 0, 0, 1056786⟩)
  · rw [show (169086 : ℕ) = 12 * 14090 + 6 from by ring,
      show (1056786 : ℕ) = 75 * 14090 + 36 from by ring,
      show (1014514 : ℕ) = 72 * 14090 + 34 from by ring]
    exact macro_r2_sn 14090
  apply stepNat_haltsIn_add (m := 6340714) (c₂ := ⟨0, 0, 0, 6604911⟩)
  · rw [show (1056786 : ℕ) = 12 * 88065 + 6 from by ring,
      show (6604911 : ℕ) = 75 * 88065 + 36 from by ring,
      show (6340714 : ℕ) = 72 * 88065 + 34 from by ring]
    exact macro_r2_sn 88065
  apply stepNat_haltsIn_add (m := 39629465) (c₂ := ⟨0, 0, 0, 41280693⟩)
  · rw [show (6604911 : ℕ) = 12 * 550409 + 3 from by ring,
      show (41280693 : ℕ) = 75 * 550409 + 18 from by ring,
      show (39629465 : ℕ) = 72 * 550409 + 17 from by ring]
    exact macro_r3_sn 550409
  apply stepNat_haltsIn_add (m := 247684155) (c₂ := ⟨0, 0, 0, 258004329⟩)
  · rw [show (41280693 : ℕ) = 12 * 3440057 + 9 from by ring,
      show (258004329 : ℕ) = 75 * 3440057 + 54 from by ring,
      show (247684155 : ℕ) = 72 * 3440057 + 51 from by ring]
    exact macro_r1_sn 3440057
  apply stepNat_haltsIn_add (m := 1548025971) (c₂ := ⟨0, 0, 0, 1612527054⟩)
  · rw [show (258004329 : ℕ) = 12 * 21500360 + 9 from by ring,
      show (1612527054 : ℕ) = 75 * 21500360 + 54 from by ring,
      show (1548025971 : ℕ) = 72 * 21500360 + 51 from by ring]
    exact macro_r1_sn 21500360
  apply stepNat_haltsIn_add (m := 9675162322) (c₂ := ⟨0, 0, 0, 10078294086⟩)
  · rw [show (1612527054 : ℕ) = 12 * 134377254 + 6 from by ring,
      show (10078294086 : ℕ) = 75 * 134377254 + 36 from by ring,
      show (9675162322 : ℕ) = 72 * 134377254 + 34 from by ring]
    exact macro_r2_sn 134377254
  apply stepNat_haltsIn_add (m := 60469764514) (c₂ := ⟨0, 0, 0, 62989338036⟩)
  · rw [show (10078294086 : ℕ) = 12 * 839857840 + 6 from by ring,
      show (62989338036 : ℕ) = 75 * 839857840 + 36 from by ring,
      show (60469764514 : ℕ) = 72 * 839857840 + 34 from by ring]
    exact macro_r2_sn 839857840
  refine ⟨⟨0, 78736672545, 0, 0⟩, ?_, rfl⟩
  rw [show (62989338036 : ℕ) = 4 * 15747334509 from by ring,
    show (141726010581 : ℕ) = 9 * 15747334509 from by ring]
  exact macro_halt_sn 15747334509

end Sz22_halted_692_11
