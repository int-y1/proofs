import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_halted_692 #9: [4/15, 9/14, 125/2, 7/5, 10/7]

Vector representation:
```
 2 -1 -1  0
-1  2  0 -1
-1  0  3  0
 0  0 -1  1
 1  0  1 -1
```

This Fractran program halts in 213713825473 steps.

Author: Claude
-/

namespace Sz22_halted_692_9

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a+1, b, c, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b, c+1, d⟩
  | _ => none

private theorem r4_gen : ∀ k c d, (⟨0, 0, c + k, d⟩ : Q) [fm]⊢^{k} ⟨0, 0, c, d + k⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · simp; rfl
  rw [show c + (k + 1) = (c + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨0, 0, (c + k) + 1, d⟩ = some ⟨0, 0, c + k, d + 1⟩; simp [fm]
  rw [show d + (1 + k) = (d + 1) + k from by ring]; exact ih c (d + 1)

private theorem r3_drain_sn : ∀ k a c, (⟨a + k, 0, c, 0⟩ : Q) [fm]⊢^{k} ⟨a, 0, c + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · simp; rfl
  rw [show a + (k + 1) = (a + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨(a + k) + 1, 0, c, 0⟩ = some ⟨a + k, 0, c + 3, 0⟩; simp [fm]
  rw [show c + 3 * (1 + k) = c + 3 + 3 * k from by ring]; exact ih a (c + 3)

private theorem round_b0 : ∀ d, (⟨0, 0, 0, d + 4⟩ : Q) [fm]⊢^{5} ⟨0, 5, 0, d⟩ := by
  intro d
  rw [show (5 : ℕ) = 1 + (1 + (1 + (1 + 1))) from by ring]
  apply stepNat_trans 1 _
  · show fm ⟨0, 0, 0, d + 4⟩ = some ⟨1, 0, 1, d + 3⟩; simp [fm]
  apply stepNat_trans 1 _
  · show fm ⟨1, 0, 1, d + 3⟩ = some ⟨0, 2, 1, d + 2⟩; simp [fm]
  apply stepNat_trans 1 _
  · show fm ⟨0, 2, 1, d + 2⟩ = some ⟨2, 1, 0, d + 2⟩; simp [fm]
  apply stepNat_trans 1 1
  · show fm ⟨2, 1, 0, d + 2⟩ = some ⟨1, 3, 0, d + 1⟩; simp [fm]
  show fm ⟨1, 3, 0, d + 1⟩ = some ⟨0, 5, 0, d⟩; simp [fm]

private theorem round_bpos : ∀ b d, (⟨0, b + 1, 0, d + 4⟩ : Q) [fm]⊢^{5} ⟨0, b + 6, 0, d⟩ := by
  intro b d
  rw [show (5 : ℕ) = 1 + (1 + (1 + (1 + 1))) from by ring]
  apply stepNat_trans 1 _
  · show fm ⟨0, b + 1, 0, d + 4⟩ = some ⟨1, b + 1, 1, d + 3⟩; simp [fm]
  apply stepNat_trans 1 _
  · show fm ⟨1, b + 1, 1, d + 3⟩ = some ⟨3, b, 0, d + 3⟩; simp [fm]
  apply stepNat_trans 1 _
  · show fm ⟨3, b, 0, d + 3⟩ = some ⟨2, b + 2, 0, d + 2⟩; simp [fm]
  apply stepNat_trans 1 1
  · show fm ⟨2, b + 2, 0, d + 2⟩ = some ⟨1, b + 4, 0, d + 1⟩; simp [fm]
  show fm ⟨1, b + 4, 0, d + 1⟩ = some ⟨0, b + 6, 0, d⟩; simp [fm]

private theorem inner_chain_pos : ∀ k b d, (⟨0, b + 1, 0, d + 4 * k⟩ : Q) [fm]⊢^{5 * k} ⟨0, b + 1 + 5 * k, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · simp; rfl
  rw [show d + 4 * (k + 1) = (d + 4 * k) + 4 from by ring, show 5 * (k + 1) = 5 + 5 * k from by ring]
  apply stepNat_trans 5 (5 * k)
  · rw [show (b + 1 : ℕ) = b + 1 from rfl]; exact round_bpos b (d + 4 * k)
  rw [show b + 6 = (b + 5) + 1 from by ring]
  have h := ih (b + 5) d
  rw [show b + 5 + 1 + 5 * k = b + 1 + (5 + 5 * k) from by ring] at h; exact h

private theorem inner_chain_sn : ∀ k d, (⟨0, 0, 0, d + 4 * k⟩ : Q) [fm]⊢^{5 * k} ⟨0, 5 * k, 0, d⟩ := by
  intro k d
  rcases k with _ | k
  · simp; rfl
  rw [show 4 * (k + 1) = 4 + 4 * k from by ring, show d + (4 + 4 * k) = (d + 4 * k) + 4 from by ring,
    show 5 * (k + 1) = 5 + 5 * k from by ring]
  apply stepNat_trans 5 (5 * k) (round_b0 (d + 4 * k))
  rw [show (5 : ℕ) = 4 + 1 from by ring]
  have h := inner_chain_pos k 4 d
  rw [show 4 + 1 + 5 * k = 5 + 5 * k from by ring] at h; exact h

private theorem drain_chain_sn : ∀ k a b, (⟨a + 1, b + 3 * k, 0, 0⟩ : Q) [fm]⊢^{4 * k} ⟨a + 1 + 5 * k, b, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · simp; rfl
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring, show 4 * (k + 1) = 4 + 4 * k from by ring]
  apply stepNat_trans 4 (4 * k)
  · rw [show (4 : ℕ) = 1 + (1 + (1 + 1)) from by ring]
    apply stepNat_trans 1 _
    · show fm ⟨a + 1, (b + 3 * k) + 3, 0, 0⟩ = some ⟨a, (b + 3 * k) + 3, 3, 0⟩; simp [fm]
    apply stepNat_trans 1 _
    · show fm ⟨a, (b + 3 * k) + 3, 3, 0⟩ = some ⟨a + 2, (b + 3 * k) + 2, 2, 0⟩; simp [fm]
    apply stepNat_trans 1 1
    · show fm ⟨a + 2, (b + 3 * k) + 2, 2, 0⟩ = some ⟨a + 4, (b + 3 * k) + 1, 1, 0⟩; simp [fm]
    show fm ⟨a + 4, (b + 3 * k) + 1, 1, 0⟩ = some ⟨a + 6, b + 3 * k, 0, 0⟩; simp [fm]
  rw [show a + 6 = (a + 5) + 1 from by ring, show a + 1 + 5 * (k + 1) = (a + 5) + 1 + 5 * k from by ring]
  exact ih (a + 5) b

private theorem boundary_r3_sn : ∀ b, (⟨0, b, 0, 3⟩ : Q) [fm]⊢^{4} ⟨1, b + 3, 0, 0⟩ := by
  intro b
  rcases b with _ | b
  · rw [show (4 : ℕ) = 1 + (1 + (1 + 1)) from by ring]
    apply stepNat_trans 1 _
    · show fm ⟨0, 0, 0, 3⟩ = some ⟨1, 0, 1, 2⟩; simp [fm]
    apply stepNat_trans 1 _
    · show fm ⟨1, 0, 1, 2⟩ = some ⟨0, 2, 1, 1⟩; simp [fm]
    apply stepNat_trans 1 1
    · show fm ⟨0, 2, 1, 1⟩ = some ⟨2, 1, 0, 1⟩; simp [fm]
    show fm ⟨2, 1, 0, 1⟩ = some ⟨1, 3, 0, 0⟩; simp [fm]
  · rw [show (4 : ℕ) = 1 + (1 + (1 + 1)) from by ring]
    apply stepNat_trans 1 _
    · show fm ⟨0, b + 1, 0, 3⟩ = some ⟨1, b + 1, 1, 2⟩; simp [fm]
    apply stepNat_trans 1 _
    · show fm ⟨1, b + 1, 1, 2⟩ = some ⟨3, b, 0, 2⟩; simp [fm]
    apply stepNat_trans 1 1
    · show fm ⟨3, b, 0, 2⟩ = some ⟨2, b + 2, 0, 1⟩; simp [fm]
    show fm ⟨2, b + 2, 0, 1⟩ = some ⟨1, b + 4, 0, 0⟩; simp [fm]

private theorem boundary_r2_sn : ∀ b, (⟨0, b + 1, 0, 2⟩ : Q) [fm]⊢^{3} ⟨2, b + 2, 0, 0⟩ := by
  intro b
  rw [show (3 : ℕ) = 1 + (1 + 1) from by ring]
  apply stepNat_trans 1 _
  · show fm ⟨0, b + 1, 0, 2⟩ = some ⟨1, b + 1, 1, 1⟩; simp [fm]
  apply stepNat_trans 1 1
  · show fm ⟨1, b + 1, 1, 1⟩ = some ⟨3, b, 0, 1⟩; simp [fm]
  show fm ⟨3, b, 0, 1⟩ = some ⟨2, b + 2, 0, 0⟩; simp [fm]

private theorem boundary_r1_sn : ∀ b, (⟨0, b + 1, 0, 1⟩ : Q) [fm]⊢^{2} ⟨3, b, 0, 0⟩ := by
  intro b
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepNat_trans 1 1
  · show fm ⟨0, b + 1, 0, 1⟩ = some ⟨1, b + 1, 1, 0⟩; simp [fm]
  show fm ⟨1, b + 1, 1, 0⟩ = some ⟨3, b, 0, 0⟩; simp [fm]

private theorem r3r4_sn : ∀ k, (⟨k, 0, 0, 0⟩ : Q) [fm]⊢^{4 * k} ⟨0, 0, 0, 3 * k⟩ := by
  intro k
  have h1 := r3_drain_sn k 0 0
  rw [show 0 + k = k from by ring, show 0 + 3 * k = 3 * k from by ring] at h1
  have h2 := r4_gen (3 * k) 0 0
  rw [show 0 + 3 * k = 3 * k from by ring] at h2
  rw [show (4 * k : ℕ) = k + 3 * k from by ring]
  exact stepNat_trans k (3 * k) h1 h2

private theorem macro_r3_sn : ∀ m, (⟨0, 0, 0, 12 * m + 3⟩ : Q) [fm]⊢^{135 * m + 32} ⟨0, 0, 0, 75 * m + 18⟩ := by
  intro m
  rw [show 12 * m + 3 = 3 + 4 * (3 * m) from by ring,
    show 135 * m + 32 = 5 * (3 * m) + (4 + (4 * (5 * m + 1) + 4 * (25 * m + 6))) from by ring]
  apply stepNat_trans (5 * (3 * m)) _ (inner_chain_sn (3 * m) 3)
  rw [show 5 * (3 * m) = 15 * m from by ring]
  apply stepNat_trans 4 _ (boundary_r3_sn (15 * m))
  rw [show (1 : ℕ) = 0 + 1 from by ring, show 15 * m + 3 = 0 + 3 * (5 * m + 1) from by ring]
  apply stepNat_trans (4 * (5 * m + 1)) (4 * (25 * m + 6))
  · have h := drain_chain_sn (5 * m + 1) 0 0
    rw [show 0 + 1 + 5 * (5 * m + 1) = 25 * m + 6 from by ring] at h; exact h
  have h := r3r4_sn (25 * m + 6)
  rw [show 3 * (25 * m + 6) = 75 * m + 18 from by ring] at h; exact h

private theorem macro_r2_sn : ∀ m, (⟨0, 0, 0, 12 * m + 6⟩ : Q) [fm]⊢^{135 * m + 64} ⟨0, 0, 0, 75 * m + 36⟩ := by
  intro m
  rw [show 12 * m + 6 = 2 + 4 * (3 * m + 1) from by ring,
    show 135 * m + 64 = 5 * (3 * m + 1) + (3 + (4 * (5 * m + 2) + 4 * (25 * m + 12))) from by ring]
  apply stepNat_trans (5 * (3 * m + 1)) _ (inner_chain_sn (3 * m + 1) 2)
  rw [show 5 * (3 * m + 1) = (15 * m + 4) + 1 from by ring]
  apply stepNat_trans 3 _ (boundary_r2_sn (15 * m + 4))
  rw [show 15 * m + 4 + 2 = 15 * m + 6 from by ring,
    show (2 : ℕ) = 1 + 1 from by ring, show 15 * m + 6 = 0 + 3 * (5 * m + 2) from by ring]
  apply stepNat_trans (4 * (5 * m + 2)) (4 * (25 * m + 12))
  · have h := drain_chain_sn (5 * m + 2) 1 0
    rw [show 1 + 1 + 5 * (5 * m + 2) = 25 * m + 12 from by ring] at h; exact h
  have h := r3r4_sn (25 * m + 12)
  rw [show 3 * (25 * m + 12) = 75 * m + 36 from by ring] at h; exact h

private theorem macro_r1_sn : ∀ m, (⟨0, 0, 0, 12 * m + 9⟩ : Q) [fm]⊢^{135 * m + 96} ⟨0, 0, 0, 75 * m + 54⟩ := by
  intro m
  rw [show 12 * m + 9 = 1 + 4 * (3 * m + 2) from by ring,
    show 135 * m + 96 = 5 * (3 * m + 2) + (2 + (4 * (5 * m + 3) + 4 * (25 * m + 18))) from by ring]
  apply stepNat_trans (5 * (3 * m + 2)) _ (inner_chain_sn (3 * m + 2) 1)
  rw [show 5 * (3 * m + 2) = (15 * m + 9) + 1 from by ring]
  apply stepNat_trans 2 _ (boundary_r1_sn (15 * m + 9))
  rw [show (3 : ℕ) = 2 + 1 from by ring, show (15 * m + 9 : ℕ) = 0 + 3 * (5 * m + 3) from by ring]
  apply stepNat_trans (4 * (5 * m + 3)) (4 * (25 * m + 18))
  · have h := drain_chain_sn (5 * m + 3) 2 0
    rw [show 2 + 1 + 5 * (5 * m + 3) = 25 * m + 18 from by ring] at h; exact h
  have h := r3r4_sn (25 * m + 18)
  rw [show 3 * (25 * m + 18) = 75 * m + 54 from by ring] at h; exact h

private theorem macro_halt_sn : ∀ q, (⟨0, 0, 0, 4 * q⟩ : Q) [fm]⊢^{5 * q} ⟨0, 5 * q, 0, 0⟩ := by
  intro q
  rw [show 4 * q = 0 + 4 * q from by ring]
  exact inner_chain_sn q 0

theorem fm_haltsIn : haltsIn fm c₀ 213713825473 := by
  apply stepNat_haltsIn_add (m := 4) (c₂ := ⟨0, 0, 0, 3⟩)
  · show stepNat fm 4 c₀ = some ⟨0, 0, 0, 3⟩; rfl
  apply stepNat_haltsIn_add (m := 32) (c₂ := ⟨0, 0, 0, 18⟩)
  · rw [show (3 : ℕ) = 12 * 0 + 3 from by ring,
      show (18 : ℕ) = 75 * 0 + 18 from by ring,
      show (32 : ℕ) = 135 * 0 + 32 from by ring]
    exact macro_r3_sn 0
  apply stepNat_haltsIn_add (m := 199) (c₂ := ⟨0, 0, 0, 111⟩)
  · rw [show (18 : ℕ) = 12 * 1 + 6 from by ring,
      show (111 : ℕ) = 75 * 1 + 36 from by ring,
      show (199 : ℕ) = 135 * 1 + 64 from by ring]
    exact macro_r2_sn 1
  apply stepNat_haltsIn_add (m := 1247) (c₂ := ⟨0, 0, 0, 693⟩)
  · rw [show (111 : ℕ) = 12 * 9 + 3 from by ring,
      show (693 : ℕ) = 75 * 9 + 18 from by ring,
      show (1247 : ℕ) = 135 * 9 + 32 from by ring]
    exact macro_r3_sn 9
  apply stepNat_haltsIn_add (m := 7791) (c₂ := ⟨0, 0, 0, 4329⟩)
  · rw [show (693 : ℕ) = 12 * 57 + 9 from by ring,
      show (4329 : ℕ) = 75 * 57 + 54 from by ring,
      show (7791 : ℕ) = 135 * 57 + 96 from by ring]
    exact macro_r1_sn 57
  apply stepNat_haltsIn_add (m := 48696) (c₂ := ⟨0, 0, 0, 27054⟩)
  · rw [show (4329 : ℕ) = 12 * 360 + 9 from by ring,
      show (27054 : ℕ) = 75 * 360 + 54 from by ring,
      show (48696 : ℕ) = 135 * 360 + 96 from by ring]
    exact macro_r1_sn 360
  apply stepNat_haltsIn_add (m := 304354) (c₂ := ⟨0, 0, 0, 169086⟩)
  · rw [show (27054 : ℕ) = 12 * 2254 + 6 from by ring,
      show (169086 : ℕ) = 75 * 2254 + 36 from by ring,
      show (304354 : ℕ) = 135 * 2254 + 64 from by ring]
    exact macro_r2_sn 2254
  apply stepNat_haltsIn_add (m := 1902214) (c₂ := ⟨0, 0, 0, 1056786⟩)
  · rw [show (169086 : ℕ) = 12 * 14090 + 6 from by ring,
      show (1056786 : ℕ) = 75 * 14090 + 36 from by ring,
      show (1902214 : ℕ) = 135 * 14090 + 64 from by ring]
    exact macro_r2_sn 14090
  apply stepNat_haltsIn_add (m := 11888839) (c₂ := ⟨0, 0, 0, 6604911⟩)
  · rw [show (1056786 : ℕ) = 12 * 88065 + 6 from by ring,
      show (6604911 : ℕ) = 75 * 88065 + 36 from by ring,
      show (11888839 : ℕ) = 135 * 88065 + 64 from by ring]
    exact macro_r2_sn 88065
  apply stepNat_haltsIn_add (m := 74305247) (c₂ := ⟨0, 0, 0, 41280693⟩)
  · rw [show (6604911 : ℕ) = 12 * 550409 + 3 from by ring,
      show (41280693 : ℕ) = 75 * 550409 + 18 from by ring,
      show (74305247 : ℕ) = 135 * 550409 + 32 from by ring]
    exact macro_r3_sn 550409
  apply stepNat_haltsIn_add (m := 464407791) (c₂ := ⟨0, 0, 0, 258004329⟩)
  · rw [show (41280693 : ℕ) = 12 * 3440057 + 9 from by ring,
      show (258004329 : ℕ) = 75 * 3440057 + 54 from by ring,
      show (464407791 : ℕ) = 135 * 3440057 + 96 from by ring]
    exact macro_r1_sn 3440057
  apply stepNat_haltsIn_add (m := 2902548696) (c₂ := ⟨0, 0, 0, 1612527054⟩)
  · rw [show (258004329 : ℕ) = 12 * 21500360 + 9 from by ring,
      show (1612527054 : ℕ) = 75 * 21500360 + 54 from by ring,
      show (2902548696 : ℕ) = 135 * 21500360 + 96 from by ring]
    exact macro_r1_sn 21500360
  apply stepNat_haltsIn_add (m := 18140929354) (c₂ := ⟨0, 0, 0, 10078294086⟩)
  · rw [show (1612527054 : ℕ) = 12 * 134377254 + 6 from by ring,
      show (10078294086 : ℕ) = 75 * 134377254 + 36 from by ring,
      show (18140929354 : ℕ) = 135 * 134377254 + 64 from by ring]
    exact macro_r2_sn 134377254
  apply stepNat_haltsIn_add (m := 113380808464) (c₂ := ⟨0, 0, 0, 62989338036⟩)
  · rw [show (10078294086 : ℕ) = 12 * 839857840 + 6 from by ring,
      show (62989338036 : ℕ) = 75 * 839857840 + 36 from by ring,
      show (113380808464 : ℕ) = 135 * 839857840 + 64 from by ring]
    exact macro_r2_sn 839857840
  refine ⟨⟨0, 78736672545, 0, 0⟩, ?_, rfl⟩
  rw [show (62989338036 : ℕ) = 4 * 15747334509 from by ring,
    show (78736672545 : ℕ) = 5 * 15747334509 from by ring]
  exact macro_halt_sn 15747334509
