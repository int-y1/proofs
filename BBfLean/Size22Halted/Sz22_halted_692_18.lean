import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_halted_692 #18: [7/45, 4/5, 125/21, 9/2, 7/3]

Vector representation:
```
 0 -2 -1  1
 2  0 -1  0
 0 -1  3 -1
-1  2  0  0
 0 -1  0  1
```

This Fractran program halts in 8742409840 steps.

Author: Claude
-/

namespace Sz22_halted_692_18

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a, b+1, c, d+1⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

private theorem r4_chain_sn : ∀ k b, (⟨k, b, 0, 0⟩ : Q) [fm]⊢^{k} ⟨0, b + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · simp; rfl
  rw [show (k + 1 : ℕ) = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨1 + k, b, 0, 0⟩ = some ⟨k, b + 2, 0, 0⟩; simp [fm, Nat.add_comm]
  rw [show b + 2 * (1 + k) = (b + 2) + 2 * k from by ring]; exact ih (b + 2)

private theorem drain_one_sn : ∀ b D, (⟨0, b + 7, 3, D⟩ : Q) [fm]⊢^{4} ⟨0, b, 3, D + 2⟩ := by
  intro b D
  apply stepNat_trans 1 3
  · show fm ⟨0, b + 7, 3, D⟩ = some ⟨0, b + 5, 2, D + 1⟩; rfl
  apply stepNat_trans 1 2
  · show fm ⟨0, b + 5, 2, D + 1⟩ = some ⟨0, b + 3, 1, D + 2⟩; rfl
  apply stepNat_trans 1 1
  · show fm ⟨0, b + 3, 1, D + 2⟩ = some ⟨0, b + 1, 0, D + 3⟩; rfl
  show fm ⟨0, b + 1, 0, D + 3⟩ = some ⟨0, b, 3, D + 2⟩; simp [fm]

private theorem drain_loop_sn : ∀ k b D, (⟨0, b + 7 * (k + 1), 3, D⟩ : Q) [fm]⊢^{4 * (k + 1)} ⟨0, b, 3, D + 2 * (k + 1)⟩ := by
  intro k; induction' k with k ih <;> intro b D
  · rw [show 7 * 1 = 7 from by ring, show 4 * 1 = 4 from by ring, show 2 * 1 = 2 from by ring]
    exact drain_one_sn b D
  have h1 := drain_one_sn (b + 7 * (k + 1)) D
  rw [show b + 7 * (k + 1) + 7 = b + 7 * (k + 1 + 1) from by ring] at h1
  have h2 := ih b (D + 2)
  rw [show (D + 2) + 2 * (k + 1) = D + 2 * (k + 1 + 1) from by ring] at h2
  rw [show 4 * (k + 1 + 1) = 4 + 4 * (k + 1) from by ring]
  exact stepNat_trans 4 (4 * (k + 1)) h1 h2

private theorem d_drain_one_sn : ∀ a d, (⟨a + 1, 0, 0, d + 2⟩ : Q) [fm]⊢^{9} ⟨a + 12, 0, 0, d⟩ := by
  intro a d
  apply stepNat_trans 1 8
  · show fm ⟨a + 1, 0, 0, d + 2⟩ = some ⟨a, 2, 0, d + 2⟩; simp [fm]
  apply stepNat_trans 1 7
  · show fm ⟨a, 2, 0, d + 2⟩ = some ⟨a, 1, 3, d + 1⟩; simp [fm]
  apply stepNat_trans 1 6
  · show fm ⟨a, 1, 3, d + 1⟩ = some ⟨a + 2, 1, 2, d + 1⟩; rfl
  apply stepNat_trans 1 5
  · show fm ⟨a + 2, 1, 2, d + 1⟩ = some ⟨a + 4, 1, 1, d + 1⟩; rfl
  apply stepNat_trans 1 4
  · show fm ⟨a + 4, 1, 1, d + 1⟩ = some ⟨a + 6, 1, 0, d + 1⟩; rfl
  apply stepNat_trans 1 3
  · show fm ⟨a + 6, 1, 0, d + 1⟩ = some ⟨a + 6, 0, 3, d⟩; simp [fm]
  apply stepNat_trans 1 2
  · show fm ⟨a + 6, 0, 3, d⟩ = some ⟨a + 8, 0, 2, d⟩; rfl
  apply stepNat_trans 1 1
  · show fm ⟨a + 8, 0, 2, d⟩ = some ⟨a + 10, 0, 1, d⟩; rfl
  show fm ⟨a + 10, 0, 1, d⟩ = some ⟨a + 12, 0, 0, d⟩; rfl

private theorem d_drain_sn : ∀ k a d, (⟨a + 1, 0, 0, d + 2 * (k + 1)⟩ : Q) [fm]⊢^{9 * (k + 1)} ⟨a + 1 + 11 * (k + 1), 0, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · rw [show 2 * 1 = 2 from by ring, show 9 * 1 = 9 from by ring, show a + 1 + 11 * 1 = a + 12 from by ring]
    exact d_drain_one_sn a d
  have h1 := d_drain_one_sn a (d + 2 * (k + 1))
  rw [show d + 2 * (k + 1) + 2 = d + 2 * (k + 1 + 1) from by ring] at h1
  have h2 := ih (a + 11) d
  rw [show a + 12 = (a + 11) + 1 from by ring,
      show (a + 11) + 1 + 11 * (k + 1) = a + 1 + 11 * (k + 1 + 1) from by ring] at h2
  rw [show 9 * (k + 1 + 1) = 9 + 9 * (k + 1) from by ring]
  exact stepNat_trans 9 (9 * (k + 1)) h1 h2

private theorem d1_finish_sn : ∀ a, (⟨a + 1, 0, 0, 1⟩ : Q) [fm]⊢^{a + 11} ⟨0, 2 * a + 13, 0, 0⟩ := by
  intro a
  have h1 : (⟨a + 1, 0, 0, 1⟩ : Q) [fm]⊢^{5} ⟨a + 6, 1, 0, 0⟩ := by
    apply stepNat_trans 1 4
    · show fm ⟨a + 1, 0, 0, 1⟩ = some ⟨a, 2, 0, 1⟩; simp [fm]
    apply stepNat_trans 1 3
    · show fm ⟨a, 2, 0, 1⟩ = some ⟨a, 1, 3, 0⟩; simp [fm]
    apply stepNat_trans 1 2
    · show fm ⟨a, 1, 3, 0⟩ = some ⟨a + 2, 1, 2, 0⟩; rfl
    apply stepNat_trans 1 1
    · show fm ⟨a + 2, 1, 2, 0⟩ = some ⟨a + 4, 1, 1, 0⟩; rfl
    show fm ⟨a + 4, 1, 1, 0⟩ = some ⟨a + 6, 1, 0, 0⟩; rfl
  have h2 := r4_chain_sn (a + 6) 1
  rw [show 1 + 2 * (a + 6) = 2 * a + 13 from by ring] at h2
  rw [show a + 11 = 5 + (a + 6) from by ring]
  exact stepNat_trans 5 (a + 6) h1 h2

private theorem entry_sn : ∀ b, (⟨0, b + 2, 0, 0⟩ : Q) [fm]⊢^{2} ⟨0, b, 3, 0⟩ := by
  intro b
  apply stepNat_trans 1 1
  · show fm ⟨0, b + 2, 0, 0⟩ = some ⟨0, b + 1, 0, 1⟩; simp [fm]
  show fm ⟨0, b + 1, 0, 1⟩ = some ⟨0, b, 3, 0⟩; simp [fm]

private theorem rem0_sn : ∀ D, (⟨0, 0, 3, D⟩ : Q) [fm]⊢^{3} ⟨6, 0, 0, D⟩ := by
  intro D
  apply stepNat_trans 1 2; · show fm ⟨0, 0, 3, D⟩ = some ⟨2, 0, 2, D⟩; rfl
  apply stepNat_trans 1 1; · show fm ⟨2, 0, 2, D⟩ = some ⟨4, 0, 1, D⟩; rfl
  show fm ⟨4, 0, 1, D⟩ = some ⟨6, 0, 0, D⟩; rfl

private theorem rem1_sn : ∀ D, (⟨0, 1, 3, D + 1⟩ : Q) [fm]⊢^{7} ⟨12, 0, 0, D⟩ := by
  intro D
  apply stepNat_trans 1 6; · show fm ⟨0, 1, 3, D + 1⟩ = some ⟨2, 1, 2, D + 1⟩; rfl
  apply stepNat_trans 1 5; · show fm ⟨2, 1, 2, D + 1⟩ = some ⟨4, 1, 1, D + 1⟩; rfl
  apply stepNat_trans 1 4; · show fm ⟨4, 1, 1, D + 1⟩ = some ⟨6, 1, 0, D + 1⟩; rfl
  apply stepNat_trans 1 3; · show fm ⟨6, 1, 0, D + 1⟩ = some ⟨6, 0, 3, D⟩; simp [fm]
  apply stepNat_trans 1 2; · show fm ⟨6, 0, 3, D⟩ = some ⟨8, 0, 2, D⟩; rfl
  apply stepNat_trans 1 1; · show fm ⟨8, 0, 2, D⟩ = some ⟨10, 0, 1, D⟩; rfl
  show fm ⟨10, 0, 1, D⟩ = some ⟨12, 0, 0, D⟩; rfl

private theorem rem2_sn : ∀ D, (⟨0, 2, 3, D⟩ : Q) [fm]⊢^{3} ⟨4, 0, 0, D + 1⟩ := by
  intro D
  apply stepNat_trans 1 2; · show fm ⟨0, 2, 3, D⟩ = some ⟨0, 0, 2, D + 1⟩; rfl
  apply stepNat_trans 1 1; · show fm ⟨0, 0, 2, D + 1⟩ = some ⟨2, 0, 1, D + 1⟩; rfl
  show fm ⟨2, 0, 1, D + 1⟩ = some ⟨4, 0, 0, D + 1⟩; rfl

private theorem rem3_sn : ∀ D, (⟨0, 3, 3, D⟩ : Q) [fm]⊢^{7} ⟨10, 0, 0, D⟩ := by
  intro D
  apply stepNat_trans 1 6; · show fm ⟨0, 3, 3, D⟩ = some ⟨0, 1, 2, D + 1⟩; rfl
  apply stepNat_trans 1 5; · show fm ⟨0, 1, 2, D + 1⟩ = some ⟨2, 1, 1, D + 1⟩; rfl
  apply stepNat_trans 1 4; · show fm ⟨2, 1, 1, D + 1⟩ = some ⟨4, 1, 0, D + 1⟩; rfl
  apply stepNat_trans 1 3; · show fm ⟨4, 1, 0, D + 1⟩ = some ⟨4, 0, 3, D⟩; simp [fm]
  apply stepNat_trans 1 2; · show fm ⟨4, 0, 3, D⟩ = some ⟨6, 0, 2, D⟩; rfl
  apply stepNat_trans 1 1; · show fm ⟨6, 0, 2, D⟩ = some ⟨8, 0, 1, D⟩; rfl
  show fm ⟨8, 0, 1, D⟩ = some ⟨10, 0, 0, D⟩; rfl

private theorem rem4_sn : ∀ D, (⟨0, 4, 3, D⟩ : Q) [fm]⊢^{3} ⟨2, 0, 0, D + 2⟩ := by
  intro D
  apply stepNat_trans 1 2; · show fm ⟨0, 4, 3, D⟩ = some ⟨0, 2, 2, D + 1⟩; rfl
  apply stepNat_trans 1 1; · show fm ⟨0, 2, 2, D + 1⟩ = some ⟨0, 0, 1, D + 2⟩; rfl
  show fm ⟨0, 0, 1, D + 2⟩ = some ⟨2, 0, 0, D + 2⟩; rfl

private theorem rem5_sn : ∀ D, (⟨0, 5, 3, D⟩ : Q) [fm]⊢^{7} ⟨8, 0, 0, D + 1⟩ := by
  intro D
  apply stepNat_trans 1 6; · show fm ⟨0, 5, 3, D⟩ = some ⟨0, 3, 2, D + 1⟩; rfl
  apply stepNat_trans 1 5; · show fm ⟨0, 3, 2, D + 1⟩ = some ⟨0, 1, 1, D + 2⟩; rfl
  apply stepNat_trans 1 4; · show fm ⟨0, 1, 1, D + 2⟩ = some ⟨2, 1, 0, D + 2⟩; rfl
  apply stepNat_trans 1 3; · show fm ⟨2, 1, 0, D + 2⟩ = some ⟨2, 0, 3, D + 1⟩; simp [fm]
  apply stepNat_trans 1 2; · show fm ⟨2, 0, 3, D + 1⟩ = some ⟨4, 0, 2, D + 1⟩; rfl
  apply stepNat_trans 1 1; · show fm ⟨4, 0, 2, D + 1⟩ = some ⟨6, 0, 1, D + 1⟩; rfl
  show fm ⟨6, 0, 1, D + 1⟩ = some ⟨8, 0, 0, D + 1⟩; rfl

private theorem rem6_sn : ∀ D, (⟨0, 6, 3, D⟩ : Q) [fm]⊢^{3} ⟨0, 0, 0, D + 3⟩ := by
  intro D
  apply stepNat_trans 1 2; · show fm ⟨0, 6, 3, D⟩ = some ⟨0, 4, 2, D + 1⟩; rfl
  apply stepNat_trans 1 1; · show fm ⟨0, 4, 2, D + 1⟩ = some ⟨0, 2, 1, D + 2⟩; rfl
  show fm ⟨0, 2, 1, D + 2⟩ = some ⟨0, 0, 0, D + 3⟩; rfl

private theorem macro_r0_sn : ∀ k, (⟨0, 7 * k + 2, 0, 0⟩ : Q) [fm]⊢^{24 * k + 11} ⟨0, 22 * k + 12, 0, 0⟩ := by
  intro k; rcases k with _ | k
  · show stepNat fm 11 ⟨0, 2, 0, 0⟩ = some ⟨0, 12, 0, 0⟩; rfl
  have h1 := entry_sn (7 * (k + 1))
  rw [show 7 * (k + 1) + 2 = 7 * (k + 1) + 2 from rfl] at h1
  have h2 := drain_loop_sn k 0 0
  rw [show 0 + 7 * (k + 1) = 7 * (k + 1) from by ring, show 0 + 2 * (k + 1) = 2 * (k + 1) from by ring] at h2
  have h3 := rem0_sn (2 * (k + 1))
  have h4 := d_drain_sn k 5 0
  rw [show 5 + 1 = 6 from by ring, show 0 + 2 * (k + 1) = 2 * (k + 1) from by ring,
      show 5 + 1 + 11 * (k + 1) = 11 * k + 17 from by ring] at h4
  have h5 := r4_chain_sn (11 * k + 17) 0
  rw [show 0 + 2 * (11 * k + 17) = 22 * (k + 1) + 12 from by ring] at h5
  rw [show 7 * (k + 1) + 2 = 7 * (k + 1) + 2 from rfl,
      show 24 * (k + 1) + 11 = 2 + (4 * (k + 1) + (3 + (9 * (k + 1) + (11 * k + 17)))) from by ring]
  exact stepNat_trans 2 _ h1 (stepNat_trans (4 * (k + 1)) _ h2
    (stepNat_trans 3 _ h3 (stepNat_trans (9 * (k + 1)) _ h4 h5)))

private theorem macro_r1_sn : ∀ k, (⟨0, 7 * (k + 1) + 3, 0, 0⟩ : Q) [fm]⊢^{24 * (k + 1) + 11} ⟨0, 22 * (k + 1) + 13, 0, 0⟩ := by
  intro k; rcases k with _ | k
  · show stepNat fm 35 ⟨0, 10, 0, 0⟩ = some ⟨0, 35, 0, 0⟩; rfl
  have h1 := entry_sn (1 + 7 * (k + 1 + 1))
  rw [show 1 + 7 * (k + 1 + 1) + 2 = 7 * (k + 1 + 1) + 3 from by ring] at h1
  have h2 := drain_loop_sn (k + 1) 1 0
  rw [show 1 + 7 * (k + 1 + 1) = 1 + 7 * (k + 1 + 1) from rfl,
      show 0 + 2 * (k + 1 + 1) = 2 * (k + 1 + 1) from by ring] at h2
  have h3 := rem1_sn (2 * k + 3)
  rw [show 2 * k + 3 + 1 = 2 * (k + 1 + 1) from by ring] at h3
  have h4 := d_drain_sn k 11 1
  rw [show 11 + 1 = 12 from by ring, show 1 + 2 * (k + 1) = 2 * k + 3 from by ring,
      show 11 + 1 + 11 * (k + 1) = 11 * k + 23 from by ring] at h4
  have h5 := d1_finish_sn (11 * k + 22)
  rw [show 11 * k + 22 + 1 = 11 * k + 23 from by ring,
      show 2 * (11 * k + 22) + 13 = 22 * (k + 1 + 1) + 13 from by ring] at h5
  rw [show 24 * (k + 1 + 1) + 11 = 2 + (4 * (k + 1 + 1) + (7 + (9 * (k + 1) + (11 * k + 22 + 11)))) from by ring]
  exact stepNat_trans 2 _ h1 (stepNat_trans (4 * (k + 1 + 1)) _ h2
    (stepNat_trans 7 _ h3 (stepNat_trans (9 * (k + 1)) (11 * k + 22 + 11) h4 h5)))

private theorem macro_r2_sn : ∀ k, (⟨0, 7 * k + 4, 0, 0⟩ : Q) [fm]⊢^{24 * k + 19} ⟨0, 22 * k + 19, 0, 0⟩ := by
  intro k; rcases k with _ | k
  · show stepNat fm 19 ⟨0, 4, 0, 0⟩ = some ⟨0, 19, 0, 0⟩; rfl
  have h1 := entry_sn (2 + 7 * (k + 1))
  rw [show 2 + 7 * (k + 1) + 2 = 7 * (k + 1) + 4 from by ring] at h1
  have h2 := drain_loop_sn k 2 0
  rw [show 2 + 7 * (k + 1) = 2 + 7 * (k + 1) from rfl, show 0 + 2 * (k + 1) = 2 * (k + 1) from by ring] at h2
  have h3 := rem2_sn (2 * (k + 1))
  rw [show 2 * (k + 1) + 1 = 1 + 2 * (k + 1) from by ring] at h3
  have h4 := d_drain_sn k 3 1
  rw [show 3 + 1 = 4 from by ring,
      show 3 + 1 + 11 * (k + 1) = 11 * k + 15 from by ring] at h4
  have h5 := d1_finish_sn (11 * k + 14)
  rw [show 11 * k + 14 + 1 = 11 * k + 15 from by ring,
      show 2 * (11 * k + 14) + 13 = 22 * (k + 1) + 19 from by ring] at h5
  rw [show 24 * (k + 1) + 19 = 2 + (4 * (k + 1) + (3 + (9 * (k + 1) + (11 * k + 14 + 11)))) from by ring]
  exact stepNat_trans 2 _ h1 (stepNat_trans (4 * (k + 1)) _ h2
    (stepNat_trans 3 _ h3 (stepNat_trans (9 * (k + 1)) (11 * k + 14 + 11) h4 h5)))

private theorem macro_r3_sn : ∀ k, (⟨0, 7 * k + 5, 0, 0⟩ : Q) [fm]⊢^{24 * k + 19} ⟨0, 22 * k + 20, 0, 0⟩ := by
  intro k; rcases k with _ | k
  · show stepNat fm 19 ⟨0, 5, 0, 0⟩ = some ⟨0, 20, 0, 0⟩; rfl
  have h1 := entry_sn (3 + 7 * (k + 1))
  rw [show 3 + 7 * (k + 1) + 2 = 7 * (k + 1) + 5 from by ring] at h1
  have h2 := drain_loop_sn k 3 0
  rw [show 3 + 7 * (k + 1) = 3 + 7 * (k + 1) from rfl, show 0 + 2 * (k + 1) = 2 * (k + 1) from by ring] at h2
  have h3 := rem3_sn (2 * (k + 1))
  have h4 := d_drain_sn k 9 0
  rw [show 9 + 1 = 10 from by ring, show 0 + 2 * (k + 1) = 2 * (k + 1) from by ring,
      show 9 + 1 + 11 * (k + 1) = 11 * k + 21 from by ring] at h4
  have h5 := r4_chain_sn (11 * k + 21) 0
  rw [show 0 + 2 * (11 * k + 21) = 22 * (k + 1) + 20 from by ring] at h5
  rw [show 24 * (k + 1) + 19 = 2 + (4 * (k + 1) + (7 + (9 * (k + 1) + (11 * k + 21)))) from by ring]
  exact stepNat_trans 2 _ h1 (stepNat_trans (4 * (k + 1)) _ h2
    (stepNat_trans 7 _ h3 (stepNat_trans (9 * (k + 1)) _ h4 h5)))

private theorem macro_r4_sn : ∀ k, (⟨0, 7 * k + 6, 0, 0⟩ : Q) [fm]⊢^{24 * k + 27} ⟨0, 22 * k + 26, 0, 0⟩ := by
  intro k; rcases k with _ | k
  · show stepNat fm 27 ⟨0, 6, 0, 0⟩ = some ⟨0, 26, 0, 0⟩; rfl
  have h1 := entry_sn (4 + 7 * (k + 1))
  rw [show 4 + 7 * (k + 1) + 2 = 7 * (k + 1) + 6 from by ring] at h1
  have h2 := drain_loop_sn k 4 0
  rw [show 4 + 7 * (k + 1) = 4 + 7 * (k + 1) from rfl, show 0 + 2 * (k + 1) = 2 * (k + 1) from by ring] at h2
  have h3 := rem4_sn (2 * (k + 1))
  rw [show 2 * (k + 1) + 2 = 0 + 2 * (k + 1 + 1) from by ring] at h3
  have h4 := d_drain_sn (k + 1) 1 0
  rw [show 1 + 1 = 2 from by ring,
      show 1 + 1 + 11 * (k + 1 + 1) = 11 * k + 24 from by ring] at h4
  have h5 := r4_chain_sn (11 * k + 24) 0
  rw [show 0 + 2 * (11 * k + 24) = 22 * (k + 1) + 26 from by ring] at h5
  rw [show 24 * (k + 1) + 27 = 2 + (4 * (k + 1) + (3 + (9 * (k + 1 + 1) + (11 * k + 24)))) from by ring]
  exact stepNat_trans 2 _ h1 (stepNat_trans (4 * (k + 1)) _ h2
    (stepNat_trans 3 _ h3 (stepNat_trans (9 * (k + 1 + 1)) _ h4 h5)))

private theorem macro_r5_sn : ∀ k, (⟨0, 7 * (k + 1), 0, 0⟩ : Q) [fm]⊢^{24 * k + 27} ⟨0, 22 * k + 27, 0, 0⟩ := by
  intro k; rcases k with _ | k
  · show stepNat fm 27 ⟨0, 7, 0, 0⟩ = some ⟨0, 27, 0, 0⟩; rfl
  have h1 := entry_sn (5 + 7 * (k + 1))
  rw [show 5 + 7 * (k + 1) + 2 = 7 * (k + 1 + 1) from by ring] at h1
  have h2 := drain_loop_sn k 5 0
  rw [show 5 + 7 * (k + 1) = 5 + 7 * (k + 1) from rfl, show 0 + 2 * (k + 1) = 2 * (k + 1) from by ring] at h2
  have h3 := rem5_sn (2 * (k + 1))
  rw [show 2 * (k + 1) + 1 = 1 + 2 * (k + 1) from by ring] at h3
  have h4 := d_drain_sn k 7 1
  rw [show 7 + 1 = 8 from by ring,
      show 7 + 1 + 11 * (k + 1) = 11 * k + 19 from by ring] at h4
  have h5 := d1_finish_sn (11 * k + 18)
  rw [show 11 * k + 18 + 1 = 11 * k + 19 from by ring,
      show 2 * (11 * k + 18) + 13 = 22 * (k + 1) + 27 from by ring] at h5
  rw [show 24 * (k + 1) + 27 = 2 + (4 * (k + 1) + (7 + (9 * (k + 1) + (11 * k + 18 + 11)))) from by ring]
  exact stepNat_trans 2 _ h1 (stepNat_trans (4 * (k + 1)) _ h2
    (stepNat_trans 7 _ h3 (stepNat_trans (9 * (k + 1)) (11 * k + 18 + 11) h4 h5)))

private theorem macro_halt_sn : ∀ k, haltsIn fm ⟨0, 7 * k + 8, 0, 0⟩ (4 * k + 5) := by
  intro k; rcases k with _ | k
  · refine ⟨⟨0, 0, 0, 3⟩, ?_, rfl⟩; show stepNat fm 5 ⟨0, 8, 0, 0⟩ = some ⟨0, 0, 0, 3⟩; rfl
  refine ⟨⟨0, 0, 0, 2 * k + 5⟩, ?_, rfl⟩
  have h1 := entry_sn (6 + 7 * (k + 1))
  rw [show 6 + 7 * (k + 1) + 2 = 7 * (k + 1) + 8 from by ring] at h1
  have h2 := drain_loop_sn k 6 0
  rw [show 6 + 7 * (k + 1) = 6 + 7 * (k + 1) from rfl, show 0 + 2 * (k + 1) = 2 * (k + 1) from by ring] at h2
  have h3 := rem6_sn (2 * (k + 1))
  rw [show 2 * (k + 1) + 3 = 2 * k + 5 from by ring] at h3
  rw [show 4 * (k + 1) + 5 = 2 + (4 * (k + 1) + 3) from by ring]
  exact stepNat_trans 2 _ h1 (stepNat_trans (4 * (k + 1)) 3 h2 h3)

theorem fm_haltsIn : haltsIn fm c₀ 8742409840 := by
  apply stepNat_haltsIn_add (m := 1) (c₂ := ⟨0, 2, 0, 0⟩)
  · show fm c₀ = some ⟨0, 2, 0, 0⟩; rfl
  apply stepNat_haltsIn_add (m := 11) (c₂ := ⟨0, 12, 0, 0⟩)
  · exact macro_r0_sn 0
  apply stepNat_haltsIn_add (m := 43) (c₂ := ⟨0, 42, 0, 0⟩)
  · rw [show (12 : ℕ) = 7 * 1 + 5 from by ring, show (42 : ℕ) = 22 * 1 + 20 from by ring,
      show (43 : ℕ) = 24 * 1 + 19 from by ring]; exact macro_r3_sn 1
  apply stepNat_haltsIn_add (m := 147) (c₂ := ⟨0, 137, 0, 0⟩)
  · rw [show (42 : ℕ) = 7 * (5 + 1) from by ring, show (137 : ℕ) = 22 * 5 + 27 from by ring,
      show (147 : ℕ) = 24 * 5 + 27 from by ring]; exact macro_r5_sn 5
  apply stepNat_haltsIn_add (m := 475) (c₂ := ⟨0, 437, 0, 0⟩)
  · rw [show (137 : ℕ) = 7 * 19 + 4 from by ring, show (437 : ℕ) = 22 * 19 + 19 from by ring,
      show (475 : ℕ) = 24 * 19 + 19 from by ring]; exact macro_r2_sn 19
  apply stepNat_haltsIn_add (m := 1499) (c₂ := ⟨0, 1377, 0, 0⟩)
  · rw [show (437 : ℕ) = 7 * (61 + 1) + 3 from by ring, show (1377 : ℕ) = 22 * (61 + 1) + 13 from by ring,
      show (1499 : ℕ) = 24 * (61 + 1) + 11 from by ring]; exact macro_r1_sn 61
  apply stepNat_haltsIn_add (m := 4723) (c₂ := ⟨0, 4332, 0, 0⟩)
  · rw [show (1377 : ℕ) = 7 * 196 + 5 from by ring, show (4332 : ℕ) = 22 * 196 + 20 from by ring,
      show (4723 : ℕ) = 24 * 196 + 19 from by ring]; exact macro_r3_sn 196
  apply stepNat_haltsIn_add (m := 14859) (c₂ := ⟨0, 13622, 0, 0⟩)
  · rw [show (4332 : ℕ) = 7 * 618 + 6 from by ring, show (13622 : ℕ) = 22 * 618 + 26 from by ring,
      show (14859 : ℕ) = 24 * 618 + 27 from by ring]; exact macro_r4_sn 618
  apply stepNat_haltsIn_add (m := 46707) (c₂ := ⟨0, 42817, 0, 0⟩)
  · rw [show (13622 : ℕ) = 7 * (1945 + 1) from by ring, show (42817 : ℕ) = 22 * 1945 + 27 from by ring,
      show (46707 : ℕ) = 24 * 1945 + 27 from by ring]; exact macro_r5_sn 1945
  apply stepNat_haltsIn_add (m := 146803) (c₂ := ⟨0, 134572, 0, 0⟩)
  · rw [show (42817 : ℕ) = 7 * 6116 + 5 from by ring, show (134572 : ℕ) = 22 * 6116 + 20 from by ring,
      show (146803 : ℕ) = 24 * 6116 + 19 from by ring]; exact macro_r3_sn 6116
  apply stepNat_haltsIn_add (m := 461395) (c₂ := ⟨0, 422947, 0, 0⟩)
  · rw [show (134572 : ℕ) = 7 * 19224 + 4 from by ring, show (422947 : ℕ) = 22 * 19224 + 19 from by ring,
      show (461395 : ℕ) = 24 * 19224 + 19 from by ring]; exact macro_r2_sn 19224
  apply stepNat_haltsIn_add (m := 1450107) (c₂ := ⟨0, 1329267, 0, 0⟩)
  · rw [show (422947 : ℕ) = 7 * (60420 + 1) from by ring, show (1329267 : ℕ) = 22 * 60420 + 27 from by ring,
      show (1450107 : ℕ) = 24 * 60420 + 27 from by ring]; exact macro_r5_sn 60420
  apply stepNat_haltsIn_add (m := 4557491) (c₂ := ⟨0, 4177702, 0, 0⟩)
  · rw [show (1329267 : ℕ) = 7 * 189895 + 2 from by ring, show (4177702 : ℕ) = 22 * 189895 + 12 from by ring,
      show (4557491 : ℕ) = 24 * 189895 + 11 from by ring]; exact macro_r0_sn 189895
  apply stepNat_haltsIn_add (m := 14323555) (c₂ := ⟨0, 13129927, 0, 0⟩)
  · rw [show (4177702 : ℕ) = 7 * 596814 + 4 from by ring, show (13129927 : ℕ) = 22 * 596814 + 19 from by ring,
      show (14323555 : ℕ) = 24 * 596814 + 19 from by ring]; exact macro_r2_sn 596814
  apply stepNat_haltsIn_add (m := 45016899) (c₂ := ⟨0, 41265492, 0, 0⟩)
  · rw [show (13129927 : ℕ) = 7 * 1875703 + 6 from by ring, show (41265492 : ℕ) = 22 * 1875703 + 26 from by ring,
      show (45016899 : ℕ) = 24 * 1875703 + 27 from by ring]; exact macro_r4_sn 1875703
  apply stepNat_haltsIn_add (m := 141481691) (c₂ := ⟨0, 129691552, 0, 0⟩)
  · rw [show (41265492 : ℕ) = 7 * 5895070 + 2 from by ring, show (129691552 : ℕ) = 22 * 5895070 + 12 from by ring,
      show (141481691 : ℕ) = 24 * 5895070 + 11 from by ring]; exact macro_r0_sn 5895070
  apply stepNat_haltsIn_add (m := 444656755) (c₂ := ⟨0, 407602027, 0, 0⟩)
  · rw [show (129691552 : ℕ) = 7 * 18527364 + 4 from by ring, show (407602027 : ℕ) = 22 * 18527364 + 19 from by ring,
      show (444656755 : ℕ) = 24 * 18527364 + 19 from by ring]; exact macro_r2_sn 18527364
  apply stepNat_haltsIn_add (m := 1397492667) (c₂ := ⟨0, 1281034947, 0, 0⟩)
  · rw [show (407602027 : ℕ) = 7 * (58228860 + 1) from by ring, show (1281034947 : ℕ) = 22 * 58228860 + 27 from by ring,
      show (1397492667 : ℕ) = 24 * 58228860 + 27 from by ring]; exact macro_r5_sn 58228860
  apply stepNat_haltsIn_add (m := 4392119819) (c₂ := ⟨0, 4026109837, 0, 0⟩)
  · rw [show (1281034947 : ℕ) = 7 * (183004991 + 1) + 3 from by ring,
      show (4026109837 : ℕ) = 22 * (183004991 + 1) + 13 from by ring,
      show (4392119819 : ℕ) = 24 * (183004991 + 1) + 11 from by ring]
    exact macro_r1_sn 183004991
  rw [show (4026109837 : ℕ) = 7 * 575158547 + 8 from by ring,
      show (2300634193 : ℕ) = 4 * 575158547 + 5 from by ring]
  exact macro_halt_sn 575158547

end Sz22_halted_692_18
