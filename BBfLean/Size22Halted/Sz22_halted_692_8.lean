import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_halted_692 #8: [7/30, 9/2, 16/35, 5/3, 7/5]

Vector representation:
```
-1 -1 -1  1
-1  2  0  0
 4  0 -1 -1
 0 -1  1  0
 0  0 -1  1
```

This Fractran program halts in 505335817223 steps.

Author: Claude
-/

namespace Sz22_halted_692_8

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+4, b, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

private theorem r2_drain : ∀ k a b d, (⟨a + k, b, 0, d⟩ : Q) [fm]⊢^{k} ⟨a, b + 2 * k, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · simp; rfl
  rw [show a + (k + 1) = (a + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨(a + k) + 1, b, 0, d⟩ = some ⟨a + k, b + 2, 0, d⟩; simp [fm]
  rw [show b + 2 * (1 + k) = (b + 2) + 2 * k from by ring]; exact ih a (b + 2) d

private theorem d_drain_step : ∀ b d, (⟨0, b + 1, 0, d + 1⟩ : Q) [fm]⊢^{6} ⟨0, b + 8, 0, d⟩ := by
  intro b d
  rw [show (6 : ℕ) = 1 + (1 + (1 + (1 + (1 + 1)))) from by ring]
  apply stepNat_trans 1 _
  · show fm ⟨0, b + 1, 0, d + 1⟩ = some ⟨0, b, 1, d + 1⟩; simp [fm]
  apply stepNat_trans 1 _
  · show fm ⟨0, b, 1, d + 1⟩ = some ⟨4, b, 0, d⟩; simp [fm]
  apply stepNat_trans 1 _
  · show fm ⟨4, b, 0, d⟩ = some ⟨3, b + 2, 0, d⟩; simp [fm]
  apply stepNat_trans 1 _
  · show fm ⟨3, b + 2, 0, d⟩ = some ⟨2, b + 4, 0, d⟩; simp [fm]
  apply stepNat_trans 1 1
  · show fm ⟨2, b + 4, 0, d⟩ = some ⟨1, b + 6, 0, d⟩; simp [fm]
  show fm ⟨1, b + 6, 0, d⟩ = some ⟨0, b + 8, 0, d⟩; simp [fm]

private theorem d_drain : ∀ k b d, (⟨0, b + 1, 0, d + k⟩ : Q) [fm]⊢^{6 * k} ⟨0, b + 1 + 7 * k, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · simp; rfl
  rw [show d + (k + 1) = (d + k) + 1 from by ring, show 6 * (k + 1) = 6 + 6 * k from by ring]
  apply stepNat_trans 6 (6 * k)
  · rw [show b + 1 = b + 1 from rfl]; exact d_drain_step b (d + k)
  rw [show b + 1 + 7 * (k + 1) = (b + 7) + 1 + 7 * k from by ring]; exact ih (b + 7) d

private theorem b_to_c : ∀ k b c, (⟨0, b + k, c, 0⟩ : Q) [fm]⊢^{k} ⟨0, b, c + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · simp; rfl
  rw [show b + (k + 1) = (b + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨0, (b + k) + 1, c, 0⟩ = some ⟨0, b + k, c + 1, 0⟩; simp [fm]
  rw [show c + (1 + k) = (c + 1) + k from by ring]; exact ih b (c + 1)

private theorem r5r3 : ∀ c, (⟨0, 0, c + 2, 0⟩ : Q) [fm]⊢^{2} ⟨4, 0, c, 0⟩ := by
  intro c; rfl

private theorem c_drain : ∀ k c d, (⟨4, 0, c + 11 * k, d⟩ : Q) [fm]⊢^{15 * k} ⟨4, 0, c, d + 5 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · simp; rfl
  rw [show c + 11 * (k + 1) = (c + 11 * k) + 11 from by ring, show 15 * (k + 1) = 15 + 15 * k from by ring]
  apply stepNat_trans 15 (15 * k)
  · show stepNat fm 15 ⟨4, 0, (c + 11 * k) + 11, d⟩ = some ⟨4, 0, c + 11 * k, d + 5⟩; rfl
  rw [show d + 5 * (k + 1) = (d + 5) + 5 * k from by ring]; exact ih c (d + 5)

private theorem bnd5 : ∀ d, (⟨4, 0, 5, d⟩ : Q) [fm]⊢^{7} ⟨2, 0, 0, d + 3⟩ := by intro d; rfl
private theorem bnd6 : ∀ d, (⟨4, 0, 6, d⟩ : Q) [fm]⊢^{11} ⟨4, 0, 0, d + 3⟩ := by intro d; rfl
private theorem bnd8 : ∀ d, (⟨4, 0, 8, d⟩ : Q) [fm]⊢^{11} ⟨3, 0, 0, d + 4⟩ := by intro d; rfl
private theorem bnd10 : ∀ d, (⟨4, 0, 10, d⟩ : Q) [fm]⊢^{14} ⟨0, 0, 0, d + 6⟩ := by intro d; rfl
private theorem bnd7e : ∀ d, (⟨4, 0, 7, d⟩ : Q) [fm]⊢^{14} ⟨0, 9, 0, d + 3⟩ := by intro d; rfl
private theorem bnd3e : ∀ d, (⟨4, 0, 3, d⟩ : Q) [fm]⊢^{9} ⟨0, 10, 0, d + 1⟩ := by intro d; rfl
private theorem bnd4e : ∀ d, (⟨4, 0, 4, d⟩ : Q) [fm]⊢^{9} ⟨0, 7, 0, d + 2⟩ := by intro d; rfl

-- #0: (1,0,0,0) -> (4,0,0,0) in 5 steps
private theorem t0 : (c₀ : Q) [fm]⊢^{5} ⟨4, 0, 0, 0⟩ := by
  show stepNat fm 5 ⟨1, 0, 0, 0⟩ = some ⟨4, 0, 0, 0⟩; rfl

-- #1: (4,0,0,0) -> (4,0,0,3) in 25 steps
private theorem t1 : (⟨4, 0, 0, 0⟩ : Q) [fm]⊢^{25} ⟨4, 0, 0, 3⟩ := by
  rw [show (25 : ℕ) = 4 + (8 + (2 + 11)) from by ring]
  apply stepNat_trans 4 _
  · have h := r2_drain 4 0 0 0; simp at h; exact h
  apply stepNat_trans 8 _
  · have h := b_to_c 8 0 0; simp at h; exact h
  rw [show (8 : ℕ) = 6 + 2 from by ring]
  apply stepNat_trans 2 11 (r5r3 6)
  exact bnd6 0

-- #2: (4,0,0,3) -> (2,0,0,13) in 90 steps
private theorem t2 : (⟨4, 0, 0, 3⟩ : Q) [fm]⊢^{90} ⟨2, 0, 0, 13⟩ := by
  rw [show (90 : ℕ) = 4 + (18 + (29 + (2 + (30 + 7)))) from by ring]
  apply stepNat_trans 4 _
  · have h := r2_drain 4 0 0 3; simp at h; exact h
  rw [show (3 : ℕ) = 0 + 3 from by ring]
  apply stepNat_trans 18 _
  · have h := d_drain 3 7 0; rw [show 7 + 1 + 7 * 3 = 29 from by ring] at h; exact h
  apply stepNat_trans 29 _
  · have h := b_to_c 29 0 0; simp at h; exact h
  rw [show (29 : ℕ) = 5 + 11 * 2 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (5 + 11 * 2)
  apply stepNat_trans 30 7
  · have h := c_drain 2 5 0; rw [show 5 * 2 = 10 from by ring] at h; exact h
  exact bnd5 10

-- #3: (2,0,0,13) -> (2,0,0,43) in 304 steps
private theorem t3 : (⟨2, 0, 0, 13⟩ : Q) [fm]⊢^{304} ⟨2, 0, 0, 43⟩ := by
  rw [show (304 : ℕ) = 2 + (78 + (95 + (2 + (120 + 7)))) from by ring]
  apply stepNat_trans 2 _
  · have h := r2_drain 2 0 0 13; simp at h; exact h
  rw [show (13 : ℕ) = 0 + 13 from by ring]
  apply stepNat_trans 78 _
  · have h := d_drain 13 3 0; rw [show 3 + 1 + 7 * 13 = 95 from by ring] at h; exact h
  apply stepNat_trans 95 _
  · have h := b_to_c 95 0 0; simp at h; exact h
  rw [show (95 : ℕ) = 5 + 11 * 8 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (5 + 11 * 8)
  apply stepNat_trans 120 7
  · have h := c_drain 8 5 0; rw [show 5 * 8 = 40 from by ring] at h; exact h
  exact bnd5 40

-- #4: (2,0,0,43) -> (4,0,0,138) in 983 steps
private theorem t4 : (⟨2, 0, 0, 43⟩ : Q) [fm]⊢^{983} ⟨4, 0, 0, 138⟩ := by
  rw [show (983 : ℕ) = 2 + (258 + (305 + (2 + (405 + 11)))) from by ring]
  apply stepNat_trans 2 _
  · have h := r2_drain 2 0 0 43; simp at h; exact h
  rw [show (43 : ℕ) = 0 + 43 from by ring]
  apply stepNat_trans 258 _
  · have h := d_drain 43 3 0; rw [show 3 + 1 + 7 * 43 = 305 from by ring] at h; exact h
  apply stepNat_trans 305 _
  · have h := b_to_c 305 0 0; simp at h; exact h
  rw [show (305 : ℕ) = 6 + 11 * 27 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (6 + 11 * 27)
  apply stepNat_trans 405 11
  · have h := c_drain 27 6 0; rw [show 5 * 27 = 135 from by ring] at h; exact h
  exact bnd6 135

-- #5: (4,0,0,138) -> (3,0,0,1409) in 13118 steps
-- Phases: r2(4) + d_drain(138) + b2c(974) + r5r3 + c_drain(88) + bnd4e
--   + d_drain(442) + b2c(3101) + r5r3 + c_drain(281) + bnd8
private theorem t5 : (⟨4, 0, 0, 138⟩ : Q) [fm]⊢^{13118} ⟨3, 0, 0, 1409⟩ := by
  rw [show (13118 : ℕ) = 4 + (828 + (974 + (2 + (1320 + (9 + (2652 + (3101 + (2 + (4215 + 11))))))))) from by ring]
  apply stepNat_trans 4 _
  · have h := r2_drain 4 0 0 138; simp at h; exact h
  rw [show (138 : ℕ) = 0 + 138 from by ring]
  apply stepNat_trans 828 _
  · have h := d_drain 138 7 0; rw [show 7 + 1 + 7 * 138 = 974 from by ring] at h; exact h
  apply stepNat_trans 974 _
  · have h := b_to_c 974 0 0; simp at h; exact h
  rw [show (974 : ℕ) = 4 + 11 * 88 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (4 + 11 * 88)
  apply stepNat_trans 1320 _
  · have h := c_drain 88 4 0; rw [show 5 * 88 = 440 from by ring] at h; exact h
  apply stepNat_trans 9 _
  · exact bnd4e 440
  rw [show (440 + 2 : ℕ) = 0 + 442 from by ring, show (7 : ℕ) = 6 + 1 from by ring]
  apply stepNat_trans 2652 _
  · have h := d_drain 442 6 0; rw [show 6 + 1 + 7 * 442 = 3101 from by ring] at h; exact h
  apply stepNat_trans 3101 _
  · have h := b_to_c 3101 0 0; simp at h; exact h
  rw [show (3101 : ℕ) = 8 + 11 * 281 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (8 + 11 * 281)
  apply stepNat_trans 4215 11
  · have h := c_drain 281 8 0; rw [show 5 * 281 = 1405 from by ring] at h; exact h
  exact bnd8 1405

-- #6: (3,0,0,1409) -> (4,0,0,4485) in 31783 steps
private theorem t6 : (⟨3, 0, 0, 1409⟩ : Q) [fm]⊢^{31783} ⟨4, 0, 0, 4485⟩ := by
  rw [show (31783 : ℕ) = 3 + (8454 + (9869 + (2 + 13455))) from by ring]
  apply stepNat_trans 3 _
  · have h := r2_drain 3 0 0 1409; simp at h; exact h
  rw [show (1409 : ℕ) = 0 + 1409 from by ring]
  apply stepNat_trans 8454 _
  · have h := d_drain 1409 5 0; rw [show 5 + 1 + 7 * 1409 = 9869 from by ring] at h; exact h
  apply stepNat_trans 9869 _
  · have h := b_to_c 9869 0 0; simp at h; exact h
  rw [show (9869 : ℕ) = 0 + 11 * 897 + 2 from by ring]
  apply stepNat_trans 2 13455
  · exact r5r3 (0 + 11 * 897)
  have h := c_drain 897 0 0; rw [show 5 * 897 = 4485 from by ring] at h; simp at h; exact h

-- #7: (4,0,0,4485) -> (2,0,0,45418) in 422955 steps
private theorem t7 : (⟨4, 0, 0, 4485⟩ : Q) [fm]⊢^{422955} ⟨2, 0, 0, 45418⟩ := by
  rw [show (422955 : ℕ) = 4 + (26910 + (31403 + (2 + (42810 + (14 + (85638 + (99920 + (2 + (136245 + 7))))))))) from by ring]
  apply stepNat_trans 4 _
  · have h := r2_drain 4 0 0 4485; simp at h; exact h
  rw [show (4485 : ℕ) = 0 + 4485 from by ring]
  apply stepNat_trans 26910 _
  · have h := d_drain 4485 7 0; rw [show 7 + 1 + 7 * 4485 = 31403 from by ring] at h; exact h
  apply stepNat_trans 31403 _
  · have h := b_to_c 31403 0 0; simp at h; exact h
  rw [show (31403 : ℕ) = 7 + 11 * 2854 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (7 + 11 * 2854)
  apply stepNat_trans 42810 _
  · have h := c_drain 2854 7 0; rw [show 5 * 2854 = 14270 from by ring] at h; exact h
  apply stepNat_trans 14 _
  · exact bnd7e 14270
  rw [show (14270 + 3 : ℕ) = 0 + 14273 from by ring, show (9 : ℕ) = 8 + 1 from by ring]
  apply stepNat_trans 85638 _
  · have h := d_drain 14273 8 0; rw [show 8 + 1 + 7 * 14273 = 99920 from by ring] at h; exact h
  apply stepNat_trans 99920 _
  · have h := b_to_c 99920 0 0; simp at h; exact h
  rw [show (99920 : ℕ) = 5 + 11 * 9083 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (5 + 11 * 9083)
  apply stepNat_trans 136245 7
  · have h := c_drain 9083 5 0; rw [show 5 * 9083 = 45415 from by ring] at h; exact h
  exact bnd5 45415

-- #8: (2,0,0,45418) -> (4,0,0,144513) in 1023983 steps
private theorem t8 : (⟨2, 0, 0, 45418⟩ : Q) [fm]⊢^{1023983} ⟨4, 0, 0, 144513⟩ := by
  rw [show (1023983 : ℕ) = 2 + (272508 + (317930 + (2 + (433530 + 11)))) from by ring]
  apply stepNat_trans 2 _
  · have h := r2_drain 2 0 0 45418; simp at h; exact h
  rw [show (45418 : ℕ) = 0 + 45418 from by ring]
  apply stepNat_trans 272508 _
  · have h := d_drain 45418 3 0; rw [show 3 + 1 + 7 * 45418 = 317930 from by ring] at h; exact h
  apply stepNat_trans 317930 _
  · have h := b_to_c 317930 0 0; simp at h; exact h
  rw [show (317930 : ℕ) = 6 + 11 * 28902 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (6 + 11 * 28902)
  apply stepNat_trans 433530 11
  · have h := c_drain 28902 6 0; rw [show 5 * 28902 = 144510 from by ring] at h; exact h
  exact bnd6 144510

-- #9: (4,0,0,144513) -> (4,0,0,14811945) in 151563440 steps
-- crem=4 -> crem=3 -> crem=4 -> crem=0
private theorem t9 : (⟨4, 0, 0, 144513⟩ : Q) [fm]⊢^{151563440} ⟨4, 0, 0, 14811945⟩ := by
  rw [show (151563440 : ℕ) = 4 + (867078 + (1011599 + (2 + (1379445 + (9 + (2758902 + (3218726 + (2 + (4389165 + (9 + (8778336 + (10241402 + (2 + (13965540 + (9 + (27931092 + (32586281 + (2 + 44435835)))))))))))))))))) from by ring]
  apply stepNat_trans 4 _
  · have h := r2_drain 4 0 0 144513; simp at h; exact h
  rw [show (144513 : ℕ) = 0 + 144513 from by ring]
  apply stepNat_trans 867078 _
  · have h := d_drain 144513 7 0; rw [show 7 + 1 + 7 * 144513 = 1011599 from by ring] at h; exact h
  apply stepNat_trans 1011599 _
  · have h := b_to_c 1011599 0 0; simp at h; exact h
  rw [show (1011599 : ℕ) = 4 + 11 * 91963 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (4 + 11 * 91963)
  apply stepNat_trans 1379445 _
  · have h := c_drain 91963 4 0; rw [show 5 * 91963 = 459815 from by ring] at h; exact h
  -- bnd4e -> sub-macro 1
  apply stepNat_trans 9 _
  · exact bnd4e 459815
  rw [show (459815 + 2 : ℕ) = 0 + 459817 from by ring, show (7 : ℕ) = 6 + 1 from by ring]
  apply stepNat_trans 2758902 _
  · have h := d_drain 459817 6 0; rw [show 6 + 1 + 7 * 459817 = 3218726 from by ring] at h; exact h
  apply stepNat_trans 3218726 _
  · have h := b_to_c 3218726 0 0; simp at h; exact h
  rw [show (3218726 : ℕ) = 3 + 11 * 292611 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (3 + 11 * 292611)
  apply stepNat_trans 4389165 _
  · have h := c_drain 292611 3 0; rw [show 5 * 292611 = 1463055 from by ring] at h; exact h
  -- bnd3e -> sub-macro 2
  apply stepNat_trans 9 _
  · exact bnd3e 1463055
  rw [show (1463055 + 1 : ℕ) = 0 + 1463056 from by ring, show (10 : ℕ) = 9 + 1 from by ring]
  apply stepNat_trans 8778336 _
  · have h := d_drain 1463056 9 0; rw [show 9 + 1 + 7 * 1463056 = 10241402 from by ring] at h; exact h
  apply stepNat_trans 10241402 _
  · have h := b_to_c 10241402 0 0; simp at h; exact h
  rw [show (10241402 : ℕ) = 4 + 11 * 931036 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (4 + 11 * 931036)
  apply stepNat_trans 13965540 _
  · have h := c_drain 931036 4 0; rw [show 5 * 931036 = 4655180 from by ring] at h; exact h
  -- bnd4e -> sub-macro 3
  apply stepNat_trans 9 _
  · exact bnd4e 4655180
  rw [show (4655180 + 2 : ℕ) = 0 + 4655182 from by ring, show (7 : ℕ) = 6 + 1 from by ring]
  apply stepNat_trans 27931092 _
  · have h := d_drain 4655182 6 0; rw [show 6 + 1 + 7 * 4655182 = 32586281 from by ring] at h; exact h
  apply stepNat_trans 32586281 _
  · have h := b_to_c 32586281 0 0; simp at h; exact h
  rw [show (32586281 : ℕ) = 0 + 11 * 2962389 + 2 from by ring]
  apply stepNat_trans 2 44435835
  · exact r5r3 (0 + 11 * 2962389)
  have h := c_drain 2962389 0 0; rw [show 5 * 2962389 = 14811945 from by ring] at h; simp at h; exact h

-- #10: (4,0,0,14811945) -> (3,0,0,47128919) in 333942055 steps
private theorem t10 : (⟨4, 0, 0, 14811945⟩ : Q) [fm]⊢^{333942055} ⟨3, 0, 0, 47128919⟩ := by
  rw [show (333942055 : ℕ) = 4 + (88871670 + (103683623 + (2 + (141386745 + 11)))) from by ring]
  apply stepNat_trans 4 _
  · have h := r2_drain 4 0 0 14811945; simp at h; exact h
  rw [show (14811945 : ℕ) = 0 + 14811945 from by ring]
  apply stepNat_trans 88871670 _
  · have h := d_drain 14811945 7 0; rw [show 7 + 1 + 7 * 14811945 = 103683623 from by ring] at h; exact h
  apply stepNat_trans 103683623 _
  · have h := b_to_c 103683623 0 0; simp at h; exact h
  rw [show (103683623 : ℕ) = 8 + 11 * 9425783 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (8 + 11 * 9425783)
  apply stepNat_trans 141386745 11
  · have h := c_drain 9425783 8 0; rw [show 5 * 9425783 = 47128915 from by ring] at h; exact h
  exact bnd8 47128915

-- #11: (3,0,0,47128919) -> (4,0,0,4830464823) in 49427804321 steps
-- crem=7 -> crem=3 -> crem=3 -> crem=6
private theorem t11 : (⟨3, 0, 0, 47128919⟩ : Q) [fm]⊢^{49427804321} ⟨4, 0, 0, 4830464823⟩ := by
  rw [show (49427804321 : ℕ) = 3 + (282773514 + (329902439 + (2 + (449866950 + (14 + (899733918 + (1049689580 + (2 + (1431394875 + (9 + (2862789756 + (3339921392 + (2 + (4554438255 + (9 + (9108876516 + (10627022612 + (2 + (14491394460 + 11))))))))))))))))))) from by ring]
  apply stepNat_trans 3 _
  · have h := r2_drain 3 0 0 47128919; simp at h; exact h
  rw [show (47128919 : ℕ) = 0 + 47128919 from by ring]
  apply stepNat_trans 282773514 _
  · have h := d_drain 47128919 5 0; rw [show 5 + 1 + 7 * 47128919 = 329902439 from by ring] at h; exact h
  apply stepNat_trans 329902439 _
  · have h := b_to_c 329902439 0 0; simp at h; exact h
  rw [show (329902439 : ℕ) = 7 + 11 * 29991130 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (7 + 11 * 29991130)
  apply stepNat_trans 449866950 _
  · have h := c_drain 29991130 7 0; rw [show 5 * 29991130 = 149955650 from by ring] at h; exact h
  -- bnd7e -> sub-macro 1
  apply stepNat_trans 14 _
  · exact bnd7e 149955650
  rw [show (149955650 + 3 : ℕ) = 0 + 149955653 from by ring, show (9 : ℕ) = 8 + 1 from by ring]
  apply stepNat_trans 899733918 _
  · have h := d_drain 149955653 8 0; rw [show 8 + 1 + 7 * 149955653 = 1049689580 from by ring] at h; exact h
  apply stepNat_trans 1049689580 _
  · have h := b_to_c 1049689580 0 0; simp at h; exact h
  rw [show (1049689580 : ℕ) = 3 + 11 * 95426325 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (3 + 11 * 95426325)
  apply stepNat_trans 1431394875 _
  · have h := c_drain 95426325 3 0; rw [show 5 * 95426325 = 477131625 from by ring] at h; exact h
  -- bnd3e -> sub-macro 2
  apply stepNat_trans 9 _
  · exact bnd3e 477131625
  rw [show (477131625 + 1 : ℕ) = 0 + 477131626 from by ring, show (10 : ℕ) = 9 + 1 from by ring]
  apply stepNat_trans 2862789756 _
  · have h := d_drain 477131626 9 0; rw [show 9 + 1 + 7 * 477131626 = 3339921392 from by ring] at h; exact h
  apply stepNat_trans 3339921392 _
  · have h := b_to_c 3339921392 0 0; simp at h; exact h
  rw [show (3339921392 : ℕ) = 3 + 11 * 303629217 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (3 + 11 * 303629217)
  apply stepNat_trans 4554438255 _
  · have h := c_drain 303629217 3 0; rw [show 5 * 303629217 = 1518146085 from by ring] at h; exact h
  -- bnd3e -> sub-macro 3
  apply stepNat_trans 9 _
  · exact bnd3e 1518146085
  rw [show (1518146085 + 1 : ℕ) = 0 + 1518146086 from by ring, show (10 : ℕ) = 9 + 1 from by ring]
  apply stepNat_trans 9108876516 _
  · have h := d_drain 1518146086 9 0; rw [show 9 + 1 + 7 * 1518146086 = 10627022612 from by ring] at h; exact h
  apply stepNat_trans 10627022612 _
  · have h := b_to_c 10627022612 0 0; simp at h; exact h
  rw [show (10627022612 : ℕ) = 6 + 11 * 966092964 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (6 + 11 * 966092964)
  apply stepNat_trans 14491394460 11
  · have h := c_drain 966092964 6 0; rw [show 5 * 966092964 = 4830464820 from by ring] at h; exact h
  exact bnd6 4830464820

-- #12: (4,0,0,4830464823) -> HALT (0,0,0,48903466196) in 455421014161 steps
-- crem=7 -> crem=10 (HALT)
private theorem t12 : (⟨4, 0, 0, 4830464823⟩ : Q) [fm]⊢^{455421014161} ⟨0, 0, 0, 48903466196⟩ := by
  rw [show (455421014161 : ℕ) = 4 + (28982788938 + (33813253769 + (2 + (46108982400 + (14 + (92217964818 + (107587625630 + (2 + (146710398570 + 14))))))))) from by ring]
  apply stepNat_trans 4 _
  · have h := r2_drain 4 0 0 4830464823; simp at h; exact h
  rw [show (4830464823 : ℕ) = 0 + 4830464823 from by ring]
  apply stepNat_trans 28982788938 _
  · have h := d_drain 4830464823 7 0; rw [show 7 + 1 + 7 * 4830464823 = 33813253769 from by ring] at h; exact h
  apply stepNat_trans 33813253769 _
  · have h := b_to_c 33813253769 0 0; simp at h; exact h
  rw [show (33813253769 : ℕ) = 7 + 11 * 3073932160 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (7 + 11 * 3073932160)
  apply stepNat_trans 46108982400 _
  · have h := c_drain 3073932160 7 0; rw [show 5 * 3073932160 = 15369660800 from by ring] at h; exact h
  -- bnd7e -> sub-macro
  apply stepNat_trans 14 _
  · exact bnd7e 15369660800
  rw [show (15369660800 + 3 : ℕ) = 0 + 15369660803 from by ring, show (9 : ℕ) = 8 + 1 from by ring]
  apply stepNat_trans 92217964818 _
  · have h := d_drain 15369660803 8 0; rw [show 8 + 1 + 7 * 15369660803 = 107587625630 from by ring] at h; exact h
  apply stepNat_trans 107587625630 _
  · have h := b_to_c 107587625630 0 0; simp at h; exact h
  rw [show (107587625630 : ℕ) = 10 + 11 * 9780693238 + 2 from by ring]
  apply stepNat_trans 2 _
  · exact r5r3 (10 + 11 * 9780693238)
  apply stepNat_trans 146710398570 14
  · have h := c_drain 9780693238 10 0; rw [show 5 * 9780693238 = 48903466190 from by ring] at h; exact h
  exact bnd10 48903466190

theorem fm_haltsIn : haltsIn fm c₀ 505335817223 := by
  apply stepNat_haltsIn_add (m := 5) (c₂ := ⟨4, 0, 0, 0⟩)
  · exact t0
  apply stepNat_haltsIn_add (m := 25) (c₂ := ⟨4, 0, 0, 3⟩)
  · exact t1
  apply stepNat_haltsIn_add (m := 90) (c₂ := ⟨2, 0, 0, 13⟩)
  · exact t2
  apply stepNat_haltsIn_add (m := 304) (c₂ := ⟨2, 0, 0, 43⟩)
  · exact t3
  apply stepNat_haltsIn_add (m := 983) (c₂ := ⟨4, 0, 0, 138⟩)
  · exact t4
  apply stepNat_haltsIn_add (m := 13118) (c₂ := ⟨3, 0, 0, 1409⟩)
  · exact t5
  apply stepNat_haltsIn_add (m := 31783) (c₂ := ⟨4, 0, 0, 4485⟩)
  · exact t6
  apply stepNat_haltsIn_add (m := 422955) (c₂ := ⟨2, 0, 0, 45418⟩)
  · exact t7
  apply stepNat_haltsIn_add (m := 1023983) (c₂ := ⟨4, 0, 0, 144513⟩)
  · exact t8
  apply stepNat_haltsIn_add (m := 151563440) (c₂ := ⟨4, 0, 0, 14811945⟩)
  · exact t9
  apply stepNat_haltsIn_add (m := 333942055) (c₂ := ⟨3, 0, 0, 47128919⟩)
  · exact t10
  apply stepNat_haltsIn_add (m := 49427804321) (c₂ := ⟨4, 0, 0, 4830464823⟩)
  · exact t11
  refine ⟨⟨0, 0, 0, 48903466196⟩, ?_, rfl⟩
  exact t12

end Sz22_halted_692_8
