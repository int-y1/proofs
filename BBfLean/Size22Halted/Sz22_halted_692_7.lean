import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_halted_692 #7: [7/30, 27/2, 8/35, 5/3, 7/5]

Vector representation:
```
-1 -1 -1  1
-1  3  0  0
 3  0 -1 -1
 0 -1  1  0
 0  0 -1  1
```

This Fractran program halts in 7548863488598188537 steps.

Author: Claude
-/

namespace Sz22_halted_692_7

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+3, c, d⟩
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+3, b, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

private theorem r2_drain : ∀ k a b d, (⟨a + k, b, 0, d⟩ : Q) [fm]⊢^{k} ⟨a, b + 3 * k, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · simp; rfl
  rw [show a + (k + 1) = (a + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨(a + k) + 1, b, 0, d⟩ = some ⟨a + k, b + 3, 0, d⟩; simp [fm]
  rw [show b + 3 * (1 + k) = (b + 3) + 3 * k from by ring]; exact ih a (b + 3) d

private theorem d_drain_step : ∀ b d, (⟨0, b + 1, 0, d + 1⟩ : Q) [fm]⊢^{5} ⟨0, b + 9, 0, d⟩ := by
  intro b d
  rw [show (5 : ℕ) = 1 + (1 + (1 + (1 + 1))) from by ring]
  apply stepNat_trans 1 _
  · show fm ⟨0, b + 1, 0, d + 1⟩ = some ⟨0, b, 1, d + 1⟩; simp [fm]
  apply stepNat_trans 1 _
  · show fm ⟨0, b, 1, d + 1⟩ = some ⟨3, b, 0, d⟩; simp [fm]
  apply stepNat_trans 1 _
  · show fm ⟨3, b, 0, d⟩ = some ⟨2, b + 3, 0, d⟩; simp [fm]
  apply stepNat_trans 1 1
  · show fm ⟨2, b + 3, 0, d⟩ = some ⟨1, b + 6, 0, d⟩; simp [fm]
  show fm ⟨1, b + 6, 0, d⟩ = some ⟨0, b + 9, 0, d⟩; simp [fm]

private theorem d_drain : ∀ k b d, (⟨0, b + 1, 0, d + k⟩ : Q) [fm]⊢^{5 * k} ⟨0, b + 1 + 8 * k, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · simp; rfl
  rw [show d + (k + 1) = (d + k) + 1 from by ring, show 5 * (k + 1) = 5 + 5 * k from by ring]
  apply stepNat_trans 5 (5 * k)
  · rw [show b + 1 = b + 1 from rfl]; exact d_drain_step b (d + k)
  rw [show b + 1 + 8 * (k + 1) = (b + 8) + 1 + 8 * k from by ring]; exact ih (b + 8) d

private theorem b_to_c : ∀ k b c, (⟨0, b + k, c, 0⟩ : Q) [fm]⊢^{k} ⟨0, b, c + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · simp; rfl
  rw [show b + (k + 1) = (b + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨0, (b + k) + 1, c, 0⟩ = some ⟨0, b + k, c + 1, 0⟩; simp [fm]
  rw [show c + (1 + k) = (c + 1) + k from by ring]; exact ih b (c + 1)

private theorem r5r3 : ∀ c, (⟨0, 0, c + 2, 0⟩ : Q) [fm]⊢^{2} ⟨3, 0, c, 0⟩ := by
  intro c; rfl

private theorem c_drain : ∀ k c d, (⟨3, 0, c + 13 * k, d⟩ : Q) [fm]⊢^{16 * k} ⟨3, 0, c, d + 5 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · simp; rfl
  rw [show c + 13 * (k + 1) = (c + 13 * k) + 13 from by ring, show 16 * (k + 1) = 16 + 16 * k from by ring]
  apply stepNat_trans 16 (16 * k)
  · show stepNat fm 16 ⟨3, 0, (c + 13 * k) + 13, d⟩ = some ⟨3, 0, c + 13 * k, d + 5⟩; rfl
  rw [show d + 5 * (k + 1) = (d + 5) + 5 * k from by ring]; exact ih c (d + 5)

private theorem bnd_r1 : ∀ d, (⟨3, 0, 1, d⟩ : Q) [fm]⊢^{3} ⟨0, 5, 0, d + 1⟩ := by intro d; rfl
private theorem bnd_r3 : ∀ d, (⟨3, 0, 3, d⟩ : Q) [fm]⊢^{7} ⟨0, 10, 0, d + 1⟩ := by intro d; rfl
private theorem bnd_r4 : ∀ d, (⟨3, 0, 4, d⟩ : Q) [fm]⊢^{5} ⟨2, 0, 0, d + 2⟩ := by intro d; rfl
private theorem bnd_r5 : ∀ d, (⟨3, 0, 5, d⟩ : Q) [fm]⊢^{7} ⟨0, 2, 0, d + 3⟩ := by intro d; rfl
private theorem bnd_r6 : ∀ d, (⟨3, 0, 6, d⟩ : Q) [fm]⊢^{11} ⟨0, 11, 0, d + 2⟩ := by intro d; rfl
private theorem bnd_r7 : ∀ d, (⟨3, 0, 7, d⟩ : Q) [fm]⊢^{11} ⟨0, 7, 0, d + 3⟩ := by intro d; rfl
private theorem bnd_r8 : ∀ d, (⟨3, 0, 8, d⟩ : Q) [fm]⊢^{10} ⟨1, 0, 0, d + 4⟩ := by intro d; rfl
private theorem bnd_r9 : ∀ d, (⟨3, 0, 9, d⟩ : Q) [fm]⊢^{15} ⟨0, 12, 0, d + 3⟩ := by intro d; rfl
private theorem bnd_r10 : ∀ d, (⟨3, 0, 10, d⟩ : Q) [fm]⊢^{15} ⟨0, 8, 0, d + 4⟩ := by intro d; rfl
private theorem bnd_r11 : ∀ d, (⟨3, 0, 11, d⟩ : Q) [fm]⊢^{15} ⟨0, 4, 0, d + 5⟩ := by intro d; rfl
private theorem bnd_r12 : ∀ d, (⟨3, 0, 12, d⟩ : Q) [fm]⊢^{15} ⟨0, 0, 0, d + 6⟩ := by intro d; rfl

private theorem t0_boot : (⟨1, 0, 0, 0⟩ : Q) [fm]⊢^{4} ⟨0, 0, 3, 0⟩ := by
  rw [show (4 : ℕ) = 1 + 3 from by ring]
  apply stepNat_trans 1 3
  · have h := r2_drain 1 0 0 0; simp at h; exact h
  have h := b_to_c 3 0 0; simp at h; exact h

private theorem t0_r0 : (⟨0, 0, 3, 0⟩ : Q) [fm]⊢^{23} ⟨0, 0, 13, 0⟩ := by
  rw [show (23 : ℕ) = 2 + (3 + (5 + 13)) from by ring]
  rw [show (3 : ℕ) = 1 + 13 * 0 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (1 + 13 * 0)
  apply stepNat_trans 3 _; · exact bnd_r1 0
  rw [show (0 + 1 : ℕ) = 0 + 1 from by ring, show (5 : ℕ) = 4 + 1 from by ring]
  apply stepNat_trans 5 13
  · have h := d_drain 1 4 0; rw [show 4 + 1 + 8 * 1 = 13 from by ring] at h; exact h
  have h := b_to_c 13 0 0; simp at h; exact h

private theorem t0_r1 : (⟨0, 0, 13, 0⟩ : Q) [fm]⊢^{86} ⟨0, 0, 44, 0⟩ := by
  rw [show (86 : ℕ) = 2 + (15 + (25 + 44)) from by ring]
  rw [show (13 : ℕ) = 11 + 13 * 0 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (11 + 13 * 0)
  apply stepNat_trans 15 _; · exact bnd_r11 0
  rw [show (0 + 5 : ℕ) = 0 + 5 from by ring, show (4 : ℕ) = 3 + 1 from by ring]
  apply stepNat_trans 25 44
  · have h := d_drain 5 3 0; rw [show 3 + 1 + 8 * 5 = 44 from by ring] at h; exact h
  have h := b_to_c 44 0 0; simp at h; exact h

private theorem t0_r2 : (⟨0, 0, 44, 0⟩ : Q) [fm]⊢^{275} ⟨0, 0, 138, 0⟩ := by
  rw [show (275 : ℕ) = 2 + (48 + (7 + (80 + 138))) from by ring]
  rw [show (44 : ℕ) = 3 + 13 * 3 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (3 + 13 * 3)
  apply stepNat_trans 48 _
  · have h := c_drain 3 3 0; rw [show 5 * 3 = 15 from by ring] at h; exact h
  apply stepNat_trans 7 _; · exact bnd_r3 15
  rw [show (15 + 1 : ℕ) = 0 + 16 from by ring, show (10 : ℕ) = 9 + 1 from by ring]
  apply stepNat_trans 80 138
  · have h := d_drain 16 9 0; rw [show 9 + 1 + 8 * 16 = 138 from by ring] at h; exact h
  have h := b_to_c 138 0 0; simp at h; exact h

private theorem t0_r3 : (⟨0, 0, 138, 0⟩ : Q) [fm]⊢^{860} ⟨0, 0, 427, 0⟩ := by
  rw [show (860 : ℕ) = 2 + (160 + (11 + (260 + 427))) from by ring]
  rw [show (138 : ℕ) = 6 + 13 * 10 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (6 + 13 * 10)
  apply stepNat_trans 160 _
  · have h := c_drain 10 6 0; rw [show 5 * 10 = 50 from by ring] at h; exact h
  apply stepNat_trans 11 _; · exact bnd_r6 50
  rw [show (50 + 2 : ℕ) = 0 + 52 from by ring, show (11 : ℕ) = 10 + 1 from by ring]
  apply stepNat_trans 260 427
  · have h := d_drain 52 10 0; rw [show 10 + 1 + 8 * 52 = 427 from by ring] at h; exact h
  have h := b_to_c 427 0 0; simp at h; exact h

private theorem t0_r4 : (⟨0, 0, 427, 0⟩ : Q) [fm]⊢^{2660} ⟨0, 0, 1316, 0⟩ := by
  rw [show (2660 : ℕ) = 2 + (512 + (15 + (815 + 1316))) from by ring]
  rw [show (427 : ℕ) = 9 + 13 * 32 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (9 + 13 * 32)
  apply stepNat_trans 512 _
  · have h := c_drain 32 9 0; rw [show 5 * 32 = 160 from by ring] at h; exact h
  apply stepNat_trans 15 _; · exact bnd_r9 160
  rw [show (160 + 3 : ℕ) = 0 + 163 from by ring, show (12 : ℕ) = 11 + 1 from by ring]
  apply stepNat_trans 815 1316
  · have h := d_drain 163 11 0; rw [show 11 + 1 + 8 * 163 = 1316 from by ring] at h; exact h
  have h := b_to_c 1316 0 0; simp at h; exact h

private theorem t0_r5 : (⟨0, 0, 1316, 0⟩ : Q) [fm]⊢^{8204} ⟨0, 0, 4053, 0⟩ := by
  rw [show (8204 : ℕ) = 2 + (1616 + (3 + (2530 + 4053))) from by ring]
  rw [show (1316 : ℕ) = 1 + 13 * 101 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (1 + 13 * 101)
  apply stepNat_trans 1616 _
  · have h := c_drain 101 1 0; rw [show 5 * 101 = 505 from by ring] at h; exact h
  apply stepNat_trans 3 _; · exact bnd_r1 505
  rw [show (505 + 1 : ℕ) = 0 + 506 from by ring, show (5 : ℕ) = 4 + 1 from by ring]
  apply stepNat_trans 2530 4053
  · have h := d_drain 506 4 0; rw [show 4 + 1 + 8 * 506 = 4053 from by ring] at h; exact h
  have h := b_to_c 4053 0 0; simp at h; exact h

private theorem t0_r6 : (⟨0, 0, 4053, 0⟩ : Q) [fm]⊢^{4988} ⟨1, 0, 0, 1559⟩ := by
  rw [show (4988 : ℕ) = 2 + (4976 + 10) from by ring]
  rw [show (4053 : ℕ) = 8 + 13 * 311 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (8 + 13 * 311)
  apply stepNat_trans 4976 10
  · have h := c_drain 311 8 0; rw [show 5 * 311 = 1555 from by ring] at h; exact h
  exact bnd_r8 1555

private theorem t0 : (⟨1, 0, 0, 0⟩ : Q) [fm]⊢^{17100} ⟨1, 0, 0, 1559⟩ := by
  rw [show (17100 : ℕ) = 4 + (23 + (86 + (275 + (860 + (2660 + (8204 + (4988))))))) from by ring]
  apply stepNat_trans 4 _
  · exact t0_boot
  apply stepNat_trans 23 _
  · exact t0_r0
  apply stepNat_trans 86 _
  · exact t0_r1
  apply stepNat_trans 275 _
  · exact t0_r2
  apply stepNat_trans 860 _
  · exact t0_r3
  apply stepNat_trans 2660 _
  · exact t0_r4
  apply stepNat_trans 8204 _
  · exact t0_r5
  exact t0_r6

private theorem t1_boot : (⟨1, 0, 0, 1559⟩ : Q) [fm]⊢^{20271} ⟨0, 0, 12475, 0⟩ := by
  rw [show (20271 : ℕ) = 1 + (7795 + 12475) from by ring]
  apply stepNat_trans 1 _
  · have h := r2_drain 1 0 0 1559; simp at h; exact h
  rw [show (1559 : ℕ) = 0 + 1559 from by ring]
  apply stepNat_trans 7795 12475
  · have h := d_drain 1559 2 0; rw [show 2 + 1 + 8 * 1559 = 12475 from by ring] at h; exact h
  have h := b_to_c 12475 0 0; simp at h; exact h

private theorem t1_r0 : (⟨0, 0, 12475, 0⟩ : Q) [fm]⊢^{77729} ⟨0, 0, 38387, 0⟩ := by
  rw [show (77729 : ℕ) = 2 + (15344 + (11 + (23985 + 38387))) from by ring]
  rw [show (12475 : ℕ) = 6 + 13 * 959 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (6 + 13 * 959)
  apply stepNat_trans 15344 _
  · have h := c_drain 959 6 0; rw [show 5 * 959 = 4795 from by ring] at h; exact h
  apply stepNat_trans 11 _; · exact bnd_r6 4795
  rw [show (4795 + 2 : ℕ) = 0 + 4797 from by ring, show (11 : ℕ) = 10 + 1 from by ring]
  apply stepNat_trans 23985 38387
  · have h := d_drain 4797 10 0; rw [show 10 + 1 + 8 * 4797 = 38387 from by ring] at h; exact h
  have h := b_to_c 38387 0 0; simp at h; exact h

private theorem t1_r1 : (⟨0, 0, 38387, 0⟩ : Q) [fm]⊢^{239180} ⟨0, 0, 118116, 0⟩ := by
  rw [show (239180 : ℕ) = 2 + (47232 + (15 + (73815 + 118116))) from by ring]
  rw [show (38387 : ℕ) = 9 + 13 * 2952 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (9 + 13 * 2952)
  apply stepNat_trans 47232 _
  · have h := c_drain 2952 9 0; rw [show 5 * 2952 = 14760 from by ring] at h; exact h
  apply stepNat_trans 15 _; · exact bnd_r9 14760
  rw [show (14760 + 3 : ℕ) = 0 + 14763 from by ring, show (12 : ℕ) = 11 + 1 from by ring]
  apply stepNat_trans 73815 118116
  · have h := d_drain 14763 11 0; rw [show 11 + 1 + 8 * 14763 = 118116 from by ring] at h; exact h
  have h := b_to_c 118116 0 0; simp at h; exact h

private theorem t1_r2 : (⟨0, 0, 118116, 0⟩ : Q) [fm]⊢^{735953} ⟨0, 0, 363436, 0⟩ := by
  rw [show (735953 : ℕ) = 2 + (145360 + (15 + (227140 + 363436))) from by ring]
  rw [show (118116 : ℕ) = 9 + 13 * 9085 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (9 + 13 * 9085)
  apply stepNat_trans 145360 _
  · have h := c_drain 9085 9 0; rw [show 5 * 9085 = 45425 from by ring] at h; exact h
  apply stepNat_trans 15 _; · exact bnd_r9 45425
  rw [show (45425 + 3 : ℕ) = 0 + 45428 from by ring, show (12 : ℕ) = 11 + 1 from by ring]
  apply stepNat_trans 227140 363436
  · have h := d_drain 45428 11 0; rw [show 11 + 1 + 8 * 45428 = 363436 from by ring] at h; exact h
  have h := b_to_c 363436 0 0; simp at h; exact h

private theorem t1_r3 : (⟨0, 0, 363436, 0⟩ : Q) [fm]⊢^{2264486} ⟨0, 0, 1118267, 0⟩ := by
  rw [show (2264486 : ℕ) = 2 + (447296 + (11 + (698910 + 1118267))) from by ring]
  rw [show (363436 : ℕ) = 6 + 13 * 27956 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (6 + 13 * 27956)
  apply stepNat_trans 447296 _
  · have h := c_drain 27956 6 0; rw [show 5 * 27956 = 139780 from by ring] at h; exact h
  apply stepNat_trans 11 _; · exact bnd_r6 139780
  rw [show (139780 + 2 : ℕ) = 0 + 139782 from by ring, show (11 : ℕ) = 10 + 1 from by ring]
  apply stepNat_trans 698910 1118267
  · have h := d_drain 139782 10 0; rw [show 10 + 1 + 8 * 139782 = 1118267 from by ring] at h; exact h
  have h := b_to_c 1118267 0 0; simp at h; exact h

private theorem t1_r4 : (⟨0, 0, 1118267, 0⟩ : Q) [fm]⊢^{6967670} ⟨0, 0, 3440826, 0⟩ := by
  rw [show (6967670 : ℕ) = 2 + (1376320 + (7 + (2150515 + 3440826))) from by ring]
  rw [show (1118267 : ℕ) = 5 + 13 * 86020 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (5 + 13 * 86020)
  apply stepNat_trans 1376320 _
  · have h := c_drain 86020 5 0; rw [show 5 * 86020 = 430100 from by ring] at h; exact h
  apply stepNat_trans 7 _; · exact bnd_r5 430100
  rw [show (430100 + 3 : ℕ) = 0 + 430103 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  apply stepNat_trans 2150515 3440826
  · have h := d_drain 430103 1 0; rw [show 1 + 1 + 8 * 430103 = 3440826 from by ring] at h; exact h
  have h := b_to_c 3440826 0 0; simp at h; exact h

private theorem t1_r5 : (⟨0, 0, 3440826, 0⟩ : Q) [fm]⊢^{21438995} ⟨0, 0, 10587160, 0⟩ := by
  rw [show (21438995 : ℕ) = 2 + (4234848 + (15 + (6616970 + 10587160))) from by ring]
  rw [show (3440826 : ℕ) = 10 + 13 * 264678 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (10 + 13 * 264678)
  apply stepNat_trans 4234848 _
  · have h := c_drain 264678 10 0; rw [show 5 * 264678 = 1323390 from by ring] at h; exact h
  apply stepNat_trans 15 _; · exact bnd_r10 1323390
  rw [show (1323390 + 4 : ℕ) = 0 + 1323394 from by ring, show (8 : ℕ) = 7 + 1 from by ring]
  apply stepNat_trans 6616970 10587160
  · have h := d_drain 1323394 7 0; rw [show 7 + 1 + 8 * 1323394 = 10587160 from by ring] at h; exact h
  have h := b_to_c 10587160 0 0; simp at h; exact h

private theorem t1_r6 : (⟨0, 0, 10587160, 0⟩ : Q) [fm]⊢^{65966153} ⟨0, 0, 32575880, 0⟩ := by
  rw [show (65966153 : ℕ) = 2 + (13030336 + (15 + (20359920 + 32575880))) from by ring]
  rw [show (10587160 : ℕ) = 10 + 13 * 814396 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (10 + 13 * 814396)
  apply stepNat_trans 13030336 _
  · have h := c_drain 814396 10 0; rw [show 5 * 814396 = 4071980 from by ring] at h; exact h
  apply stepNat_trans 15 _; · exact bnd_r10 4071980
  rw [show (4071980 + 4 : ℕ) = 0 + 4071984 from by ring, show (8 : ℕ) = 7 + 1 from by ring]
  apply stepNat_trans 20359920 32575880
  · have h := d_drain 4071984 7 0; rw [show 7 + 1 + 8 * 4071984 = 32575880 from by ring] at h; exact h
  have h := b_to_c 32575880 0 0; simp at h; exact h

private theorem t1_r7 : (⟨0, 0, 32575880, 0⟩ : Q) [fm]⊢^{202972793} ⟨0, 0, 100233480, 0⟩ := by
  rw [show (202972793 : ℕ) = 2 + (40093376 + (15 + (62645920 + 100233480))) from by ring]
  rw [show (32575880 : ℕ) = 10 + 13 * 2505836 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (10 + 13 * 2505836)
  apply stepNat_trans 40093376 _
  · have h := c_drain 2505836 10 0; rw [show 5 * 2505836 = 12529180 from by ring] at h; exact h
  apply stepNat_trans 15 _; · exact bnd_r10 12529180
  rw [show (12529180 + 4 : ℕ) = 0 + 12529184 from by ring, show (8 : ℕ) = 7 + 1 from by ring]
  apply stepNat_trans 62645920 100233480
  · have h := d_drain 12529184 7 0; rw [show 7 + 1 + 8 * 12529184 = 100233480 from by ring] at h; exact h
  have h := b_to_c 100233480 0 0; simp at h; exact h

private theorem t1_r8 : (⟨0, 0, 100233480, 0⟩ : Q) [fm]⊢^{624531686} ⟨0, 0, 308410711, 0⟩ := by
  rw [show (624531686 : ℕ) = 2 + (123364272 + (11 + (192756690 + 308410711))) from by ring]
  rw [show (100233480 : ℕ) = 7 + 13 * 7710267 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (7 + 13 * 7710267)
  apply stepNat_trans 123364272 _
  · have h := c_drain 7710267 7 0; rw [show 5 * 7710267 = 38551335 from by ring] at h; exact h
  apply stepNat_trans 11 _; · exact bnd_r7 38551335
  rw [show (38551335 + 3 : ℕ) = 0 + 38551338 from by ring, show (7 : ℕ) = 6 + 1 from by ring]
  apply stepNat_trans 192756690 308410711
  · have h := d_drain 38551338 6 0; rw [show 6 + 1 + 8 * 38551338 = 308410711 from by ring] at h; exact h
  have h := b_to_c 308410711 0 0; simp at h; exact h

private theorem t1_r9 : (⟨0, 0, 308410711, 0⟩ : Q) [fm]⊢^{1921635968} ⟨0, 0, 948956036, 0⟩ := by
  rw [show (1921635968 : ℕ) = 2 + (379582400 + (15 + (593097515 + 948956036))) from by ring]
  rw [show (308410711 : ℕ) = 9 + 13 * 23723900 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (9 + 13 * 23723900)
  apply stepNat_trans 379582400 _
  · have h := c_drain 23723900 9 0; rw [show 5 * 23723900 = 118619500 from by ring] at h; exact h
  apply stepNat_trans 15 _; · exact bnd_r9 118619500
  rw [show (118619500 + 3 : ℕ) = 0 + 118619503 from by ring, show (12 : ℕ) = 11 + 1 from by ring]
  apply stepNat_trans 593097515 948956036
  · have h := d_drain 118619503 11 0; rw [show 11 + 1 + 8 * 118619503 = 948956036 from by ring] at h; exact h
  have h := b_to_c 948956036 0 0; simp at h; exact h

private theorem t1_r10 : (⟨0, 0, 948956036, 0⟩ : Q) [fm]⊢^{1167945890} ⟨3, 0, 0, 364983090⟩ := by
  rw [show (1167945890 : ℕ) = 2 + 1167945888 from by ring]
  rw [show (948956036 : ℕ) = 0 + 13 * 72996618 + 2 from by ring]
  apply stepNat_trans 2 1167945888
  · exact r5r3 (0 + 13 * 72996618)
  have h := c_drain 72996618 0 0; rw [show 5 * 72996618 = 364983090 from by ring] at h; simp at h; exact h

private theorem t1 : (⟨1, 0, 0, 1559⟩ : Q) [fm]⊢^{4014796774} ⟨3, 0, 0, 364983090⟩ := by
  rw [show (4014796774 : ℕ) = 20271 + (77729 + (239180 + (735953 + (2264486 + (6967670 + (21438995 + (65966153 + (202972793 + (624531686 + (1921635968 + (1167945890))))))))))) from by ring]
  apply stepNat_trans 20271 _
  · exact t1_boot
  apply stepNat_trans 77729 _
  · exact t1_r0
  apply stepNat_trans 239180 _
  · exact t1_r1
  apply stepNat_trans 735953 _
  · exact t1_r2
  apply stepNat_trans 2264486 _
  · exact t1_r3
  apply stepNat_trans 6967670 _
  · exact t1_r4
  apply stepNat_trans 21438995 _
  · exact t1_r5
  apply stepNat_trans 65966153 _
  · exact t1_r6
  apply stepNat_trans 202972793 _
  · exact t1_r7
  apply stepNat_trans 624531686 _
  · exact t1_r8
  apply stepNat_trans 1921635968 _
  · exact t1_r9
  exact t1_r10

private theorem t2_boot : (⟨3, 0, 0, 364983090⟩ : Q) [fm]⊢^{4744780182} ⟨0, 0, 2919864729, 0⟩ := by
  rw [show (4744780182 : ℕ) = 3 + (1824915450 + 2919864729) from by ring]
  apply stepNat_trans 3 _
  · have h := r2_drain 3 0 0 364983090; simp at h; exact h
  rw [show (364983090 : ℕ) = 0 + 364983090 from by ring]
  apply stepNat_trans 1824915450 2919864729
  · have h := d_drain 364983090 8 0; rw [show 8 + 1 + 8 * 364983090 = 2919864729 from by ring] at h; exact h
  have h := b_to_c 2919864729 0 0; simp at h; exact h

private theorem t2_r0 : (⟨0, 0, 2919864729, 0⟩ : Q) [fm]⊢^{3593679666} ⟨3, 0, 0, 1123024895⟩ := by
  rw [show (3593679666 : ℕ) = 2 + 3593679664 from by ring]
  rw [show (2919864729 : ℕ) = 0 + 13 * 224604979 + 2 from by ring]
  apply stepNat_trans 2 3593679664
  · exact r5r3 (0 + 13 * 224604979)
  have h := c_drain 224604979 0 0; rw [show 5 * 224604979 = 1123024895 from by ring] at h; simp at h; exact h

private theorem t2 : (⟨3, 0, 0, 364983090⟩ : Q) [fm]⊢^{8338459848} ⟨3, 0, 0, 1123024895⟩ := by
  rw [show (8338459848 : ℕ) = 4744780182 + (3593679666) from by ring]
  apply stepNat_trans 4744780182 _
  · exact t2_boot
  exact t2_r0

private theorem t3_boot : (⟨3, 0, 0, 1123024895⟩ : Q) [fm]⊢^{14599323647} ⟨0, 0, 8984199169, 0⟩ := by
  rw [show (14599323647 : ℕ) = 3 + (5615124475 + 8984199169) from by ring]
  apply stepNat_trans 3 _
  · have h := r2_drain 3 0 0 1123024895; simp at h; exact h
  rw [show (1123024895 : ℕ) = 0 + 1123024895 from by ring]
  apply stepNat_trans 5615124475 8984199169
  · have h := d_drain 1123024895 8 0; rw [show 8 + 1 + 8 * 1123024895 = 8984199169 from by ring] at h; exact h
  have h := b_to_c 8984199169 0 0; simp at h; exact h

private theorem t3_r0 : (⟨0, 0, 8984199169, 0⟩ : Q) [fm]⊢^{11057475900} ⟨1, 0, 0, 3455461219⟩ := by
  rw [show (11057475900 : ℕ) = 2 + (11057475888 + 10) from by ring]
  rw [show (8984199169 : ℕ) = 8 + 13 * 691092243 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (8 + 13 * 691092243)
  apply stepNat_trans 11057475888 10
  · have h := c_drain 691092243 8 0; rw [show 5 * 691092243 = 3455461215 from by ring] at h; exact h
  exact bnd_r8 3455461215

private theorem t3 : (⟨3, 0, 0, 1123024895⟩ : Q) [fm]⊢^{25656799547} ⟨1, 0, 0, 3455461219⟩ := by
  rw [show (25656799547 : ℕ) = 14599323647 + (11057475900) from by ring]
  apply stepNat_trans 14599323647 _
  · exact t3_boot
  exact t3_r0

private theorem t4_boot : (⟨1, 0, 0, 3455461219⟩ : Q) [fm]⊢^{44920995851} ⟨0, 0, 27643689755, 0⟩ := by
  rw [show (44920995851 : ℕ) = 1 + (17277306095 + 27643689755) from by ring]
  apply stepNat_trans 1 _
  · have h := r2_drain 1 0 0 3455461219; simp at h; exact h
  rw [show (3455461219 : ℕ) = 0 + 3455461219 from by ring]
  apply stepNat_trans 17277306095 27643689755
  · have h := d_drain 3455461219 2 0; rw [show 2 + 1 + 8 * 3455461219 = 27643689755 from by ring] at h; exact h
  have h := b_to_c 27643689755 0 0; simp at h; exact h

private theorem t4_r0 : (⟨0, 0, 27643689755, 0⟩ : Q) [fm]⊢^{34023002775} ⟨2, 0, 0, 10632188367⟩ := by
  rw [show (34023002775 : ℕ) = 2 + (34023002768 + 5) from by ring]
  rw [show (27643689755 : ℕ) = 4 + 13 * 2126437673 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (4 + 13 * 2126437673)
  apply stepNat_trans 34023002768 5
  · have h := c_drain 2126437673 4 0; rw [show 5 * 2126437673 = 10632188365 from by ring] at h; exact h
  exact bnd_r4 10632188365

private theorem t4 : (⟨1, 0, 0, 3455461219⟩ : Q) [fm]⊢^{78943998626} ⟨2, 0, 0, 10632188367⟩ := by
  rw [show (78943998626 : ℕ) = 44920995851 + (34023002775) from by ring]
  apply stepNat_trans 44920995851 _
  · exact t4_boot
  exact t4_r0

private theorem t5_boot : (⟨2, 0, 0, 10632188367⟩ : Q) [fm]⊢^{138218448779} ⟨0, 0, 85057506942, 0⟩ := by
  rw [show (138218448779 : ℕ) = 2 + (53160941835 + 85057506942) from by ring]
  apply stepNat_trans 2 _
  · have h := r2_drain 2 0 0 10632188367; simp at h; exact h
  rw [show (10632188367 : ℕ) = 0 + 10632188367 from by ring]
  apply stepNat_trans 53160941835 85057506942
  · have h := d_drain 10632188367 5 0; rw [show 5 + 1 + 8 * 10632188367 = 85057506942 from by ring] at h; exact h
  have h := b_to_c 85057506942 0 0; simp at h; exact h

private theorem t5_r0 : (⟨0, 0, 85057506942, 0⟩ : Q) [fm]⊢^{529973697101} ⟨0, 0, 261715405978, 0⟩ := by
  rw [show (529973697101 : ℕ) = 2 + (104686162384 + (7 + (163572128730 + 261715405978))) from by ring]
  rw [show (85057506942 : ℕ) = 3 + 13 * 6542885149 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (3 + 13 * 6542885149)
  apply stepNat_trans 104686162384 _
  · have h := c_drain 6542885149 3 0; rw [show 5 * 6542885149 = 32714425745 from by ring] at h; exact h
  apply stepNat_trans 7 _; · exact bnd_r3 32714425745
  rw [show (32714425745 + 1 : ℕ) = 0 + 32714425746 from by ring, show (10 : ℕ) = 9 + 1 from by ring]
  apply stepNat_trans 163572128730 261715405978
  · have h := d_drain 32714425746 9 0; rw [show 9 + 1 + 8 * 32714425746 = 261715405978 from by ring] at h; exact h
  have h := b_to_c 261715405978 0 0; simp at h; exact h

private theorem t5_r1 : (⟨0, 0, 261715405978, 0⟩ : Q) [fm]⊢^{1630688298791} ⟨0, 0, 805278172244, 0⟩ := by
  rw [show (1630688298791 : ℕ) = 2 + (322111268880 + (15 + (503298857650 + 805278172244))) from by ring]
  rw [show (261715405978 : ℕ) = 11 + 13 * 20131954305 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (11 + 13 * 20131954305)
  apply stepNat_trans 322111268880 _
  · have h := c_drain 20131954305 11 0; rw [show 5 * 20131954305 = 100659771525 from by ring] at h; exact h
  apply stepNat_trans 15 _; · exact bnd_r11 100659771525
  rw [show (100659771525 + 5 : ℕ) = 0 + 100659771530 from by ring, show (4 : ℕ) = 3 + 1 from by ring]
  apply stepNat_trans 503298857650 805278172244
  · have h := d_drain 100659771530 3 0; rw [show 3 + 1 + 8 * 100659771530 = 805278172244 from by ring] at h; exact h
  have h := b_to_c 805278172244 0 0; simp at h; exact h

private theorem t5_r2 : (⟨0, 0, 805278172244, 0⟩ : Q) [fm]⊢^{5017502457833} ⟨0, 0, 2477778991524, 0⟩ := by
  rw [show (5017502457833 : ℕ) = 2 + (991111596592 + (15 + (1548611869700 + 2477778991524))) from by ring]
  rw [show (805278172244 : ℕ) = 11 + 13 * 61944474787 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (11 + 13 * 61944474787)
  apply stepNat_trans 991111596592 _
  · have h := c_drain 61944474787 11 0; rw [show 5 * 61944474787 = 309722373935 from by ring] at h; exact h
  apply stepNat_trans 15 _; · exact bnd_r11 309722373935
  rw [show (309722373935 + 5 : ℕ) = 0 + 309722373940 from by ring, show (4 : ℕ) = 3 + 1 from by ring]
  apply stepNat_trans 1548611869700 2477778991524
  · have h := d_drain 309722373940 3 0; rw [show 3 + 1 + 8 * 309722373940 = 2477778991524 from by ring] at h; exact h
  have h := b_to_c 2477778991524 0 0; simp at h; exact h

private theorem t5_r3 : (⟨0, 0, 2477778991524, 0⟩ : Q) [fm]⊢^{15438469101035} ⟨0, 0, 7623935358538, 0⟩ := by
  rw [show (15438469101035 : ℕ) = 2 + (3049574143408 + (7 + (4764959599080 + 7623935358538))) from by ring]
  rw [show (2477778991524 : ℕ) = 3 + 13 * 190598383963 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (3 + 13 * 190598383963)
  apply stepNat_trans 3049574143408 _
  · have h := c_drain 190598383963 3 0; rw [show 5 * 190598383963 = 952991919815 from by ring] at h; exact h
  apply stepNat_trans 7 _; · exact bnd_r3 952991919815
  rw [show (952991919815 + 1 : ℕ) = 0 + 952991919816 from by ring, show (10 : ℕ) = 9 + 1 from by ring]
  apply stepNat_trans 4764959599080 7623935358538
  · have h := d_drain 952991919816 9 0; rw [show 9 + 1 + 8 * 952991919816 = 7623935358538 from by ring] at h; exact h
  have h := b_to_c 7623935358538 0 0; simp at h; exact h

private theorem t5_r4 : (⟨0, 0, 7623935358538, 0⟩ : Q) [fm]⊢^{47502981849353} ⟨0, 0, 23458262641658, 0⟩ := by
  rw [show (47502981849353 : ℕ) = 2 + (9383305056656 + (7 + (14661414151030 + 23458262641658))) from by ring]
  rw [show (7623935358538 : ℕ) = 3 + 13 * 586456566041 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (3 + 13 * 586456566041)
  apply stepNat_trans 9383305056656 _
  · have h := c_drain 586456566041 3 0; rw [show 5 * 586456566041 = 2932282830205 from by ring] at h; exact h
  apply stepNat_trans 7 _; · exact bnd_r3 2932282830205
  rw [show (2932282830205 + 1 : ℕ) = 0 + 2932282830206 from by ring, show (10 : ℕ) = 9 + 1 from by ring]
  apply stepNat_trans 14661414151030 23458262641658
  · have h := d_drain 2932282830206 9 0; rw [show 9 + 1 + 8 * 2932282830206 = 23458262641658 from by ring] at h; exact h
  have h := b_to_c 23458262641658 0 0; simp at h; exact h

private theorem t5_r5 : (⟨0, 0, 23458262641658, 0⟩ : Q) [fm]⊢^{146163021074951} ⟨0, 0, 72179269666644, 0⟩ := by
  rw [show (146163021074951 : ℕ) = 2 + (28871707866640 + (15 + (45112043541650 + 72179269666644))) from by ring]
  rw [show (23458262641658 : ℕ) = 11 + 13 * 1804481741665 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (11 + 13 * 1804481741665)
  apply stepNat_trans 28871707866640 _
  · have h := c_drain 1804481741665 11 0; rw [show 5 * 1804481741665 = 9022408708325 from by ring] at h; exact h
  apply stepNat_trans 15 _; · exact bnd_r11 9022408708325
  rw [show (9022408708325 + 5 : ℕ) = 0 + 9022408708330 from by ring, show (4 : ℕ) = 3 + 1 from by ring]
  apply stepNat_trans 45112043541650 72179269666644
  · have h := d_drain 9022408708330 3 0; rw [show 3 + 1 + 8 * 9022408708330 = 72179269666644 from by ring] at h; exact h
  have h := b_to_c 72179269666644 0 0; simp at h; exact h

private theorem t5_r6 : (⟨0, 0, 72179269666644, 0⟩ : Q) [fm]⊢^{88836024205100} ⟨1, 0, 0, 27761257564094⟩ := by
  rw [show (88836024205100 : ℕ) = 2 + (88836024205088 + 10) from by ring]
  rw [show (72179269666644 : ℕ) = 8 + 13 * 5552251512818 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (8 + 13 * 5552251512818)
  apply stepNat_trans 88836024205088 10
  · have h := c_drain 5552251512818 8 0; rw [show 5 * 5552251512818 = 27761257564090 from by ring] at h; exact h
  exact bnd_r8 27761257564090

private theorem t5 : (⟨2, 0, 0, 10632188367⟩ : Q) [fm]⊢^{305256879132943} ⟨1, 0, 0, 27761257564094⟩ := by
  rw [show (305256879132943 : ℕ) = 138218448779 + (529973697101 + (1630688298791 + (5017502457833 + (15438469101035 + (47502981849353 + (146163021074951 + (88836024205100))))))) from by ring]
  apply stepNat_trans 138218448779 _
  · exact t5_boot
  apply stepNat_trans 529973697101 _
  · exact t5_r0
  apply stepNat_trans 1630688298791 _
  · exact t5_r1
  apply stepNat_trans 5017502457833 _
  · exact t5_r2
  apply stepNat_trans 15438469101035 _
  · exact t5_r3
  apply stepNat_trans 47502981849353 _
  · exact t5_r4
  apply stepNat_trans 146163021074951 _
  · exact t5_r5
  exact t5_r6

private theorem t6_boot : (⟨1, 0, 0, 27761257564094⟩ : Q) [fm]⊢^{360896348333226} ⟨0, 0, 222090060512755, 0⟩ := by
  rw [show (360896348333226 : ℕ) = 1 + (138806287820470 + 222090060512755) from by ring]
  apply stepNat_trans 1 _
  · have h := r2_drain 1 0 0 27761257564094; simp at h; exact h
  rw [show (27761257564094 : ℕ) = 0 + 27761257564094 from by ring]
  apply stepNat_trans 138806287820470 222090060512755
  · have h := d_drain 27761257564094 2 0; rw [show 2 + 1 + 8 * 27761257564094 = 222090060512755 from by ring] at h; exact h
  have h := b_to_c 222090060512755 0 0; simp at h; exact h

private theorem t6_r0 : (⟨0, 0, 222090060512755, 0⟩ : Q) [fm]⊢^{273341612938775} ⟨2, 0, 0, 85419254043367⟩ := by
  rw [show (273341612938775 : ℕ) = 2 + (273341612938768 + 5) from by ring]
  rw [show (222090060512755 : ℕ) = 4 + 13 * 17083850808673 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (4 + 13 * 17083850808673)
  apply stepNat_trans 273341612938768 5
  · have h := c_drain 17083850808673 4 0; rw [show 5 * 17083850808673 = 85419254043365 from by ring] at h; exact h
  exact bnd_r4 85419254043365

private theorem t6 : (⟨1, 0, 0, 27761257564094⟩ : Q) [fm]⊢^{634237961272001} ⟨2, 0, 0, 85419254043367⟩ := by
  rw [show (634237961272001 : ℕ) = 360896348333226 + (273341612938775) from by ring]
  apply stepNat_trans 360896348333226 _
  · exact t6_boot
  exact t6_r0

private theorem t7_boot : (⟨2, 0, 0, 85419254043367⟩ : Q) [fm]⊢^{1110450302563779} ⟨0, 0, 683354032346942, 0⟩ := by
  rw [show (1110450302563779 : ℕ) = 2 + (427096270216835 + 683354032346942) from by ring]
  apply stepNat_trans 2 _
  · have h := r2_drain 2 0 0 85419254043367; simp at h; exact h
  rw [show (85419254043367 : ℕ) = 0 + 85419254043367 from by ring]
  apply stepNat_trans 427096270216835 683354032346942
  · have h := d_drain 85419254043367 5 0; rw [show 5 + 1 + 8 * 85419254043367 = 683354032346942 from by ring] at h; exact h
  have h := b_to_c 683354032346942 0 0; simp at h; exact h

private theorem t7_r0 : (⟨0, 0, 683354032346942, 0⟩ : Q) [fm]⊢^{4257821278469408} ⟨0, 0, 2102627791836747, 0⟩ := by
  rw [show (4257821278469408 : ℕ) = 2 + (841051116734688 + (11 + (1314142369897960 + 2102627791836747))) from by ring]
  rw [show (683354032346942 : ℕ) = 6 + 13 * 52565694795918 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (6 + 13 * 52565694795918)
  apply stepNat_trans 841051116734688 _
  · have h := c_drain 52565694795918 6 0; rw [show 5 * 52565694795918 = 262828473979590 from by ring] at h; exact h
  apply stepNat_trans 11 _; · exact bnd_r6 262828473979590
  rw [show (262828473979590 + 2 : ℕ) = 0 + 262828473979592 from by ring, show (11 : ℕ) = 10 + 1 from by ring]
  apply stepNat_trans 1314142369897960 2102627791836747
  · have h := d_drain 262828473979592 10 0; rw [show 10 + 1 + 8 * 262828473979592 = 2102627791836747 from by ring] at h; exact h
  have h := b_to_c 2102627791836747 0 0; simp at h; exact h

private theorem t7_r1 : (⟨0, 0, 2102627791836747, 0⟩ : Q) [fm]⊢^{2587849589952919} ⟨2, 0, 0, 808702996860287⟩ := by
  rw [show (2587849589952919 : ℕ) = 2 + (2587849589952912 + 5) from by ring]
  rw [show (2102627791836747 : ℕ) = 4 + 13 * 161740599372057 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (4 + 13 * 161740599372057)
  apply stepNat_trans 2587849589952912 5
  · have h := c_drain 161740599372057 4 0; rw [show 5 * 161740599372057 = 808702996860285 from by ring] at h; exact h
  exact bnd_r4 808702996860285

private theorem t7 : (⟨2, 0, 0, 85419254043367⟩ : Q) [fm]⊢^{7956121170986106} ⟨2, 0, 0, 808702996860287⟩ := by
  rw [show (7956121170986106 : ℕ) = 1110450302563779 + (4257821278469408 + (2587849589952919)) from by ring]
  apply stepNat_trans 1110450302563779 _
  · exact t7_boot
  apply stepNat_trans 4257821278469408 _
  · exact t7_r0
  exact t7_r1

private theorem t8_boot : (⟨2, 0, 0, 808702996860287⟩ : Q) [fm]⊢^{10513138959183739} ⟨0, 0, 6469623974882302, 0⟩ := by
  rw [show (10513138959183739 : ℕ) = 2 + (4043514984301435 + 6469623974882302) from by ring]
  apply stepNat_trans 2 _
  · have h := r2_drain 2 0 0 808702996860287; simp at h; exact h
  rw [show (808702996860287 : ℕ) = 0 + 808702996860287 from by ring]
  apply stepNat_trans 4043514984301435 6469623974882302
  · have h := d_drain 808702996860287 5 0; rw [show 5 + 1 + 8 * 808702996860287 = 6469623974882302 from by ring] at h; exact h
  have h := b_to_c 6469623974882302 0 0; simp at h; exact h

private theorem t8_r0 : (⟨0, 0, 6469623974882302, 0⟩ : Q) [fm]⊢^{40310733997343579} ⟨0, 0, 19906535307330164, 0⟩ := by
  rw [show (40310733997343579 : ℕ) = 2 + (7962614122932048 + (15 + (12441584567081350 + 19906535307330164))) from by ring]
  rw [show (6469623974882302 : ℕ) = 11 + 13 * 497663382683253 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (11 + 13 * 497663382683253)
  apply stepNat_trans 7962614122932048 _
  · have h := c_drain 497663382683253 11 0; rw [show 5 * 497663382683253 = 2488316913416265 from by ring] at h; exact h
  apply stepNat_trans 15 _; · exact bnd_r11 2488316913416265
  rw [show (2488316913416265 + 5 : ℕ) = 0 + 2488316913416270 from by ring, show (4 : ℕ) = 3 + 1 from by ring]
  apply stepNat_trans 12441584567081350 19906535307330164
  · have h := d_drain 2488316913416270 3 0; rw [show 3 + 1 + 8 * 2488316913416270 = 19906535307330164 from by ring] at h; exact h
  have h := b_to_c 19906535307330164 0 0; simp at h; exact h

private theorem t8_r1 : (⟨0, 0, 19906535307330164, 0⟩ : Q) [fm]⊢^{124033027684134101} ⟨0, 0, 61250877868708200, 0⟩ := by
  rw [show (124033027684134101 : ℕ) = 2 + (24500351147483264 + (15 + (38281798667942620 + 61250877868708200))) from by ring]
  rw [show (19906535307330164 : ℕ) = 10 + 13 * 1531271946717704 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (10 + 13 * 1531271946717704)
  apply stepNat_trans 24500351147483264 _
  · have h := c_drain 1531271946717704 10 0; rw [show 5 * 1531271946717704 = 7656359733588520 from by ring] at h; exact h
  apply stepNat_trans 15 _; · exact bnd_r10 7656359733588520
  rw [show (7656359733588520 + 4 : ℕ) = 0 + 7656359733588524 from by ring, show (8 : ℕ) = 7 + 1 from by ring]
  apply stepNat_trans 38281798667942620 61250877868708200
  · have h := d_drain 7656359733588524 7 0; rw [show 7 + 1 + 8 * 7656359733588524 = 61250877868708200 from by ring] at h; exact h
  have h := b_to_c 61250877868708200 0 0; simp at h; exact h

private theorem t8_r2 : (⟨0, 0, 61250877868708200, 0⟩ : Q) [fm]⊢^{75385695838410092} ⟨1, 0, 0, 23558029949503154⟩ := by
  rw [show (75385695838410092 : ℕ) = 2 + (75385695838410080 + 10) from by ring]
  rw [show (61250877868708200 : ℕ) = 8 + 13 * 4711605989900630 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (8 + 13 * 4711605989900630)
  apply stepNat_trans 75385695838410080 10
  · have h := c_drain 4711605989900630 8 0; rw [show 5 * 4711605989900630 = 23558029949503150 from by ring] at h; exact h
  exact bnd_r8 23558029949503150

private theorem t8 : (⟨2, 0, 0, 808702996860287⟩ : Q) [fm]⊢^{250242596479071511} ⟨1, 0, 0, 23558029949503154⟩ := by
  rw [show (250242596479071511 : ℕ) = 10513138959183739 + (40310733997343579 + (124033027684134101 + (75385695838410092))) from by ring]
  apply stepNat_trans 10513138959183739 _
  · exact t8_boot
  apply stepNat_trans 40310733997343579 _
  · exact t8_r0
  apply stepNat_trans 124033027684134101 _
  · exact t8_r1
  exact t8_r2

private theorem t9_boot : (⟨1, 0, 0, 23558029949503154⟩ : Q) [fm]⊢^{306254389343541006} ⟨0, 0, 188464239596025235, 0⟩ := by
  rw [show (306254389343541006 : ℕ) = 1 + (117790149747515770 + 188464239596025235) from by ring]
  apply stepNat_trans 1 _
  · have h := r2_drain 1 0 0 23558029949503154; simp at h; exact h
  rw [show (23558029949503154 : ℕ) = 0 + 23558029949503154 from by ring]
  apply stepNat_trans 117790149747515770 188464239596025235
  · have h := d_drain 23558029949503154 2 0; rw [show 2 + 1 + 8 * 23558029949503154 = 188464239596025235 from by ring] at h; exact h
  have h := b_to_c 188464239596025235 0 0; simp at h; exact h

private theorem t9_r0 : (⟨0, 0, 188464239596025235, 0⟩ : Q) [fm]⊢^{1174277185175234156} ⟨0, 0, 579889967987769956, 0⟩ := by
  rw [show (1174277185175234156 : ℕ) = 2 + (231955987195107968 + (15 + (362431229992356215 + 579889967987769956))) from by ring]
  rw [show (188464239596025235 : ℕ) = 9 + 13 * 14497249199694248 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (9 + 13 * 14497249199694248)
  apply stepNat_trans 231955987195107968 _
  · have h := c_drain 14497249199694248 9 0; rw [show 5 * 14497249199694248 = 72486245998471240 from by ring] at h; exact h
  apply stepNat_trans 15 _; · exact bnd_r9 72486245998471240
  rw [show (72486245998471240 + 3 : ℕ) = 0 + 72486245998471243 from by ring, show (12 : ℕ) = 11 + 1 from by ring]
  apply stepNat_trans 362431229992356215 579889967987769956
  · have h := d_drain 72486245998471243 11 0; rw [show 11 + 1 + 8 * 72486245998471243 = 579889967987769956 from by ring] at h; exact h
  have h := b_to_c 579889967987769956 0 0; simp at h; exact h

private theorem t9_r1 : (⟨0, 0, 579889967987769956, 0⟩ : Q) [fm]⊢^{713710729831101484} ⟨1, 0, 0, 223034603072219214⟩ := by
  rw [show (713710729831101484 : ℕ) = 2 + (713710729831101472 + 10) from by ring]
  rw [show (579889967987769956 : ℕ) = 8 + 13 * 44606920614443842 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (8 + 13 * 44606920614443842)
  apply stepNat_trans 713710729831101472 10
  · have h := c_drain 44606920614443842 8 0; rw [show 5 * 44606920614443842 = 223034603072219210 from by ring] at h; exact h
  exact bnd_r8 223034603072219210

private theorem t9 : (⟨1, 0, 0, 23558029949503154⟩ : Q) [fm]⊢^{2194242304349876646} ⟨1, 0, 0, 223034603072219214⟩ := by
  rw [show (2194242304349876646 : ℕ) = 306254389343541006 + (1174277185175234156 + (713710729831101484)) from by ring]
  apply stepNat_trans 306254389343541006 _
  · exact t9_boot
  apply stepNat_trans 1174277185175234156 _
  · exact t9_r0
  exact t9_r1

private theorem t10_boot : (⟨1, 0, 0, 223034603072219214⟩ : Q) [fm]⊢^{2899449839938849786} ⟨0, 0, 1784276824577753715, 0⟩ := by
  rw [show (2899449839938849786 : ℕ) = 1 + (1115173015361096070 + 1784276824577753715) from by ring]
  apply stepNat_trans 1 _
  · have h := r2_drain 1 0 0 223034603072219214; simp at h; exact h
  rw [show (223034603072219214 : ℕ) = 0 + 223034603072219214 from by ring]
  apply stepNat_trans 1115173015361096070 1784276824577753715
  · have h := d_drain 223034603072219214 2 0; rw [show 2 + 1 + 8 * 223034603072219214 = 1784276824577753715 from by ring] at h; exact h
  have h := b_to_c 1784276824577753715 0 0; simp at h; exact h

private theorem t10_r0 : (⟨0, 0, 1784276824577753715, 0⟩ : Q) [fm]⊢^{2196033014864927649} ⟨0, 0, 0, 686260317145289891⟩ := by
  rw [show (2196033014864927649 : ℕ) = 2 + (2196033014864927632 + 15) from by ring]
  rw [show (1784276824577753715 : ℕ) = 12 + 13 * 137252063429057977 + 2 from by ring]
  apply stepNat_trans 2 _; · exact r5r3 (12 + 13 * 137252063429057977)
  apply stepNat_trans 2196033014864927632 15
  · have h := c_drain 137252063429057977 12 0; rw [show 5 * 137252063429057977 = 686260317145289885 from by ring] at h; exact h
  exact bnd_r12 686260317145289885

private theorem t10 : (⟨1, 0, 0, 223034603072219214⟩ : Q) [fm]⊢^{5095482854803777435} ⟨0, 0, 0, 686260317145289891⟩ := by
  rw [show (5095482854803777435 : ℕ) = 2899449839938849786 + (2196033014864927649) from by ring]
  apply stepNat_trans 2899449839938849786 _
  · exact t10_boot
  exact t10_r0


theorem fm_haltsIn : haltsIn fm c₀ 7548863488598188537 := by
  apply stepNat_haltsIn_add (m := 17100) (c₂ := ⟨1, 0, 0, 1559⟩)
  · exact t0
  apply stepNat_haltsIn_add (m := 4014796774) (c₂ := ⟨3, 0, 0, 364983090⟩)
  · exact t1
  apply stepNat_haltsIn_add (m := 8338459848) (c₂ := ⟨3, 0, 0, 1123024895⟩)
  · exact t2
  apply stepNat_haltsIn_add (m := 25656799547) (c₂ := ⟨1, 0, 0, 3455461219⟩)
  · exact t3
  apply stepNat_haltsIn_add (m := 78943998626) (c₂ := ⟨2, 0, 0, 10632188367⟩)
  · exact t4
  apply stepNat_haltsIn_add (m := 305256879132943) (c₂ := ⟨1, 0, 0, 27761257564094⟩)
  · exact t5
  apply stepNat_haltsIn_add (m := 634237961272001) (c₂ := ⟨2, 0, 0, 85419254043367⟩)
  · exact t6
  apply stepNat_haltsIn_add (m := 7956121170986106) (c₂ := ⟨2, 0, 0, 808702996860287⟩)
  · exact t7
  apply stepNat_haltsIn_add (m := 250242596479071511) (c₂ := ⟨1, 0, 0, 23558029949503154⟩)
  · exact t8
  apply stepNat_haltsIn_add (m := 2194242304349876646) (c₂ := ⟨1, 0, 0, 223034603072219214⟩)
  · exact t9
  refine ⟨⟨0, 0, 0, 686260317145289891⟩, ?_, rfl⟩
  exact t10

end Sz22_halted_692_7
