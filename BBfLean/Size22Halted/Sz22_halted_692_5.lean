import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_halted_692 #5: [1/18, 4/15, 21/2, 11/3, 5/7, 2/11]

Vector representation:
```
-1 -2  0  0  0
 2 -1 -1  0  0
-1  1  0  1  0
 0 -1  0  0  1
 0  0  1 -1  0
 1  0  0  0 -1
```

This Fractran program halts in 114613926700260640237968442298168949531348819453104518623702293 steps.

Author: Claude
-/

namespace Sz22_halted_692_5

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

private theorem r5_sn : ∀ k c d e, (⟨0, 0, c, d + k, e⟩ : Q) [fm]⊢^{k} ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; rfl
  rw [show d + (k + 1) = (d + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨0, 0, c, (d + k) + 1, e⟩ = some ⟨0, 0, c + 1, d + k, e⟩; rfl
  have h := ih (c + 1) d e; rw [show (c + 1) + k = c + (1 + k) from by ring] at h; exact h

private theorem r3r1_sn : ∀ k, ∀ a c d e, (⟨a + 1, 0, c + k, d, e⟩ : Q) [fm]⊢^{2 * k} ⟨a + k + 1, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · simp; rfl
  rw [show c + (k + 1) = (c + k) + 1 from by ring, show 2 * (k + 1) = 1 + (1 + 2 * k) from by ring]
  apply stepNat_trans 1 (1 + 2 * k)
  · show fm ⟨a + 1, 0, (c + k) + 1, d, e⟩ = some ⟨a, 1, (c + k) + 1, d + 1, e⟩; rfl
  apply stepNat_trans 1 (2 * k)
  · show fm ⟨a, 1, (c + k) + 1, d + 1, e⟩ = some ⟨a + 2, 0, c + k, d + 1, e⟩; simp [fm]
  have h := ih (a + 1) c (d + 1) e
  rw [show (a + 1) + k + 1 = a + (k + 1) + 1 from by ring,
    show (d + 1) + k = d + (k + 1) from by ring] at h
  rw [show a + 2 = (a + 1) + 1 from by ring]; exact h

private theorem drain_sn : ∀ k, ∀ a d e, (⟨a + 3 * k, 0, 0, d, e⟩ : Q) [fm]⊢^{3 * k} ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · simp; rfl
  rw [show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring, show 3 * (k + 1) = 3 + 3 * k from by ring]
  apply stepNat_trans 3 (3 * k)
  · show stepNat fm 3 ⟨(a + 3 * k) + 3, 0, 0, d, e⟩ = some ⟨a + 3 * k, 0, 0, d + 2, e⟩; rfl
  have h := ih a (d + 2) e; rw [show (d + 2) + 2 * k = d + 2 * (k + 1) from by ring] at h; exact h

private theorem tail1_sn : ∀ d e, (⟨1, 0, 0, d, e⟩ : Q) [fm]⊢^{2} ⟨0, 0, 0, d + 1, e + 1⟩ := by
  intro d e; rfl

private theorem tail2_sn : ∀ d e, (⟨2, 0, 0, d, e⟩ : Q) [fm]⊢^{4} ⟨0, 0, 0, d + 2, e + 2⟩ := by
  intro d e; rfl

private theorem mod0_sn : ∀ k E, (⟨0, 0, 0, 3 * k, E + 1⟩ : Q) [fm]⊢^{12 * k + 3} ⟨0, 0, 0, 5 * k + 1, E + 1⟩ := by
  intro k E
  have h1 := r5_sn (3 * k) 0 0 (E + 1)
  simp only [Nat.zero_add] at h1
  have h2 : (⟨0, 0, 3 * k, 0, E + 1⟩ : Q) [fm]⊢^{1} ⟨1, 0, 3 * k, 0, E⟩ := rfl
  have h3 := r3r1_sn (3 * k) 0 0 0 E
  simp only [Nat.zero_add] at h3
  rw [show 3 * k + 1 = 1 + 3 * k from by ring] at h3
  have h4 := drain_sn k 1 (3 * k) E
  rw [show 3 * k + 2 * k = 5 * k from by ring] at h4
  have h5 := tail1_sn (5 * k) E
  have h12 := stepNat_trans (3 * k) 1 h1 h2
  have h123 := stepNat_trans (3 * k + 1) (2 * (3 * k)) h12 h3
  have h1234 := stepNat_trans (3 * k + 1 + 2 * (3 * k)) (3 * k) h123 h4
  have h12345 := stepNat_trans (3 * k + 1 + 2 * (3 * k) + 3 * k) 2 h1234 h5
  rw [show 3 * k + 1 + 2 * (3 * k) + 3 * k + 2 = 12 * k + 3 from by ring] at h12345
  exact h12345

private theorem mod1_sn : ∀ k E, (⟨0, 0, 0, 3 * k + 1, E + 1⟩ : Q) [fm]⊢^{12 * k + 8} ⟨0, 0, 0, 5 * k + 3, E + 2⟩ := by
  intro k E
  have h1 := r5_sn (3 * k + 1) 0 0 (E + 1)
  simp only [Nat.zero_add] at h1
  have h2 : (⟨0, 0, 3 * k + 1, 0, E + 1⟩ : Q) [fm]⊢^{1} ⟨1, 0, 3 * k + 1, 0, E⟩ := rfl
  have h3 := r3r1_sn (3 * k + 1) 0 0 0 E
  simp only [Nat.zero_add] at h3
  rw [show 3 * k + 1 + 1 = 2 + 3 * k from by ring] at h3
  have h4 := drain_sn k 2 (3 * k + 1) E
  rw [show 3 * k + 1 + 2 * k = 5 * k + 1 from by ring] at h4
  have h5 := tail2_sn (5 * k + 1) E
  rw [show 5 * k + 1 + 2 = 5 * k + 3 from by ring] at h5
  have h12 := stepNat_trans (3 * k + 1) 1 h1 h2
  have h123 := stepNat_trans (3 * k + 1 + 1) (2 * (3 * k + 1)) h12 h3
  have h1234 := stepNat_trans (3 * k + 1 + 1 + 2 * (3 * k + 1)) (3 * k) h123 h4
  have h12345 := stepNat_trans (3 * k + 1 + 1 + 2 * (3 * k + 1) + 3 * k) 4 h1234 h5
  rw [show 3 * k + 1 + 1 + 2 * (3 * k + 1) + 3 * k + 4 = 12 * k + 8 from by ring] at h12345
  exact h12345

private theorem mod2_sn : ∀ k E, (⟨0, 0, 0, 3 * k + 2, E + 1⟩ : Q) [fm]⊢^{12 * k + 10} ⟨0, 0, 0, 5 * k + 4, E⟩ := by
  intro k E
  have h1 := r5_sn (3 * k + 2) 0 0 (E + 1)
  simp only [Nat.zero_add] at h1
  have h2 : (⟨0, 0, 3 * k + 2, 0, E + 1⟩ : Q) [fm]⊢^{1} ⟨1, 0, 3 * k + 2, 0, E⟩ := rfl
  have h3 := r3r1_sn (3 * k + 2) 0 0 0 E
  simp only [Nat.zero_add] at h3
  rw [show 3 * k + 2 + 1 = 3 * (k + 1) from by ring] at h3
  have h4 := drain_sn (k + 1) 0 (3 * k + 2) E
  simp only [Nat.zero_add] at h4
  rw [show 3 * k + 2 + 2 * (k + 1) = 5 * k + 4 from by ring] at h4
  have h12 := stepNat_trans (3 * k + 2) 1 h1 h2
  have h123 := stepNat_trans (3 * k + 2 + 1) (2 * (3 * k + 2)) h12 h3
  have h1234 := stepNat_trans (3 * k + 2 + 1 + 2 * (3 * k + 2)) (3 * (k + 1)) h123 h4
  rw [show 3 * k + 2 + 1 + 2 * (3 * k + 2) + 3 * (k + 1) = 12 * k + 10 from by ring] at h1234
  exact h1234

private theorem halt_sn : ∀ D, haltsIn fm (⟨0, 0, 0, D, 0⟩ : Q) D := by
  intro D; refine ⟨⟨0, 0, D, 0, 0⟩, ?_, rfl⟩
  have h := r5_sn D 0 0 0
  simp only [Nat.zero_add] at h; exact h

theorem fm_haltsIn : haltsIn fm c₀ 114613926700260640237968442298168949531348819453104518623702293 := by
  apply stepNat_haltsIn_add (m := 10) (c₂ := ⟨0, 0, 0, 3, 2⟩)
  · show stepNat fm 10 c₀ = some ⟨0, 0, 0, 3, 2⟩; rfl
  apply stepNat_haltsIn_add (m := 15) (c₂ := ⟨0, 0, 0, 6, 2⟩)
  · have h := mod0_sn 1 1
    rw [show 3 * 1 = 3 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 1 + 1 = 6 from by ring, show 12 * 1 + 3 = 15 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 27) (c₂ := ⟨0, 0, 0, 11, 2⟩)
  · have h := mod0_sn 2 1
    rw [show 3 * 2 = 6 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 2 + 1 = 11 from by ring, show 12 * 2 + 3 = 27 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 46) (c₂ := ⟨0, 0, 0, 19, 1⟩)
  · have h := mod2_sn 3 1
    rw [show 3 * 3 + 2 = 11 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 3 + 4 = 19 from by ring, show 12 * 3 + 10 = 46 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 80) (c₂ := ⟨0, 0, 0, 33, 2⟩)
  · have h := mod1_sn 6 0
    rw [show 3 * 6 + 1 = 19 from by ring, show 0 + 1 = 1 from by ring,
      show 5 * 6 + 3 = 33 from by ring, show 0 + 2 = 2 from by ring,
      show 12 * 6 + 8 = 80 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 135) (c₂ := ⟨0, 0, 0, 56, 2⟩)
  · have h := mod0_sn 11 1
    rw [show 3 * 11 = 33 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 11 + 1 = 56 from by ring, show 12 * 11 + 3 = 135 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 226) (c₂ := ⟨0, 0, 0, 94, 1⟩)
  · have h := mod2_sn 18 1
    rw [show 3 * 18 + 2 = 56 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 18 + 4 = 94 from by ring, show 12 * 18 + 10 = 226 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 380) (c₂ := ⟨0, 0, 0, 158, 2⟩)
  · have h := mod1_sn 31 0
    rw [show 3 * 31 + 1 = 94 from by ring, show 0 + 1 = 1 from by ring,
      show 5 * 31 + 3 = 158 from by ring, show 0 + 2 = 2 from by ring,
      show 12 * 31 + 8 = 380 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 634) (c₂ := ⟨0, 0, 0, 264, 1⟩)
  · have h := mod2_sn 52 1
    rw [show 3 * 52 + 2 = 158 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 52 + 4 = 264 from by ring, show 12 * 52 + 10 = 634 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1059) (c₂ := ⟨0, 0, 0, 441, 1⟩)
  · have h := mod0_sn 88 0
    rw [show 3 * 88 = 264 from by ring, show 0 + 1 = 1 from by ring,
      show 5 * 88 + 1 = 441 from by ring, show 12 * 88 + 3 = 1059 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1767) (c₂ := ⟨0, 0, 0, 736, 1⟩)
  · have h := mod0_sn 147 0
    rw [show 3 * 147 = 441 from by ring, show 0 + 1 = 1 from by ring,
      show 5 * 147 + 1 = 736 from by ring, show 12 * 147 + 3 = 1767 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2948) (c₂ := ⟨0, 0, 0, 1228, 2⟩)
  · have h := mod1_sn 245 0
    rw [show 3 * 245 + 1 = 736 from by ring, show 0 + 1 = 1 from by ring,
      show 5 * 245 + 3 = 1228 from by ring, show 0 + 2 = 2 from by ring,
      show 12 * 245 + 8 = 2948 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 4916) (c₂ := ⟨0, 0, 0, 2048, 3⟩)
  · have h := mod1_sn 409 1
    rw [show 3 * 409 + 1 = 1228 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 409 + 3 = 2048 from by ring, show 1 + 2 = 3 from by ring,
      show 12 * 409 + 8 = 4916 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 8194) (c₂ := ⟨0, 0, 0, 3414, 2⟩)
  · have h := mod2_sn 682 2
    rw [show 3 * 682 + 2 = 2048 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 682 + 4 = 3414 from by ring, show 12 * 682 + 10 = 8194 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 13659) (c₂ := ⟨0, 0, 0, 5691, 2⟩)
  · have h := mod0_sn 1138 1
    rw [show 3 * 1138 = 3414 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 1138 + 1 = 5691 from by ring, show 12 * 1138 + 3 = 13659 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 22767) (c₂ := ⟨0, 0, 0, 9486, 2⟩)
  · have h := mod0_sn 1897 1
    rw [show 3 * 1897 = 5691 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 1897 + 1 = 9486 from by ring, show 12 * 1897 + 3 = 22767 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 37947) (c₂ := ⟨0, 0, 0, 15811, 2⟩)
  · have h := mod0_sn 3162 1
    rw [show 3 * 3162 = 9486 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 3162 + 1 = 15811 from by ring, show 12 * 3162 + 3 = 37947 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 63248) (c₂ := ⟨0, 0, 0, 26353, 3⟩)
  · have h := mod1_sn 5270 1
    rw [show 3 * 5270 + 1 = 15811 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 5270 + 3 = 26353 from by ring, show 1 + 2 = 3 from by ring,
      show 12 * 5270 + 8 = 63248 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 105416) (c₂ := ⟨0, 0, 0, 43923, 4⟩)
  · have h := mod1_sn 8784 2
    rw [show 3 * 8784 + 1 = 26353 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 8784 + 3 = 43923 from by ring, show 2 + 2 = 4 from by ring,
      show 12 * 8784 + 8 = 105416 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 175695) (c₂ := ⟨0, 0, 0, 73206, 4⟩)
  · have h := mod0_sn 14641 3
    rw [show 3 * 14641 = 43923 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 14641 + 1 = 73206 from by ring, show 12 * 14641 + 3 = 175695 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 292827) (c₂ := ⟨0, 0, 0, 122011, 4⟩)
  · have h := mod0_sn 24402 3
    rw [show 3 * 24402 = 73206 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 24402 + 1 = 122011 from by ring, show 12 * 24402 + 3 = 292827 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 488048) (c₂ := ⟨0, 0, 0, 203353, 5⟩)
  · have h := mod1_sn 40670 3
    rw [show 3 * 40670 + 1 = 122011 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 40670 + 3 = 203353 from by ring, show 3 + 2 = 5 from by ring,
      show 12 * 40670 + 8 = 488048 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 813416) (c₂ := ⟨0, 0, 0, 338923, 6⟩)
  · have h := mod1_sn 67784 4
    rw [show 3 * 67784 + 1 = 203353 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 67784 + 3 = 338923 from by ring, show 4 + 2 = 6 from by ring,
      show 12 * 67784 + 8 = 813416 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1355696) (c₂ := ⟨0, 0, 0, 564873, 7⟩)
  · have h := mod1_sn 112974 5
    rw [show 3 * 112974 + 1 = 338923 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 112974 + 3 = 564873 from by ring, show 5 + 2 = 7 from by ring,
      show 12 * 112974 + 8 = 1355696 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2259495) (c₂ := ⟨0, 0, 0, 941456, 7⟩)
  · have h := mod0_sn 188291 6
    rw [show 3 * 188291 = 564873 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 188291 + 1 = 941456 from by ring, show 12 * 188291 + 3 = 2259495 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 3765826) (c₂ := ⟨0, 0, 0, 1569094, 6⟩)
  · have h := mod2_sn 313818 6
    rw [show 3 * 313818 + 2 = 941456 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 313818 + 4 = 1569094 from by ring, show 12 * 313818 + 10 = 3765826 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 6276380) (c₂ := ⟨0, 0, 0, 2615158, 7⟩)
  · have h := mod1_sn 523031 5
    rw [show 3 * 523031 + 1 = 1569094 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 523031 + 3 = 2615158 from by ring, show 5 + 2 = 7 from by ring,
      show 12 * 523031 + 8 = 6276380 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 10460636) (c₂ := ⟨0, 0, 0, 4358598, 8⟩)
  · have h := mod1_sn 871719 6
    rw [show 3 * 871719 + 1 = 2615158 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 871719 + 3 = 4358598 from by ring, show 6 + 2 = 8 from by ring,
      show 12 * 871719 + 8 = 10460636 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 17434395) (c₂ := ⟨0, 0, 0, 7264331, 8⟩)
  · have h := mod0_sn 1452866 7
    rw [show 3 * 1452866 = 4358598 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 1452866 + 1 = 7264331 from by ring, show 12 * 1452866 + 3 = 17434395 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 29057326) (c₂ := ⟨0, 0, 0, 12107219, 7⟩)
  · have h := mod2_sn 2421443 7
    rw [show 3 * 2421443 + 2 = 7264331 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 2421443 + 4 = 12107219 from by ring, show 12 * 2421443 + 10 = 29057326 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 48428878) (c₂ := ⟨0, 0, 0, 20178699, 6⟩)
  · have h := mod2_sn 4035739 6
    rw [show 3 * 4035739 + 2 = 12107219 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 4035739 + 4 = 20178699 from by ring, show 12 * 4035739 + 10 = 48428878 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 80714799) (c₂ := ⟨0, 0, 0, 33631166, 6⟩)
  · have h := mod0_sn 6726233 5
    rw [show 3 * 6726233 = 20178699 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 6726233 + 1 = 33631166 from by ring, show 12 * 6726233 + 3 = 80714799 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 134524666) (c₂ := ⟨0, 0, 0, 56051944, 5⟩)
  · have h := mod2_sn 11210388 5
    rw [show 3 * 11210388 + 2 = 33631166 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 11210388 + 4 = 56051944 from by ring, show 12 * 11210388 + 10 = 134524666 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 224207780) (c₂ := ⟨0, 0, 0, 93419908, 6⟩)
  · have h := mod1_sn 18683981 4
    rw [show 3 * 18683981 + 1 = 56051944 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 18683981 + 3 = 93419908 from by ring, show 4 + 2 = 6 from by ring,
      show 12 * 18683981 + 8 = 224207780 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 373679636) (c₂ := ⟨0, 0, 0, 155699848, 7⟩)
  · have h := mod1_sn 31139969 5
    rw [show 3 * 31139969 + 1 = 93419908 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 31139969 + 3 = 155699848 from by ring, show 5 + 2 = 7 from by ring,
      show 12 * 31139969 + 8 = 373679636 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 622799396) (c₂ := ⟨0, 0, 0, 259499748, 8⟩)
  · have h := mod1_sn 51899949 6
    rw [show 3 * 51899949 + 1 = 155699848 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 51899949 + 3 = 259499748 from by ring, show 6 + 2 = 8 from by ring,
      show 12 * 51899949 + 8 = 622799396 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1037998995) (c₂ := ⟨0, 0, 0, 432499581, 8⟩)
  · have h := mod0_sn 86499916 7
    rw [show 3 * 86499916 = 259499748 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 86499916 + 1 = 432499581 from by ring, show 12 * 86499916 + 3 = 1037998995 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1729998327) (c₂ := ⟨0, 0, 0, 720832636, 8⟩)
  · have h := mod0_sn 144166527 7
    rw [show 3 * 144166527 = 432499581 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 144166527 + 1 = 720832636 from by ring, show 12 * 144166527 + 3 = 1729998327 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2883330548) (c₂ := ⟨0, 0, 0, 1201387728, 9⟩)
  · have h := mod1_sn 240277545 7
    rw [show 3 * 240277545 + 1 = 720832636 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 240277545 + 3 = 1201387728 from by ring, show 7 + 2 = 9 from by ring,
      show 12 * 240277545 + 8 = 2883330548 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 4805550915) (c₂ := ⟨0, 0, 0, 2002312881, 9⟩)
  · have h := mod0_sn 400462576 8
    rw [show 3 * 400462576 = 1201387728 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 400462576 + 1 = 2002312881 from by ring, show 12 * 400462576 + 3 = 4805550915 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 8009251527) (c₂ := ⟨0, 0, 0, 3337188136, 9⟩)
  · have h := mod0_sn 667437627 8
    rw [show 3 * 667437627 = 2002312881 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 667437627 + 1 = 3337188136 from by ring, show 12 * 667437627 + 3 = 8009251527 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 13348752548) (c₂ := ⟨0, 0, 0, 5561980228, 10⟩)
  · have h := mod1_sn 1112396045 8
    rw [show 3 * 1112396045 + 1 = 3337188136 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 1112396045 + 3 = 5561980228 from by ring, show 8 + 2 = 10 from by ring,
      show 12 * 1112396045 + 8 = 13348752548 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 22247920916) (c₂ := ⟨0, 0, 0, 9269967048, 11⟩)
  · have h := mod1_sn 1853993409 9
    rw [show 3 * 1853993409 + 1 = 5561980228 from by ring, show 9 + 1 = 10 from by ring,
      show 5 * 1853993409 + 3 = 9269967048 from by ring, show 9 + 2 = 11 from by ring,
      show 12 * 1853993409 + 8 = 22247920916 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 37079868195) (c₂ := ⟨0, 0, 0, 15449945081, 11⟩)
  · have h := mod0_sn 3089989016 10
    rw [show 3 * 3089989016 = 9269967048 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 3089989016 + 1 = 15449945081 from by ring, show 12 * 3089989016 + 3 = 37079868195 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 61799780326) (c₂ := ⟨0, 0, 0, 25749908469, 10⟩)
  · have h := mod2_sn 5149981693 10
    rw [show 3 * 5149981693 + 2 = 15449945081 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 5149981693 + 4 = 25749908469 from by ring, show 12 * 5149981693 + 10 = 61799780326 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 102999633879) (c₂ := ⟨0, 0, 0, 42916514116, 10⟩)
  · have h := mod0_sn 8583302823 9
    rw [show 3 * 8583302823 = 25749908469 from by ring, show 9 + 1 = 10 from by ring,
      show 5 * 8583302823 + 1 = 42916514116 from by ring, show 12 * 8583302823 + 3 = 102999633879 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 171666056468) (c₂ := ⟨0, 0, 0, 71527523528, 11⟩)
  · have h := mod1_sn 14305504705 9
    rw [show 3 * 14305504705 + 1 = 42916514116 from by ring, show 9 + 1 = 10 from by ring,
      show 5 * 14305504705 + 3 = 71527523528 from by ring, show 9 + 2 = 11 from by ring,
      show 12 * 14305504705 + 8 = 171666056468 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 286110094114) (c₂ := ⟨0, 0, 0, 119212539214, 10⟩)
  · have h := mod2_sn 23842507842 10
    rw [show 3 * 23842507842 + 2 = 71527523528 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 23842507842 + 4 = 119212539214 from by ring, show 12 * 23842507842 + 10 = 286110094114 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 476850156860) (c₂ := ⟨0, 0, 0, 198687565358, 11⟩)
  · have h := mod1_sn 39737513071 9
    rw [show 3 * 39737513071 + 1 = 119212539214 from by ring, show 9 + 1 = 10 from by ring,
      show 5 * 39737513071 + 3 = 198687565358 from by ring, show 9 + 2 = 11 from by ring,
      show 12 * 39737513071 + 8 = 476850156860 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 794750261434) (c₂ := ⟨0, 0, 0, 331145942264, 10⟩)
  · have h := mod2_sn 66229188452 10
    rw [show 3 * 66229188452 + 2 = 198687565358 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 66229188452 + 4 = 331145942264 from by ring, show 12 * 66229188452 + 10 = 794750261434 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1324583769058) (c₂ := ⟨0, 0, 0, 551909903774, 9⟩)
  · have h := mod2_sn 110381980754 9
    rw [show 3 * 110381980754 + 2 = 331145942264 from by ring, show 9 + 1 = 10 from by ring,
      show 5 * 110381980754 + 4 = 551909903774 from by ring, show 12 * 110381980754 + 10 = 1324583769058 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2207639615098) (c₂ := ⟨0, 0, 0, 919849839624, 8⟩)
  · have h := mod2_sn 183969967924 8
    rw [show 3 * 183969967924 + 2 = 551909903774 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 183969967924 + 4 = 919849839624 from by ring, show 12 * 183969967924 + 10 = 2207639615098 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 3679399358499) (c₂ := ⟨0, 0, 0, 1533083066041, 8⟩)
  · have h := mod0_sn 306616613208 7
    rw [show 3 * 306616613208 = 919849839624 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 306616613208 + 1 = 1533083066041 from by ring, show 12 * 306616613208 + 3 = 3679399358499 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 6132332264168) (c₂ := ⟨0, 0, 0, 2555138443403, 9⟩)
  · have h := mod1_sn 511027688680 7
    rw [show 3 * 511027688680 + 1 = 1533083066041 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 511027688680 + 3 = 2555138443403 from by ring, show 7 + 2 = 9 from by ring,
      show 12 * 511027688680 + 8 = 6132332264168 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 10220553773614) (c₂ := ⟨0, 0, 0, 4258564072339, 8⟩)
  · have h := mod2_sn 851712814467 8
    rw [show 3 * 851712814467 + 2 = 2555138443403 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 851712814467 + 4 = 4258564072339 from by ring, show 12 * 851712814467 + 10 = 10220553773614 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 17034256289360) (c₂ := ⟨0, 0, 0, 7097606787233, 9⟩)
  · have h := mod1_sn 1419521357446 7
    rw [show 3 * 1419521357446 + 1 = 4258564072339 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 1419521357446 + 3 = 7097606787233 from by ring, show 7 + 2 = 9 from by ring,
      show 12 * 1419521357446 + 8 = 17034256289360 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 28390427148934) (c₂ := ⟨0, 0, 0, 11829344645389, 8⟩)
  · have h := mod2_sn 2365868929077 8
    rw [show 3 * 2365868929077 + 2 = 7097606787233 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 2365868929077 + 4 = 11829344645389 from by ring, show 12 * 2365868929077 + 10 = 28390427148934 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 47317378581560) (c₂ := ⟨0, 0, 0, 19715574408983, 9⟩)
  · have h := mod1_sn 3943114881796 7
    rw [show 3 * 3943114881796 + 1 = 11829344645389 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 3943114881796 + 3 = 19715574408983 from by ring, show 7 + 2 = 9 from by ring,
      show 12 * 3943114881796 + 8 = 47317378581560 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 78862297635934) (c₂ := ⟨0, 0, 0, 32859290681639, 8⟩)
  · have h := mod2_sn 6571858136327 8
    rw [show 3 * 6571858136327 + 2 = 19715574408983 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 6571858136327 + 4 = 32859290681639 from by ring, show 12 * 6571858136327 + 10 = 78862297635934 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 131437162726558) (c₂ := ⟨0, 0, 0, 54765484469399, 7⟩)
  · have h := mod2_sn 10953096893879 7
    rw [show 3 * 10953096893879 + 2 = 32859290681639 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 10953096893879 + 4 = 54765484469399 from by ring, show 12 * 10953096893879 + 10 = 131437162726558 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 219061937877598) (c₂ := ⟨0, 0, 0, 91275807448999, 6⟩)
  · have h := mod2_sn 18255161489799 6
    rw [show 3 * 18255161489799 + 2 = 54765484469399 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 18255161489799 + 4 = 91275807448999 from by ring, show 12 * 18255161489799 + 10 = 219061937877598 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 365103229796000) (c₂ := ⟨0, 0, 0, 152126345748333, 7⟩)
  · have h := mod1_sn 30425269149666 5
    rw [show 3 * 30425269149666 + 1 = 91275807448999 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 30425269149666 + 3 = 152126345748333 from by ring, show 5 + 2 = 7 from by ring,
      show 12 * 30425269149666 + 8 = 365103229796000 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 608505382993335) (c₂ := ⟨0, 0, 0, 253543909580556, 7⟩)
  · have h := mod0_sn 50708781916111 6
    rw [show 3 * 50708781916111 = 152126345748333 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 50708781916111 + 1 = 253543909580556 from by ring, show 12 * 50708781916111 + 3 = 608505382993335 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1014175638322227) (c₂ := ⟨0, 0, 0, 422573182634261, 7⟩)
  · have h := mod0_sn 84514636526852 6
    rw [show 3 * 84514636526852 = 253543909580556 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 84514636526852 + 1 = 422573182634261 from by ring, show 12 * 84514636526852 + 3 = 1014175638322227 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1690292730537046) (c₂ := ⟨0, 0, 0, 704288637723769, 6⟩)
  · have h := mod2_sn 140857727544753 6
    rw [show 3 * 140857727544753 + 2 = 422573182634261 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 140857727544753 + 4 = 704288637723769 from by ring, show 12 * 140857727544753 + 10 = 1690292730537046 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2817154550895080) (c₂ := ⟨0, 0, 0, 1173814396206283, 7⟩)
  · have h := mod1_sn 234762879241256 5
    rw [show 3 * 234762879241256 + 1 = 704288637723769 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 234762879241256 + 3 = 1173814396206283 from by ring, show 5 + 2 = 7 from by ring,
      show 12 * 234762879241256 + 8 = 2817154550895080 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 4695257584825136) (c₂ := ⟨0, 0, 0, 1956357327010473, 8⟩)
  · have h := mod1_sn 391271465402094 6
    rw [show 3 * 391271465402094 + 1 = 1173814396206283 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 391271465402094 + 3 = 1956357327010473 from by ring, show 6 + 2 = 8 from by ring,
      show 12 * 391271465402094 + 8 = 4695257584825136 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 7825429308041895) (c₂ := ⟨0, 0, 0, 3260595545017456, 8⟩)
  · have h := mod0_sn 652119109003491 7
    rw [show 3 * 652119109003491 = 1956357327010473 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 652119109003491 + 1 = 3260595545017456 from by ring, show 12 * 652119109003491 + 3 = 7825429308041895 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 13042382180069828) (c₂ := ⟨0, 0, 0, 5434325908362428, 9⟩)
  · have h := mod1_sn 1086865181672485 7
    rw [show 3 * 1086865181672485 + 1 = 3260595545017456 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 1086865181672485 + 3 = 5434325908362428 from by ring, show 7 + 2 = 9 from by ring,
      show 12 * 1086865181672485 + 8 = 13042382180069828 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 21737303633449714) (c₂ := ⟨0, 0, 0, 9057209847270714, 8⟩)
  · have h := mod2_sn 1811441969454142 8
    rw [show 3 * 1811441969454142 + 2 = 5434325908362428 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 1811441969454142 + 4 = 9057209847270714 from by ring, show 12 * 1811441969454142 + 10 = 21737303633449714 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 36228839389082859) (c₂ := ⟨0, 0, 0, 15095349745451191, 8⟩)
  · have h := mod0_sn 3019069949090238 7
    rw [show 3 * 3019069949090238 = 9057209847270714 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 3019069949090238 + 1 = 15095349745451191 from by ring, show 12 * 3019069949090238 + 3 = 36228839389082859 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 60381398981804768) (c₂ := ⟨0, 0, 0, 25158916242418653, 9⟩)
  · have h := mod1_sn 5031783248483730 7
    rw [show 3 * 5031783248483730 + 1 = 15095349745451191 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 5031783248483730 + 3 = 25158916242418653 from by ring, show 7 + 2 = 9 from by ring,
      show 12 * 5031783248483730 + 8 = 60381398981804768 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 100635664969674615) (c₂ := ⟨0, 0, 0, 41931527070697756, 9⟩)
  · have h := mod0_sn 8386305414139551 8
    rw [show 3 * 8386305414139551 = 25158916242418653 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 8386305414139551 + 1 = 41931527070697756 from by ring, show 12 * 8386305414139551 + 3 = 100635664969674615 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 167726108282791028) (c₂ := ⟨0, 0, 0, 69885878451162928, 10⟩)
  · have h := mod1_sn 13977175690232585 8
    rw [show 3 * 13977175690232585 + 1 = 41931527070697756 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 13977175690232585 + 3 = 69885878451162928 from by ring, show 8 + 2 = 10 from by ring,
      show 12 * 13977175690232585 + 8 = 167726108282791028 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 279543513804651716) (c₂ := ⟨0, 0, 0, 116476464085271548, 11⟩)
  · have h := mod1_sn 23295292817054309 9
    rw [show 3 * 23295292817054309 + 1 = 69885878451162928 from by ring, show 9 + 1 = 10 from by ring,
      show 5 * 23295292817054309 + 3 = 116476464085271548 from by ring, show 9 + 2 = 11 from by ring,
      show 12 * 23295292817054309 + 8 = 279543513804651716 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 465905856341086196) (c₂ := ⟨0, 0, 0, 194127440142119248, 12⟩)
  · have h := mod1_sn 38825488028423849 10
    rw [show 3 * 38825488028423849 + 1 = 116476464085271548 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 38825488028423849 + 3 = 194127440142119248 from by ring, show 10 + 2 = 12 from by ring,
      show 12 * 38825488028423849 + 8 = 465905856341086196 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 776509760568476996) (c₂ := ⟨0, 0, 0, 323545733570198748, 13⟩)
  · have h := mod1_sn 64709146714039749 11
    rw [show 3 * 64709146714039749 + 1 = 194127440142119248 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 64709146714039749 + 3 = 323545733570198748 from by ring, show 11 + 2 = 13 from by ring,
      show 12 * 64709146714039749 + 8 = 776509760568476996 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1294182934280794995) (c₂ := ⟨0, 0, 0, 539242889283664581, 13⟩)
  · have h := mod0_sn 107848577856732916 12
    rw [show 3 * 107848577856732916 = 323545733570198748 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 107848577856732916 + 1 = 539242889283664581 from by ring, show 12 * 107848577856732916 + 3 = 1294182934280794995 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2156971557134658327) (c₂ := ⟨0, 0, 0, 898738148806107636, 13⟩)
  · have h := mod0_sn 179747629761221527 12
    rw [show 3 * 179747629761221527 = 539242889283664581 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 179747629761221527 + 1 = 898738148806107636 from by ring, show 12 * 179747629761221527 + 3 = 2156971557134658327 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 3594952595224430547) (c₂ := ⟨0, 0, 0, 1497896914676846061, 13⟩)
  · have h := mod0_sn 299579382935369212 12
    rw [show 3 * 299579382935369212 = 898738148806107636 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 299579382935369212 + 1 = 1497896914676846061 from by ring, show 12 * 299579382935369212 + 3 = 3594952595224430547 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 5991587658707384247) (c₂ := ⟨0, 0, 0, 2496494857794743436, 13⟩)
  · have h := mod0_sn 499298971558948687 12
    rw [show 3 * 499298971558948687 = 1497896914676846061 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 499298971558948687 + 1 = 2496494857794743436 from by ring, show 12 * 499298971558948687 + 3 = 5991587658707384247 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 9985979431178973747) (c₂ := ⟨0, 0, 0, 4160824762991239061, 13⟩)
  · have h := mod0_sn 832164952598247812 12
    rw [show 3 * 832164952598247812 = 2496494857794743436 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 832164952598247812 + 1 = 4160824762991239061 from by ring, show 12 * 832164952598247812 + 3 = 9985979431178973747 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 16643299051964956246) (c₂ := ⟨0, 0, 0, 6934707938318731769, 12⟩)
  · have h := mod2_sn 1386941587663746353 12
    rw [show 3 * 1386941587663746353 + 2 = 4160824762991239061 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 1386941587663746353 + 4 = 6934707938318731769 from by ring, show 12 * 1386941587663746353 + 10 = 16643299051964956246 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 27738831753274927078) (c₂ := ⟨0, 0, 0, 11557846563864552949, 11⟩)
  · have h := mod2_sn 2311569312772910589 11
    rw [show 3 * 2311569312772910589 + 2 = 6934707938318731769 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 2311569312772910589 + 4 = 11557846563864552949 from by ring, show 12 * 2311569312772910589 + 10 = 27738831753274927078 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 46231386255458211800) (c₂ := ⟨0, 0, 0, 19263077606440921583, 12⟩)
  · have h := mod1_sn 3852615521288184316 10
    rw [show 3 * 3852615521288184316 + 1 = 11557846563864552949 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 3852615521288184316 + 3 = 19263077606440921583 from by ring, show 10 + 2 = 12 from by ring,
      show 12 * 3852615521288184316 + 8 = 46231386255458211800 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 77052310425763686334) (c₂ := ⟨0, 0, 0, 32105129344068202639, 11⟩)
  · have h := mod2_sn 6421025868813640527 11
    rw [show 3 * 6421025868813640527 + 2 = 19263077606440921583 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 6421025868813640527 + 4 = 32105129344068202639 from by ring, show 12 * 6421025868813640527 + 10 = 77052310425763686334 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 128420517376272810560) (c₂ := ⟨0, 0, 0, 53508548906780337733, 12⟩)
  · have h := mod1_sn 10701709781356067546 10
    rw [show 3 * 10701709781356067546 + 1 = 32105129344068202639 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 10701709781356067546 + 3 = 53508548906780337733 from by ring, show 10 + 2 = 12 from by ring,
      show 12 * 10701709781356067546 + 8 = 128420517376272810560 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 214034195627121350936) (c₂ := ⟨0, 0, 0, 89180914844633896223, 13⟩)
  · have h := mod1_sn 17836182968926779244 11
    rw [show 3 * 17836182968926779244 + 1 = 53508548906780337733 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 17836182968926779244 + 3 = 89180914844633896223 from by ring, show 11 + 2 = 13 from by ring,
      show 12 * 17836182968926779244 + 8 = 214034195627121350936 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 356723659378535584894) (c₂ := ⟨0, 0, 0, 148634858074389827039, 12⟩)
  · have h := mod2_sn 29726971614877965407 12
    rw [show 3 * 29726971614877965407 + 2 = 89180914844633896223 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 29726971614877965407 + 4 = 148634858074389827039 from by ring, show 12 * 29726971614877965407 + 10 = 356723659378535584894 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 594539432297559308158) (c₂ := ⟨0, 0, 0, 247724763457316378399, 11⟩)
  · have h := mod2_sn 49544952691463275679 11
    rw [show 3 * 49544952691463275679 + 2 = 148634858074389827039 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 49544952691463275679 + 4 = 247724763457316378399 from by ring, show 12 * 49544952691463275679 + 10 = 594539432297559308158 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 990899053829265513598) (c₂ := ⟨0, 0, 0, 412874605762193963999, 10⟩)
  · have h := mod2_sn 82574921152438792799 10
    rw [show 3 * 82574921152438792799 + 2 = 247724763457316378399 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 82574921152438792799 + 4 = 412874605762193963999 from by ring, show 12 * 82574921152438792799 + 10 = 990899053829265513598 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1651498423048775855998) (c₂ := ⟨0, 0, 0, 688124342936989939999, 9⟩)
  · have h := mod2_sn 137624868587397987999 9
    rw [show 3 * 137624868587397987999 + 2 = 412874605762193963999 from by ring, show 9 + 1 = 10 from by ring,
      show 5 * 137624868587397987999 + 4 = 688124342936989939999 from by ring, show 12 * 137624868587397987999 + 10 = 1651498423048775855998 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2752497371747959760000) (c₂ := ⟨0, 0, 0, 1146873904894983233333, 10⟩)
  · have h := mod1_sn 229374780978996646666 8
    rw [show 3 * 229374780978996646666 + 1 = 688124342936989939999 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 229374780978996646666 + 3 = 1146873904894983233333 from by ring, show 8 + 2 = 10 from by ring,
      show 12 * 229374780978996646666 + 8 = 2752497371747959760000 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 4587495619579932933334) (c₂ := ⟨0, 0, 0, 1911456508158305388889, 9⟩)
  · have h := mod2_sn 382291301631661077777 9
    rw [show 3 * 382291301631661077777 + 2 = 1146873904894983233333 from by ring, show 9 + 1 = 10 from by ring,
      show 5 * 382291301631661077777 + 4 = 1911456508158305388889 from by ring, show 12 * 382291301631661077777 + 10 = 4587495619579932933334 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 7645826032633221555560) (c₂ := ⟨0, 0, 0, 3185760846930508981483, 10⟩)
  · have h := mod1_sn 637152169386101796296 8
    rw [show 3 * 637152169386101796296 + 1 = 1911456508158305388889 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 637152169386101796296 + 3 = 3185760846930508981483 from by ring, show 8 + 2 = 10 from by ring,
      show 12 * 637152169386101796296 + 8 = 7645826032633221555560 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 12743043387722035925936) (c₂ := ⟨0, 0, 0, 5309601411550848302473, 11⟩)
  · have h := mod1_sn 1061920282310169660494 9
    rw [show 3 * 1061920282310169660494 + 1 = 3185760846930508981483 from by ring, show 9 + 1 = 10 from by ring,
      show 5 * 1061920282310169660494 + 3 = 5309601411550848302473 from by ring, show 9 + 2 = 11 from by ring,
      show 12 * 1061920282310169660494 + 8 = 12743043387722035925936 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 21238405646203393209896) (c₂ := ⟨0, 0, 0, 8849335685918080504123, 12⟩)
  · have h := mod1_sn 1769867137183616100824 10
    rw [show 3 * 1769867137183616100824 + 1 = 5309601411550848302473 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 1769867137183616100824 + 3 = 8849335685918080504123 from by ring, show 10 + 2 = 12 from by ring,
      show 12 * 1769867137183616100824 + 8 = 21238405646203393209896 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 35397342743672322016496) (c₂ := ⟨0, 0, 0, 14748892809863467506873, 13⟩)
  · have h := mod1_sn 2949778561972693501374 11
    rw [show 3 * 2949778561972693501374 + 1 = 8849335685918080504123 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 2949778561972693501374 + 3 = 14748892809863467506873 from by ring, show 11 + 2 = 13 from by ring,
      show 12 * 2949778561972693501374 + 8 = 35397342743672322016496 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 58995571239453870027495) (c₂ := ⟨0, 0, 0, 24581488016439112511456, 13⟩)
  · have h := mod0_sn 4916297603287822502291 12
    rw [show 3 * 4916297603287822502291 = 14748892809863467506873 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 4916297603287822502291 + 1 = 24581488016439112511456 from by ring, show 12 * 4916297603287822502291 + 3 = 58995571239453870027495 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 98325952065756450045826) (c₂ := ⟨0, 0, 0, 40969146694065187519094, 12⟩)
  · have h := mod2_sn 8193829338813037503818 12
    rw [show 3 * 8193829338813037503818 + 2 = 24581488016439112511456 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 8193829338813037503818 + 4 = 40969146694065187519094 from by ring, show 12 * 8193829338813037503818 + 10 = 98325952065756450045826 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 163876586776260750076378) (c₂ := ⟨0, 0, 0, 68281911156775312531824, 11⟩)
  · have h := mod2_sn 13656382231355062506364 11
    rw [show 3 * 13656382231355062506364 + 2 = 40969146694065187519094 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 13656382231355062506364 + 4 = 68281911156775312531824 from by ring, show 12 * 13656382231355062506364 + 10 = 163876586776260750076378 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 273127644627101250127299) (c₂ := ⟨0, 0, 0, 113803185261292187553041, 11⟩)
  · have h := mod0_sn 22760637052258437510608 10
    rw [show 3 * 22760637052258437510608 = 68281911156775312531824 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 22760637052258437510608 + 1 = 113803185261292187553041 from by ring, show 12 * 22760637052258437510608 + 3 = 273127644627101250127299 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 455212741045168750212166) (c₂ := ⟨0, 0, 0, 189671975435486979255069, 10⟩)
  · have h := mod2_sn 37934395087097395851013 10
    rw [show 3 * 37934395087097395851013 + 2 = 113803185261292187553041 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 37934395087097395851013 + 4 = 189671975435486979255069 from by ring, show 12 * 37934395087097395851013 + 10 = 455212741045168750212166 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 758687901741947917020279) (c₂ := ⟨0, 0, 0, 316119959059144965425116, 10⟩)
  · have h := mod0_sn 63223991811828993085023 9
    rw [show 3 * 63223991811828993085023 = 189671975435486979255069 from by ring, show 9 + 1 = 10 from by ring,
      show 5 * 63223991811828993085023 + 1 = 316119959059144965425116 from by ring, show 12 * 63223991811828993085023 + 3 = 758687901741947917020279 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1264479836236579861700468) (c₂ := ⟨0, 0, 0, 526866598431908275708528, 11⟩)
  · have h := mod1_sn 105373319686381655141705 9
    rw [show 3 * 105373319686381655141705 + 1 = 316119959059144965425116 from by ring, show 9 + 1 = 10 from by ring,
      show 5 * 105373319686381655141705 + 3 = 526866598431908275708528 from by ring, show 9 + 2 = 11 from by ring,
      show 12 * 105373319686381655141705 + 8 = 1264479836236579861700468 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2107466393727633102834116) (c₂ := ⟨0, 0, 0, 878110997386513792847548, 12⟩)
  · have h := mod1_sn 175622199477302758569509 10
    rw [show 3 * 175622199477302758569509 + 1 = 526866598431908275708528 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 175622199477302758569509 + 3 = 878110997386513792847548 from by ring, show 10 + 2 = 12 from by ring,
      show 12 * 175622199477302758569509 + 8 = 2107466393727633102834116 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 3512443989546055171390196) (c₂ := ⟨0, 0, 0, 1463518328977522988079248, 13⟩)
  · have h := mod1_sn 292703665795504597615849 11
    rw [show 3 * 292703665795504597615849 + 1 = 878110997386513792847548 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 292703665795504597615849 + 3 = 1463518328977522988079248 from by ring, show 11 + 2 = 13 from by ring,
      show 12 * 292703665795504597615849 + 8 = 3512443989546055171390196 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 5854073315910091952316994) (c₂ := ⟨0, 0, 0, 2439197214962538313465414, 12⟩)
  · have h := mod2_sn 487839442992507662693082 12
    rw [show 3 * 487839442992507662693082 + 2 = 1463518328977522988079248 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 487839442992507662693082 + 4 = 2439197214962538313465414 from by ring, show 12 * 487839442992507662693082 + 10 = 5854073315910091952316994 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 9756788859850153253861660) (c₂ := ⟨0, 0, 0, 4065328691604230522442358, 13⟩)
  · have h := mod1_sn 813065738320846104488471 11
    rw [show 3 * 813065738320846104488471 + 1 = 2439197214962538313465414 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 813065738320846104488471 + 3 = 4065328691604230522442358 from by ring, show 11 + 2 = 13 from by ring,
      show 12 * 813065738320846104488471 + 8 = 9756788859850153253861660 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 16261314766416922089769436) (c₂ := ⟨0, 0, 0, 6775547819340384204070598, 14⟩)
  · have h := mod1_sn 1355109563868076840814119 12
    rw [show 3 * 1355109563868076840814119 + 1 = 4065328691604230522442358 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 1355109563868076840814119 + 3 = 6775547819340384204070598 from by ring, show 12 + 2 = 14 from by ring,
      show 12 * 1355109563868076840814119 + 8 = 16261314766416922089769436 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 27102191277361536816282394) (c₂ := ⟨0, 0, 0, 11292579698900640340117664, 13⟩)
  · have h := mod2_sn 2258515939780128068023532 13
    rw [show 3 * 2258515939780128068023532 + 2 = 6775547819340384204070598 from by ring, show 13 + 1 = 14 from by ring,
      show 5 * 2258515939780128068023532 + 4 = 11292579698900640340117664 from by ring, show 12 * 2258515939780128068023532 + 10 = 27102191277361536816282394 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 45170318795602561360470658) (c₂ := ⟨0, 0, 0, 18820966164834400566862774, 12⟩)
  · have h := mod2_sn 3764193232966880113372554 12
    rw [show 3 * 3764193232966880113372554 + 2 = 11292579698900640340117664 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 3764193232966880113372554 + 4 = 18820966164834400566862774 from by ring, show 12 * 3764193232966880113372554 + 10 = 45170318795602561360470658 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 75283864659337602267451100) (c₂ := ⟨0, 0, 0, 31368276941390667611437958, 13⟩)
  · have h := mod1_sn 6273655388278133522287591 11
    rw [show 3 * 6273655388278133522287591 + 1 = 18820966164834400566862774 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 6273655388278133522287591 + 3 = 31368276941390667611437958 from by ring, show 11 + 2 = 13 from by ring,
      show 12 * 6273655388278133522287591 + 8 = 75283864659337602267451100 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 125473107765562670445751834) (c₂ := ⟨0, 0, 0, 52280461568984446019063264, 12⟩)
  · have h := mod2_sn 10456092313796889203812652 12
    rw [show 3 * 10456092313796889203812652 + 2 = 31368276941390667611437958 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 10456092313796889203812652 + 4 = 52280461568984446019063264 from by ring, show 12 * 10456092313796889203812652 + 10 = 125473107765562670445751834 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 209121846275937784076253058) (c₂ := ⟨0, 0, 0, 87134102614974076698438774, 11⟩)
  · have h := mod2_sn 17426820522994815339687754 11
    rw [show 3 * 17426820522994815339687754 + 2 = 52280461568984446019063264 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 17426820522994815339687754 + 4 = 87134102614974076698438774 from by ring, show 12 * 17426820522994815339687754 + 10 = 209121846275937784076253058 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 348536410459896306793755099) (c₂ := ⟨0, 0, 0, 145223504358290127830731291, 11⟩)
  · have h := mod0_sn 29044700871658025566146258 10
    rw [show 3 * 29044700871658025566146258 = 87134102614974076698438774 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 29044700871658025566146258 + 1 = 145223504358290127830731291 from by ring, show 12 * 29044700871658025566146258 + 3 = 348536410459896306793755099 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 580894017433160511322925168) (c₂ := ⟨0, 0, 0, 242039173930483546384552153, 12⟩)
  · have h := mod1_sn 48407834786096709276910430 10
    rw [show 3 * 48407834786096709276910430 + 1 = 145223504358290127830731291 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 48407834786096709276910430 + 3 = 242039173930483546384552153 from by ring, show 10 + 2 = 12 from by ring,
      show 12 * 48407834786096709276910430 + 8 = 580894017433160511322925168 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 968156695721934185538208616) (c₂ := ⟨0, 0, 0, 403398623217472577307586923, 13⟩)
  · have h := mod1_sn 80679724643494515461517384 11
    rw [show 3 * 80679724643494515461517384 + 1 = 242039173930483546384552153 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 80679724643494515461517384 + 3 = 403398623217472577307586923 from by ring, show 11 + 2 = 13 from by ring,
      show 12 * 80679724643494515461517384 + 8 = 968156695721934185538208616 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1613594492869890309230347695) (c₂ := ⟨0, 0, 0, 672331038695787628845978206, 13⟩)
  · have h := mod0_sn 134466207739157525769195641 12
    rw [show 3 * 134466207739157525769195641 = 403398623217472577307586923 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 134466207739157525769195641 + 1 = 672331038695787628845978206 from by ring, show 12 * 134466207739157525769195641 + 3 = 1613594492869890309230347695 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2689324154783150515383912826) (c₂ := ⟨0, 0, 0, 1120551731159646048076630344, 12⟩)
  · have h := mod2_sn 224110346231929209615326068 12
    rw [show 3 * 224110346231929209615326068 + 2 = 672331038695787628845978206 from by ring, show 12 + 1 = 13 from by ring,
      show 5 * 224110346231929209615326068 + 4 = 1120551731159646048076630344 from by ring, show 12 * 224110346231929209615326068 + 10 = 2689324154783150515383912826 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 4482206924638584192306521379) (c₂ := ⟨0, 0, 0, 1867586218599410080127717241, 12⟩)
  · have h := mod0_sn 373517243719882016025543448 11
    rw [show 3 * 373517243719882016025543448 = 1120551731159646048076630344 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 373517243719882016025543448 + 1 = 1867586218599410080127717241 from by ring, show 12 * 373517243719882016025543448 + 3 = 4482206924638584192306521379 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 7470344874397640320510868967) (c₂ := ⟨0, 0, 0, 3112643697665683466879528736, 12⟩)
  · have h := mod0_sn 622528739533136693375905747 11
    rw [show 3 * 622528739533136693375905747 = 1867586218599410080127717241 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 622528739533136693375905747 + 1 = 3112643697665683466879528736 from by ring, show 12 * 622528739533136693375905747 + 3 = 7470344874397640320510868967 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 12450574790662733867518114947) (c₂ := ⟨0, 0, 0, 5187739496109472444799214561, 12⟩)
  · have h := mod0_sn 1037547899221894488959842912 11
    rw [show 3 * 1037547899221894488959842912 = 3112643697665683466879528736 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 1037547899221894488959842912 + 1 = 5187739496109472444799214561 from by ring, show 12 * 1037547899221894488959842912 + 3 = 12450574790662733867518114947 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 20750957984437889779196858247) (c₂ := ⟨0, 0, 0, 8646232493515787407998690936, 12⟩)
  · have h := mod0_sn 1729246498703157481599738187 11
    rw [show 3 * 1729246498703157481599738187 = 5187739496109472444799214561 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 1729246498703157481599738187 + 1 = 8646232493515787407998690936 from by ring, show 12 * 1729246498703157481599738187 + 3 = 20750957984437889779196858247 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 34584929974063149631994763747) (c₂ := ⟨0, 0, 0, 14410387489192979013331151561, 12⟩)
  · have h := mod0_sn 2882077497838595802666230312 11
    rw [show 3 * 2882077497838595802666230312 = 8646232493515787407998690936 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 2882077497838595802666230312 + 1 = 14410387489192979013331151561 from by ring, show 12 * 2882077497838595802666230312 + 3 = 34584929974063149631994763747 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 57641549956771916053324606246) (c₂ := ⟨0, 0, 0, 24017312481988298355551919269, 11⟩)
  · have h := mod2_sn 4803462496397659671110383853 11
    rw [show 3 * 4803462496397659671110383853 + 2 = 14410387489192979013331151561 from by ring, show 11 + 1 = 12 from by ring,
      show 5 * 4803462496397659671110383853 + 4 = 24017312481988298355551919269 from by ring, show 12 * 4803462496397659671110383853 + 10 = 57641549956771916053324606246 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 96069249927953193422207677078) (c₂ := ⟨0, 0, 0, 40028854136647163925919865449, 10⟩)
  · have h := mod2_sn 8005770827329432785183973089 10
    rw [show 3 * 8005770827329432785183973089 + 2 = 24017312481988298355551919269 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 8005770827329432785183973089 + 4 = 40028854136647163925919865449 from by ring, show 12 * 8005770827329432785183973089 + 10 = 96069249927953193422207677078 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 160115416546588655703679461800) (c₂ := ⟨0, 0, 0, 66714756894411939876533109083, 11⟩)
  · have h := mod1_sn 13342951378882387975306621816 9
    rw [show 3 * 13342951378882387975306621816 + 1 = 40028854136647163925919865449 from by ring, show 9 + 1 = 10 from by ring,
      show 5 * 13342951378882387975306621816 + 3 = 66714756894411939876533109083 from by ring, show 9 + 2 = 11 from by ring,
      show 12 * 13342951378882387975306621816 + 8 = 160115416546588655703679461800 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 266859027577647759506132436334) (c₂ := ⟨0, 0, 0, 111191261490686566460888515139, 10⟩)
  · have h := mod2_sn 22238252298137313292177703027 10
    rw [show 3 * 22238252298137313292177703027 + 2 = 66714756894411939876533109083 from by ring, show 10 + 1 = 11 from by ring,
      show 5 * 22238252298137313292177703027 + 4 = 111191261490686566460888515139 from by ring, show 12 * 22238252298137313292177703027 + 10 = 266859027577647759506132436334 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 444765045962746265843554060558) (c₂ := ⟨0, 0, 0, 185318769151144277434814191899, 9⟩)
  · have h := mod2_sn 37063753830228855486962838379 9
    rw [show 3 * 37063753830228855486962838379 + 2 = 111191261490686566460888515139 from by ring, show 9 + 1 = 10 from by ring,
      show 5 * 37063753830228855486962838379 + 4 = 185318769151144277434814191899 from by ring, show 12 * 37063753830228855486962838379 + 10 = 444765045962746265843554060558 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 741275076604577109739256767599) (c₂ := ⟨0, 0, 0, 308864615251907129058023653166, 9⟩)
  · have h := mod0_sn 61772923050381425811604730633 8
    rw [show 3 * 61772923050381425811604730633 = 185318769151144277434814191899 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 61772923050381425811604730633 + 1 = 308864615251907129058023653166 from by ring, show 12 * 61772923050381425811604730633 + 3 = 741275076604577109739256767599 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1235458461007628516232094612666) (c₂ := ⟨0, 0, 0, 514774358753178548430039421944, 8⟩)
  · have h := mod2_sn 102954871750635709686007884388 8
    rw [show 3 * 102954871750635709686007884388 + 2 = 308864615251907129058023653166 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 102954871750635709686007884388 + 4 = 514774358753178548430039421944 from by ring, show 12 * 102954871750635709686007884388 + 10 = 1235458461007628516232094612666 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2059097435012714193720157687779) (c₂ := ⟨0, 0, 0, 857957264588630914050065703241, 8⟩)
  · have h := mod0_sn 171591452917726182810013140648 7
    rw [show 3 * 171591452917726182810013140648 = 514774358753178548430039421944 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 171591452917726182810013140648 + 1 = 857957264588630914050065703241 from by ring, show 12 * 171591452917726182810013140648 + 3 = 2059097435012714193720157687779 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 3431829058354523656200262812968) (c₂ := ⟨0, 0, 0, 1429928774314384856750109505403, 9⟩)
  · have h := mod1_sn 285985754862876971350021901080 7
    rw [show 3 * 285985754862876971350021901080 + 1 = 857957264588630914050065703241 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 285985754862876971350021901080 + 3 = 1429928774314384856750109505403 from by ring, show 7 + 2 = 9 from by ring,
      show 12 * 285985754862876971350021901080 + 8 = 3431829058354523656200262812968 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 5719715097257539427000438021614) (c₂ := ⟨0, 0, 0, 2383214623857308094583515842339, 8⟩)
  · have h := mod2_sn 476642924771461618916703168467 8
    rw [show 3 * 476642924771461618916703168467 + 2 = 1429928774314384856750109505403 from by ring, show 8 + 1 = 9 from by ring,
      show 5 * 476642924771461618916703168467 + 4 = 2383214623857308094583515842339 from by ring, show 12 * 476642924771461618916703168467 + 10 = 5719715097257539427000438021614 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 9532858495429232378334063369358) (c₂ := ⟨0, 0, 0, 3972024373095513490972526403899, 7⟩)
  · have h := mod2_sn 794404874619102698194505280779 7
    rw [show 3 * 794404874619102698194505280779 + 2 = 2383214623857308094583515842339 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 794404874619102698194505280779 + 4 = 3972024373095513490972526403899 from by ring, show 12 * 794404874619102698194505280779 + 10 = 9532858495429232378334063369358 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 15888097492382053963890105615598) (c₂ := ⟨0, 0, 0, 6620040621825855818287544006499, 6⟩)
  · have h := mod2_sn 1324008124365171163657508801299 6
    rw [show 3 * 1324008124365171163657508801299 + 2 = 3972024373095513490972526403899 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 1324008124365171163657508801299 + 4 = 6620040621825855818287544006499 from by ring, show 12 * 1324008124365171163657508801299 + 10 = 15888097492382053963890105615598 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 26480162487303423273150176025999) (c₂ := ⟨0, 0, 0, 11033401036376426363812573344166, 6⟩)
  · have h := mod0_sn 2206680207275285272762514668833 5
    rw [show 3 * 2206680207275285272762514668833 = 6620040621825855818287544006499 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 2206680207275285272762514668833 + 1 = 11033401036376426363812573344166 from by ring, show 12 * 2206680207275285272762514668833 + 3 = 26480162487303423273150176025999 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 44133604145505705455250293376668) (c₂ := ⟨0, 0, 0, 18389001727294043939687622240278, 7⟩)
  · have h := mod1_sn 3677800345458808787937524448055 5
    rw [show 3 * 3677800345458808787937524448055 + 1 = 11033401036376426363812573344166 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 3677800345458808787937524448055 + 3 = 18389001727294043939687622240278 from by ring, show 5 + 2 = 7 from by ring,
      show 12 * 3677800345458808787937524448055 + 8 = 44133604145505705455250293376668 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 73556006909176175758750488961114) (c₂ := ⟨0, 0, 0, 30648336212156739899479370400464, 6⟩)
  · have h := mod2_sn 6129667242431347979895874080092 6
    rw [show 3 * 6129667242431347979895874080092 + 2 = 18389001727294043939687622240278 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 6129667242431347979895874080092 + 4 = 30648336212156739899479370400464 from by ring, show 12 * 6129667242431347979895874080092 + 10 = 73556006909176175758750488961114 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 122593344848626959597917481601858) (c₂ := ⟨0, 0, 0, 51080560353594566499132284000774, 5⟩)
  · have h := mod2_sn 10216112070718913299826456800154 5
    rw [show 3 * 10216112070718913299826456800154 + 2 = 30648336212156739899479370400464 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 10216112070718913299826456800154 + 4 = 51080560353594566499132284000774 from by ring, show 12 * 10216112070718913299826456800154 + 10 = 122593344848626959597917481601858 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 204322241414378265996529136003098) (c₂ := ⟨0, 0, 0, 85134267255990944165220473334624, 4⟩)
  · have h := mod2_sn 17026853451198188833044094666924 4
    rw [show 3 * 17026853451198188833044094666924 + 2 = 51080560353594566499132284000774 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 17026853451198188833044094666924 + 4 = 85134267255990944165220473334624 from by ring, show 12 * 17026853451198188833044094666924 + 10 = 204322241414378265996529136003098 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 340537069023963776660881893338499) (c₂ := ⟨0, 0, 0, 141890445426651573608700788891041, 4⟩)
  · have h := mod0_sn 28378089085330314721740157778208 3
    rw [show 3 * 28378089085330314721740157778208 = 85134267255990944165220473334624 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 28378089085330314721740157778208 + 1 = 141890445426651573608700788891041 from by ring, show 12 * 28378089085330314721740157778208 + 3 = 340537069023963776660881893338499 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 567561781706606294434803155564168) (c₂ := ⟨0, 0, 0, 236484075711085956014501314818403, 5⟩)
  · have h := mod1_sn 47296815142217191202900262963680 3
    rw [show 3 * 47296815142217191202900262963680 + 1 = 141890445426651573608700788891041 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 47296815142217191202900262963680 + 3 = 236484075711085956014501314818403 from by ring, show 3 + 2 = 5 from by ring,
      show 12 * 47296815142217191202900262963680 + 8 = 567561781706606294434803155564168 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 945936302844343824058005259273616) (c₂ := ⟨0, 0, 0, 394140126185143260024168858030673, 6⟩)
  · have h := mod1_sn 78828025237028652004833771606134 4
    rw [show 3 * 78828025237028652004833771606134 + 1 = 236484075711085956014501314818403 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 78828025237028652004833771606134 + 3 = 394140126185143260024168858030673 from by ring, show 4 + 2 = 6 from by ring,
      show 12 * 78828025237028652004833771606134 + 8 = 945936302844343824058005259273616 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1576560504740573040096675432122696) (c₂ := ⟨0, 0, 0, 656900210308572100040281430051123, 7⟩)
  · have h := mod1_sn 131380042061714420008056286010224 5
    rw [show 3 * 131380042061714420008056286010224 + 1 = 394140126185143260024168858030673 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 131380042061714420008056286010224 + 3 = 656900210308572100040281430051123 from by ring, show 5 + 2 = 7 from by ring,
      show 12 * 131380042061714420008056286010224 + 8 = 1576560504740573040096675432122696 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2627600841234288400161125720204494) (c₂ := ⟨0, 0, 0, 1094833683847620166733802383418539, 6⟩)
  · have h := mod2_sn 218966736769524033346760476683707 6
    rw [show 3 * 218966736769524033346760476683707 + 2 = 656900210308572100040281430051123 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 218966736769524033346760476683707 + 4 = 1094833683847620166733802383418539 from by ring, show 12 * 218966736769524033346760476683707 + 10 = 2627600841234288400161125720204494 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 4379334735390480666935209533674158) (c₂ := ⟨0, 0, 0, 1824722806412700277889670639030899, 5⟩)
  · have h := mod2_sn 364944561282540055577934127806179 5
    rw [show 3 * 364944561282540055577934127806179 + 2 = 1094833683847620166733802383418539 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 364944561282540055577934127806179 + 4 = 1824722806412700277889670639030899 from by ring, show 12 * 364944561282540055577934127806179 + 10 = 4379334735390480666935209533674158 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 7298891225650801111558682556123598) (c₂ := ⟨0, 0, 0, 3041204677354500463149451065051499, 4⟩)
  · have h := mod2_sn 608240935470900092629890213010299 4
    rw [show 3 * 608240935470900092629890213010299 + 2 = 1824722806412700277889670639030899 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 608240935470900092629890213010299 + 4 = 3041204677354500463149451065051499 from by ring, show 12 * 608240935470900092629890213010299 + 10 = 7298891225650801111558682556123598 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 12164818709418001852597804260206000) (c₂ := ⟨0, 0, 0, 5068674462257500771915751775085833, 5⟩)
  · have h := mod1_sn 1013734892451500154383150355017166 3
    rw [show 3 * 1013734892451500154383150355017166 + 1 = 3041204677354500463149451065051499 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 1013734892451500154383150355017166 + 3 = 5068674462257500771915751775085833 from by ring, show 3 + 2 = 5 from by ring,
      show 12 * 1013734892451500154383150355017166 + 8 = 12164818709418001852597804260206000 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 20274697849030003087663007100343335) (c₂ := ⟨0, 0, 0, 8447790770429167953192919625143056, 5⟩)
  · have h := mod0_sn 1689558154085833590638583925028611 4
    rw [show 3 * 1689558154085833590638583925028611 = 5068674462257500771915751775085833 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 1689558154085833590638583925028611 + 1 = 8447790770429167953192919625143056 from by ring, show 12 * 1689558154085833590638583925028611 + 3 = 20274697849030003087663007100343335 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 33791163081716671812771678500572227) (c₂ := ⟨0, 0, 0, 14079651284048613255321532708571761, 5⟩)
  · have h := mod0_sn 2815930256809722651064306541714352 4
    rw [show 3 * 2815930256809722651064306541714352 = 8447790770429167953192919625143056 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 2815930256809722651064306541714352 + 1 = 14079651284048613255321532708571761 from by ring, show 12 * 2815930256809722651064306541714352 + 3 = 33791163081716671812771678500572227 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 56318605136194453021286130834287048) (c₂ := ⟨0, 0, 0, 23466085473414355425535887847619603, 6⟩)
  · have h := mod1_sn 4693217094682871085107177569523920 4
    rw [show 3 * 4693217094682871085107177569523920 + 1 = 14079651284048613255321532708571761 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 4693217094682871085107177569523920 + 3 = 23466085473414355425535887847619603 from by ring, show 4 + 2 = 6 from by ring,
      show 12 * 4693217094682871085107177569523920 + 8 = 56318605136194453021286130834287048 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 93864341893657421702143551390478414) (c₂ := ⟨0, 0, 0, 39110142455690592375893146412699339, 5⟩)
  · have h := mod2_sn 7822028491138118475178629282539867 5
    rw [show 3 * 7822028491138118475178629282539867 + 2 = 23466085473414355425535887847619603 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 7822028491138118475178629282539867 + 4 = 39110142455690592375893146412699339 from by ring, show 12 * 7822028491138118475178629282539867 + 10 = 93864341893657421702143551390478414 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 156440569822762369503572585650797358) (c₂ := ⟨0, 0, 0, 65183570759484320626488577354498899, 4⟩)
  · have h := mod2_sn 13036714151896864125297715470899779 4
    rw [show 3 * 13036714151896864125297715470899779 + 2 = 39110142455690592375893146412699339 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 13036714151896864125297715470899779 + 4 = 65183570759484320626488577354498899 from by ring, show 12 * 13036714151896864125297715470899779 + 10 = 156440569822762369503572585650797358 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 260734283037937282505954309417995599) (c₂ := ⟨0, 0, 0, 108639284599140534377480962257498166, 4⟩)
  · have h := mod0_sn 21727856919828106875496192451499633 3
    rw [show 3 * 21727856919828106875496192451499633 = 65183570759484320626488577354498899 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 21727856919828106875496192451499633 + 1 = 108639284599140534377480962257498166 from by ring, show 12 * 21727856919828106875496192451499633 + 3 = 260734283037937282505954309417995599 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 434557138396562137509923849029992668) (c₂ := ⟨0, 0, 0, 181065474331900890629134937095830278, 5⟩)
  · have h := mod1_sn 36213094866380178125826987419166055 3
    rw [show 3 * 36213094866380178125826987419166055 + 1 = 108639284599140534377480962257498166 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 36213094866380178125826987419166055 + 3 = 181065474331900890629134937095830278 from by ring, show 3 + 2 = 5 from by ring,
      show 12 * 36213094866380178125826987419166055 + 8 = 434557138396562137509923849029992668 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 724261897327603562516539748383321114) (c₂ := ⟨0, 0, 0, 301775790553168151048558228493050464, 4⟩)
  · have h := mod2_sn 60355158110633630209711645698610092 4
    rw [show 3 * 60355158110633630209711645698610092 + 2 = 181065474331900890629134937095830278 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 60355158110633630209711645698610092 + 4 = 301775790553168151048558228493050464 from by ring, show 12 * 60355158110633630209711645698610092 + 10 = 724261897327603562516539748383321114 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1207103162212672604194232913972201860) (c₂ := ⟨0, 0, 0, 502959650921946918414263714155084108, 5⟩)
  · have h := mod1_sn 100591930184389383682852742831016821 3
    rw [show 3 * 100591930184389383682852742831016821 + 1 = 301775790553168151048558228493050464 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 100591930184389383682852742831016821 + 3 = 502959650921946918414263714155084108 from by ring, show 3 + 2 = 5 from by ring,
      show 12 * 100591930184389383682852742831016821 + 8 = 1207103162212672604194232913972201860 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2011838603687787673657054856620336436) (c₂ := ⟨0, 0, 0, 838266084869911530690439523591806848, 6⟩)
  · have h := mod1_sn 167653216973982306138087904718361369 4
    rw [show 3 * 167653216973982306138087904718361369 + 1 = 502959650921946918414263714155084108 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 167653216973982306138087904718361369 + 3 = 838266084869911530690439523591806848 from by ring, show 4 + 2 = 6 from by ring,
      show 12 * 167653216973982306138087904718361369 + 8 = 2011838603687787673657054856620336436 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 3353064339479646122761758094367227395) (c₂ := ⟨0, 0, 0, 1397110141449852551150732539319678081, 6⟩)
  · have h := mod0_sn 279422028289970510230146507863935616 5
    rw [show 3 * 279422028289970510230146507863935616 = 838266084869911530690439523591806848 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 279422028289970510230146507863935616 + 1 = 1397110141449852551150732539319678081 from by ring, show 12 * 279422028289970510230146507863935616 + 3 = 3353064339479646122761758094367227395 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 5588440565799410204602930157278712326) (c₂ := ⟨0, 0, 0, 2328516902416420918584554232199463469, 5⟩)
  · have h := mod2_sn 465703380483284183716910846439892693 5
    rw [show 3 * 465703380483284183716910846439892693 + 2 = 1397110141449852551150732539319678081 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 465703380483284183716910846439892693 + 4 = 2328516902416420918584554232199463469 from by ring, show 12 * 465703380483284183716910846439892693 + 10 = 5588440565799410204602930157278712326 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 9314067609665683674338216928797853879) (c₂ := ⟨0, 0, 0, 3880861504027368197640923720332439116, 5⟩)
  · have h := mod0_sn 776172300805473639528184744066487823 4
    rw [show 3 * 776172300805473639528184744066487823 = 2328516902416420918584554232199463469 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 776172300805473639528184744066487823 + 1 = 3880861504027368197640923720332439116 from by ring, show 12 * 776172300805473639528184744066487823 + 3 = 9314067609665683674338216928797853879 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 15523446016109472790563694881329756468) (c₂ := ⟨0, 0, 0, 6468102506712280329401539533887398528, 6⟩)
  · have h := mod1_sn 1293620501342456065880307906777479705 4
    rw [show 3 * 1293620501342456065880307906777479705 + 1 = 3880861504027368197640923720332439116 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 1293620501342456065880307906777479705 + 3 = 6468102506712280329401539533887398528 from by ring, show 4 + 2 = 6 from by ring,
      show 12 * 1293620501342456065880307906777479705 + 8 = 15523446016109472790563694881329756468 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 25872410026849121317606158135549594116) (c₂ := ⟨0, 0, 0, 10780170844520467215669232556478997548, 7⟩)
  · have h := mod1_sn 2156034168904093443133846511295799509 5
    rw [show 3 * 2156034168904093443133846511295799509 + 1 = 6468102506712280329401539533887398528 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 2156034168904093443133846511295799509 + 3 = 10780170844520467215669232556478997548 from by ring, show 5 + 2 = 7 from by ring,
      show 12 * 2156034168904093443133846511295799509 + 8 = 25872410026849121317606158135549594116 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 43120683378081868862676930225915990195) (c₂ := ⟨0, 0, 0, 17966951407534112026115387594131662581, 7⟩)
  · have h := mod0_sn 3593390281506822405223077518826332516 6
    rw [show 3 * 3593390281506822405223077518826332516 = 10780170844520467215669232556478997548 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 3593390281506822405223077518826332516 + 1 = 17966951407534112026115387594131662581 from by ring, show 12 * 3593390281506822405223077518826332516 + 3 = 43120683378081868862676930225915990195 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 71867805630136448104461550376526650326) (c₂ := ⟨0, 0, 0, 29944919012556853376858979323552770969, 6⟩)
  · have h := mod2_sn 5988983802511370675371795864710554193 6
    rw [show 3 * 5988983802511370675371795864710554193 + 2 = 17966951407534112026115387594131662581 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 5988983802511370675371795864710554193 + 4 = 29944919012556853376858979323552770969 from by ring, show 12 * 5988983802511370675371795864710554193 + 10 = 71867805630136448104461550376526650326 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 119779676050227413507435917294211083880) (c₂ := ⟨0, 0, 0, 49908198354261422294764965539254618283, 7⟩)
  · have h := mod1_sn 9981639670852284458952993107850923656 5
    rw [show 3 * 9981639670852284458952993107850923656 + 1 = 29944919012556853376858979323552770969 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 9981639670852284458952993107850923656 + 3 = 49908198354261422294764965539254618283 from by ring, show 5 + 2 = 7 from by ring,
      show 12 * 9981639670852284458952993107850923656 + 8 = 119779676050227413507435917294211083880 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 199632793417045689179059862157018473134) (c₂ := ⟨0, 0, 0, 83180330590435703824608275898757697139, 6⟩)
  · have h := mod2_sn 16636066118087140764921655179751539427 6
    rw [show 3 * 16636066118087140764921655179751539427 + 2 = 49908198354261422294764965539254618283 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 16636066118087140764921655179751539427 + 4 = 83180330590435703824608275898757697139 from by ring, show 12 * 16636066118087140764921655179751539427 + 10 = 199632793417045689179059862157018473134 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 332721322361742815298433103595030788559) (c₂ := ⟨0, 0, 0, 138633884317392839707680459831262828566, 6⟩)
  · have h := mod0_sn 27726776863478567941536091966252565713 5
    rw [show 3 * 27726776863478567941536091966252565713 = 83180330590435703824608275898757697139 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 27726776863478567941536091966252565713 + 1 = 138633884317392839707680459831262828566 from by ring, show 12 * 27726776863478567941536091966252565713 + 3 = 332721322361742815298433103595030788559 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 554535537269571358830721839325051314267) (c₂ := ⟨0, 0, 0, 231056473862321399512800766385438047611, 6⟩)
  · have h := mod0_sn 46211294772464279902560153277087609522 5
    rw [show 3 * 46211294772464279902560153277087609522 = 138633884317392839707680459831262828566 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 46211294772464279902560153277087609522 + 1 = 231056473862321399512800766385438047611 from by ring, show 12 * 46211294772464279902560153277087609522 + 3 = 554535537269571358830721839325051314267 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 924225895449285598051203065541752190447) (c₂ := ⟨0, 0, 0, 385094123103868999188001277309063412686, 6⟩)
  · have h := mod0_sn 77018824620773799837600255461812682537 5
    rw [show 3 * 77018824620773799837600255461812682537 = 231056473862321399512800766385438047611 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 77018824620773799837600255461812682537 + 1 = 385094123103868999188001277309063412686 from by ring, show 12 * 77018824620773799837600255461812682537 + 3 = 924225895449285598051203065541752190447 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1540376492415475996752005109236253650746) (c₂ := ⟨0, 0, 0, 641823538506448331980002128848439021144, 5⟩)
  · have h := mod2_sn 128364707701289666396000425769687804228 5
    rw [show 3 * 128364707701289666396000425769687804228 + 2 = 385094123103868999188001277309063412686 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 128364707701289666396000425769687804228 + 4 = 641823538506448331980002128848439021144 from by ring, show 12 * 128364707701289666396000425769687804228 + 10 = 1540376492415475996752005109236253650746 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2567294154025793327920008515393756084578) (c₂ := ⟨0, 0, 0, 1069705897510747219966670214747398368574, 4⟩)
  · have h := mod2_sn 213941179502149443993334042949479673714 4
    rw [show 3 * 213941179502149443993334042949479673714 + 2 = 641823538506448331980002128848439021144 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 213941179502149443993334042949479673714 + 4 = 1069705897510747219966670214747398368574 from by ring, show 12 * 213941179502149443993334042949479673714 + 10 = 2567294154025793327920008515393756084578 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 4278823590042988879866680858989593474298) (c₂ := ⟨0, 0, 0, 1782843162517912033277783691245663947624, 3⟩)
  · have h := mod2_sn 356568632503582406655556738249132789524 3
    rw [show 3 * 356568632503582406655556738249132789524 + 2 = 1069705897510747219966670214747398368574 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 356568632503582406655556738249132789524 + 4 = 1782843162517912033277783691245663947624 from by ring, show 12 * 356568632503582406655556738249132789524 + 10 = 4278823590042988879866680858989593474298 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 7131372650071648133111134764982655790500) (c₂ := ⟨0, 0, 0, 2971405270863186722129639485409439912708, 4⟩)
  · have h := mod1_sn 594281054172637344425927897081887982541 2
    rw [show 3 * 594281054172637344425927897081887982541 + 1 = 1782843162517912033277783691245663947624 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 594281054172637344425927897081887982541 + 3 = 2971405270863186722129639485409439912708 from by ring, show 2 + 2 = 4 from by ring,
      show 12 * 594281054172637344425927897081887982541 + 8 = 7131372650071648133111134764982655790500 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 11885621083452746888518557941637759650835) (c₂ := ⟨0, 0, 0, 4952342118105311203549399142349066521181, 4⟩)
  · have h := mod0_sn 990468423621062240709879828469813304236 3
    rw [show 3 * 990468423621062240709879828469813304236 = 2971405270863186722129639485409439912708 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 990468423621062240709879828469813304236 + 1 = 4952342118105311203549399142349066521181 from by ring, show 12 * 990468423621062240709879828469813304236 + 3 = 11885621083452746888518557941637759650835 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 19809368472421244814197596569396266084727) (c₂ := ⟨0, 0, 0, 8253903530175518672582331903915110868636, 4⟩)
  · have h := mod0_sn 1650780706035103734516466380783022173727 3
    rw [show 3 * 1650780706035103734516466380783022173727 = 4952342118105311203549399142349066521181 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 1650780706035103734516466380783022173727 + 1 = 8253903530175518672582331903915110868636 from by ring, show 12 * 1650780706035103734516466380783022173727 + 3 = 19809368472421244814197596569396266084727 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 33015614120702074690329327615660443474547) (c₂ := ⟨0, 0, 0, 13756505883625864454303886506525184781061, 4⟩)
  · have h := mod0_sn 2751301176725172890860777301305036956212 3
    rw [show 3 * 2751301176725172890860777301305036956212 = 8253903530175518672582331903915110868636 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 2751301176725172890860777301305036956212 + 1 = 13756505883625864454303886506525184781061 from by ring, show 12 * 2751301176725172890860777301305036956212 + 3 = 33015614120702074690329327615660443474547 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 55026023534503457817215546026100739124246) (c₂ := ⟨0, 0, 0, 22927509806043107423839810844208641301769, 3⟩)
  · have h := mod2_sn 4585501961208621484767962168841728260353 3
    rw [show 3 * 4585501961208621484767962168841728260353 + 2 = 13756505883625864454303886506525184781061 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 4585501961208621484767962168841728260353 + 4 = 22927509806043107423839810844208641301769 from by ring, show 12 * 4585501961208621484767962168841728260353 + 10 = 55026023534503457817215546026100739124246 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 91710039224172429695359243376834565207080) (c₂ := ⟨0, 0, 0, 38212516343405179039733018073681068836283, 4⟩)
  · have h := mod1_sn 7642503268681035807946603614736213767256 2
    rw [show 3 * 7642503268681035807946603614736213767256 + 1 = 22927509806043107423839810844208641301769 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 7642503268681035807946603614736213767256 + 3 = 38212516343405179039733018073681068836283 from by ring, show 2 + 2 = 4 from by ring,
      show 12 * 7642503268681035807946603614736213767256 + 8 = 91710039224172429695359243376834565207080 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 152850065373620716158932072294724275345134) (c₂ := ⟨0, 0, 0, 63687527239008631732888363456135114727139, 3⟩)
  · have h := mod2_sn 12737505447801726346577672691227022945427 3
    rw [show 3 * 12737505447801726346577672691227022945427 + 2 = 38212516343405179039733018073681068836283 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 12737505447801726346577672691227022945427 + 4 = 63687527239008631732888363456135114727139 from by ring, show 12 * 12737505447801726346577672691227022945427 + 10 = 152850065373620716158932072294724275345134 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 254750108956034526931553453824540458908559) (c₂ := ⟨0, 0, 0, 106145878731681052888147272426891857878566, 3⟩)
  · have h := mod0_sn 21229175746336210577629454485378371575713 2
    rw [show 3 * 21229175746336210577629454485378371575713 = 63687527239008631732888363456135114727139 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 21229175746336210577629454485378371575713 + 1 = 106145878731681052888147272426891857878566 from by ring, show 12 * 21229175746336210577629454485378371575713 + 3 = 254750108956034526931553453824540458908559 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 424583514926724211552589089707567431514267) (c₂ := ⟨0, 0, 0, 176909797886135088146912120711486429797611, 3⟩)
  · have h := mod0_sn 35381959577227017629382424142297285959522 2
    rw [show 3 * 35381959577227017629382424142297285959522 = 106145878731681052888147272426891857878566 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 35381959577227017629382424142297285959522 + 1 = 176909797886135088146912120711486429797611 from by ring, show 12 * 35381959577227017629382424142297285959522 + 3 = 424583514926724211552589089707567431514267 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 707639191544540352587648482845945719190447) (c₂ := ⟨0, 0, 0, 294849663143558480244853534519144049662686, 3⟩)
  · have h := mod0_sn 58969932628711696048970706903828809932537 2
    rw [show 3 * 58969932628711696048970706903828809932537 = 176909797886135088146912120711486429797611 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 58969932628711696048970706903828809932537 + 1 = 294849663143558480244853534519144049662686 from by ring, show 12 * 58969932628711696048970706903828809932537 + 3 = 707639191544540352587648482845945719190447 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1179398652574233920979414138076576198650747) (c₂ := ⟨0, 0, 0, 491416105239264133741422557531906749437811, 3⟩)
  · have h := mod0_sn 98283221047852826748284511506381349887562 2
    rw [show 3 * 98283221047852826748284511506381349887562 = 294849663143558480244853534519144049662686 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 98283221047852826748284511506381349887562 + 1 = 491416105239264133741422557531906749437811 from by ring, show 12 * 98283221047852826748284511506381349887562 + 3 = 1179398652574233920979414138076576198650747 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1965664420957056534965690230127626997751248) (c₂ := ⟨0, 0, 0, 819026842065440222902370929219844582396353, 4⟩)
  · have h := mod1_sn 163805368413088044580474185843968916479270 2
    rw [show 3 * 163805368413088044580474185843968916479270 + 1 = 491416105239264133741422557531906749437811 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 163805368413088044580474185843968916479270 + 3 = 819026842065440222902370929219844582396353 from by ring, show 2 + 2 = 4 from by ring,
      show 12 * 163805368413088044580474185843968916479270 + 8 = 1965664420957056534965690230127626997751248 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 3276107368261760891609483716879378329585416) (c₂ := ⟨0, 0, 0, 1365044736775733704837284882033074303993923, 5⟩)
  · have h := mod1_sn 273008947355146740967456976406614860798784 3
    rw [show 3 * 273008947355146740967456976406614860798784 + 1 = 819026842065440222902370929219844582396353 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 273008947355146740967456976406614860798784 + 3 = 1365044736775733704837284882033074303993923 from by ring, show 3 + 2 = 5 from by ring,
      show 12 * 273008947355146740967456976406614860798784 + 8 = 3276107368261760891609483716879378329585416 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 5460178947102934819349139528132297215975696) (c₂ := ⟨0, 0, 0, 2275074561292889508062141470055123839989873, 6⟩)
  · have h := mod1_sn 455014912258577901612428294011024767997974 4
    rw [show 3 * 455014912258577901612428294011024767997974 + 1 = 1365044736775733704837284882033074303993923 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 455014912258577901612428294011024767997974 + 3 = 2275074561292889508062141470055123839989873 from by ring, show 4 + 2 = 6 from by ring,
      show 12 * 455014912258577901612428294011024767997974 + 8 = 5460178947102934819349139528132297215975696 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 9100298245171558032248565880220495359959495) (c₂ := ⟨0, 0, 0, 3791790935488149180103569116758539733316456, 6⟩)
  · have h := mod0_sn 758358187097629836020713823351707946663291 5
    rw [show 3 * 758358187097629836020713823351707946663291 = 2275074561292889508062141470055123839989873 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 758358187097629836020713823351707946663291 + 1 = 3791790935488149180103569116758539733316456 from by ring, show 12 * 758358187097629836020713823351707946663291 + 3 = 9100298245171558032248565880220495359959495 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 15167163741952596720414276467034158933265826) (c₂ := ⟨0, 0, 0, 6319651559146915300172615194597566222194094, 5⟩)
  · have h := mod2_sn 1263930311829383060034523038919513244438818 5
    rw [show 3 * 1263930311829383060034523038919513244438818 + 2 = 3791790935488149180103569116758539733316456 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 1263930311829383060034523038919513244438818 + 4 = 6319651559146915300172615194597566222194094 from by ring, show 12 * 1263930311829383060034523038919513244438818 + 10 = 15167163741952596720414276467034158933265826 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 25278606236587661200690460778390264888776379) (c₂ := ⟨0, 0, 0, 10532752598578192166954358657662610370323491, 5⟩)
  · have h := mod0_sn 2106550519715638433390871731532522074064698 4
    rw [show 3 * 2106550519715638433390871731532522074064698 = 6319651559146915300172615194597566222194094 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 2106550519715638433390871731532522074064698 + 1 = 10532752598578192166954358657662610370323491 from by ring, show 12 * 2106550519715638433390871731532522074064698 + 3 = 25278606236587661200690460778390264888776379 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 42131010394312768667817434630650441481293966) (c₂ := ⟨0, 0, 0, 17554587664296986944923931096104350617205819, 4⟩)
  · have h := mod2_sn 3510917532859397388984786219220870123441163 4
    rw [show 3 * 3510917532859397388984786219220870123441163 + 2 = 10532752598578192166954358657662610370323491 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 3510917532859397388984786219220870123441163 + 4 = 17554587664296986944923931096104350617205819 from by ring, show 12 * 3510917532859397388984786219220870123441163 + 10 = 42131010394312768667817434630650441481293966 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 70218350657187947779695724384417402468823278) (c₂ := ⟨0, 0, 0, 29257646107161644908206551826840584362009699, 3⟩)
  · have h := mod2_sn 5851529221432328981641310365368116872401939 3
    rw [show 3 * 5851529221432328981641310365368116872401939 + 2 = 17554587664296986944923931096104350617205819 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 5851529221432328981641310365368116872401939 + 4 = 29257646107161644908206551826840584362009699 from by ring, show 12 * 5851529221432328981641310365368116872401939 + 10 = 70218350657187947779695724384417402468823278 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 117030584428646579632826207307362337448038800) (c₂ := ⟨0, 0, 0, 48762743511936074847010919711400973936682833, 4⟩)
  · have h := mod1_sn 9752548702387214969402183942280194787336566 2
    rw [show 3 * 9752548702387214969402183942280194787336566 + 1 = 29257646107161644908206551826840584362009699 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 9752548702387214969402183942280194787336566 + 3 = 48762743511936074847010919711400973936682833 from by ring, show 2 + 2 = 4 from by ring,
      show 12 * 9752548702387214969402183942280194787336566 + 8 = 117030584428646579632826207307362337448038800 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 195050974047744299388043678845603895746731336) (c₂ := ⟨0, 0, 0, 81271239186560124745018199519001623227804723, 5⟩)
  · have h := mod1_sn 16254247837312024949003639903800324645560944 3
    rw [show 3 * 16254247837312024949003639903800324645560944 + 1 = 48762743511936074847010919711400973936682833 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 16254247837312024949003639903800324645560944 + 3 = 81271239186560124745018199519001623227804723 from by ring, show 3 + 2 = 5 from by ring,
      show 12 * 16254247837312024949003639903800324645560944 + 8 = 195050974047744299388043678845603895746731336 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 325084956746240498980072798076006492911218896) (c₂ := ⟨0, 0, 0, 135452065310933541241696999198336038713007873, 6⟩)
  · have h := mod1_sn 27090413062186708248339399839667207742601574 4
    rw [show 3 * 27090413062186708248339399839667207742601574 + 1 = 81271239186560124745018199519001623227804723 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 27090413062186708248339399839667207742601574 + 3 = 135452065310933541241696999198336038713007873 from by ring, show 4 + 2 = 6 from by ring,
      show 12 * 27090413062186708248339399839667207742601574 + 8 = 325084956746240498980072798076006492911218896 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 541808261243734164966787996793344154852031495) (c₂ := ⟨0, 0, 0, 225753442184889235402828331997226731188346456, 6⟩)
  · have h := mod0_sn 45150688436977847080565666399445346237669291 5
    rw [show 3 * 45150688436977847080565666399445346237669291 = 135452065310933541241696999198336038713007873 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 45150688436977847080565666399445346237669291 + 1 = 225753442184889235402828331997226731188346456 from by ring, show 12 * 45150688436977847080565666399445346237669291 + 3 = 541808261243734164966787996793344154852031495 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 903013768739556941611313327988906924753385827) (c₂ := ⟨0, 0, 0, 376255736974815392338047219995377885313910761, 6⟩)
  · have h := mod0_sn 75251147394963078467609443999075577062782152 5
    rw [show 3 * 75251147394963078467609443999075577062782152 = 225753442184889235402828331997226731188346456 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 75251147394963078467609443999075577062782152 + 1 = 376255736974815392338047219995377885313910761 from by ring, show 12 * 75251147394963078467609443999075577062782152 + 3 = 903013768739556941611313327988906924753385827 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1505022947899261569352188879981511541255643046) (c₂ := ⟨0, 0, 0, 627092894958025653896745366658963142189851269, 5⟩)
  · have h := mod2_sn 125418578991605130779349073331792628437970253 5
    rw [show 3 * 125418578991605130779349073331792628437970253 + 2 = 376255736974815392338047219995377885313910761 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 125418578991605130779349073331792628437970253 + 4 = 627092894958025653896745366658963142189851269 from by ring, show 12 * 125418578991605130779349073331792628437970253 + 10 = 1505022947899261569352188879981511541255643046 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2508371579832102615586981466635852568759405079) (c₂ := ⟨0, 0, 0, 1045154824930042756494575611098271903649752116, 5⟩)
  · have h := mod0_sn 209030964986008551298915122219654380729950423 4
    rw [show 3 * 209030964986008551298915122219654380729950423 = 627092894958025653896745366658963142189851269 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 209030964986008551298915122219654380729950423 + 1 = 1045154824930042756494575611098271903649752116 from by ring, show 12 * 209030964986008551298915122219654380729950423 + 3 = 2508371579832102615586981466635852568759405079 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 4180619299720171025978302444393087614599008467) (c₂ := ⟨0, 0, 0, 1741924708216737927490959351830453172749586861, 5⟩)
  · have h := mod0_sn 348384941643347585498191870366090634549917372 4
    rw [show 3 * 348384941643347585498191870366090634549917372 = 1045154824930042756494575611098271903649752116 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 348384941643347585498191870366090634549917372 + 1 = 1741924708216737927490959351830453172749586861 from by ring, show 12 * 348384941643347585498191870366090634549917372 + 3 = 4180619299720171025978302444393087614599008467 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 6967698832866951709963837407321812690998347447) (c₂ := ⟨0, 0, 0, 2903207847027896545818265586384088621249311436, 5⟩)
  · have h := mod0_sn 580641569405579309163653117276817724249862287 4
    rw [show 3 * 580641569405579309163653117276817724249862287 = 1741924708216737927490959351830453172749586861 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 580641569405579309163653117276817724249862287 + 1 = 2903207847027896545818265586384088621249311436 from by ring, show 12 * 580641569405579309163653117276817724249862287 + 3 = 6967698832866951709963837407321812690998347447 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 11612831388111586183273062345536354484997245747) (c₂ := ⟨0, 0, 0, 4838679745046494243030442643973481035415519061, 5⟩)
  · have h := mod0_sn 967735949009298848606088528794696207083103812 4
    rw [show 3 * 967735949009298848606088528794696207083103812 = 2903207847027896545818265586384088621249311436 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 967735949009298848606088528794696207083103812 + 1 = 4838679745046494243030442643973481035415519061 from by ring, show 12 * 967735949009298848606088528794696207083103812 + 3 = 11612831388111586183273062345536354484997245747 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 19354718980185976972121770575893924141662076247) (c₂ := ⟨0, 0, 0, 8064466241744157071717404406622468392359198436, 5⟩)
  · have h := mod0_sn 1612893248348831414343480881324493678471839687 4
    rw [show 3 * 1612893248348831414343480881324493678471839687 = 4838679745046494243030442643973481035415519061 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 1612893248348831414343480881324493678471839687 + 1 = 8064466241744157071717404406622468392359198436 from by ring, show 12 * 1612893248348831414343480881324493678471839687 + 3 = 19354718980185976972121770575893924141662076247 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 32257864966976628286869617626489873569436793746) (c₂ := ⟨0, 0, 0, 13440777069573595119529007344370780653931997394, 4⟩)
  · have h := mod2_sn 2688155413914719023905801468874156130786399478 4
    rw [show 3 * 2688155413914719023905801468874156130786399478 + 2 = 8064466241744157071717404406622468392359198436 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 2688155413914719023905801468874156130786399478 + 4 = 13440777069573595119529007344370780653931997394 from by ring, show 12 * 2688155413914719023905801468874156130786399478 + 10 = 32257864966976628286869617626489873569436793746 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 53763108278294380478116029377483122615727989580) (c₂ := ⟨0, 0, 0, 22401295115955991865881678907284634423219995658, 5⟩)
  · have h := mod1_sn 4480259023191198373176335781456926884643999131 3
    rw [show 3 * 4480259023191198373176335781456926884643999131 + 1 = 13440777069573595119529007344370780653931997394 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 4480259023191198373176335781456926884643999131 + 3 = 22401295115955991865881678907284634423219995658 from by ring, show 3 + 2 = 5 from by ring,
      show 12 * 4480259023191198373176335781456926884643999131 + 8 = 53763108278294380478116029377483122615727989580 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 89605180463823967463526715629138537692879982634) (c₂ := ⟨0, 0, 0, 37335491859926653109802798178807724038699992764, 4⟩)
  · have h := mod2_sn 7467098371985330621960559635761544807739998552 4
    rw [show 3 * 7467098371985330621960559635761544807739998552 + 2 = 22401295115955991865881678907284634423219995658 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 7467098371985330621960559635761544807739998552 + 4 = 37335491859926653109802798178807724038699992764 from by ring, show 12 * 7467098371985330621960559635761544807739998552 + 10 = 89605180463823967463526715629138537692879982634 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 149341967439706612439211192715230896154799971058) (c₂ := ⟨0, 0, 0, 62225819766544421849671330298012873397833321274, 3⟩)
  · have h := mod2_sn 12445163953308884369934266059602574679566664254 3
    rw [show 3 * 12445163953308884369934266059602574679566664254 + 2 = 37335491859926653109802798178807724038699992764 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 12445163953308884369934266059602574679566664254 + 4 = 62225819766544421849671330298012873397833321274 from by ring, show 12 * 12445163953308884369934266059602574679566664254 + 10 = 149341967439706612439211192715230896154799971058 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 248903279066177687398685321192051493591333285099) (c₂ := ⟨0, 0, 0, 103709699610907369749452217163354788996388868791, 3⟩)
  · have h := mod0_sn 20741939922181473949890443432670957799277773758 2
    rw [show 3 * 20741939922181473949890443432670957799277773758 = 62225819766544421849671330298012873397833321274 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 20741939922181473949890443432670957799277773758 + 1 = 103709699610907369749452217163354788996388868791 from by ring, show 12 * 20741939922181473949890443432670957799277773758 + 3 = 248903279066177687398685321192051493591333285099 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 414838798443629478997808868653419155985555475168) (c₂ := ⟨0, 0, 0, 172849499351512282915753695272257981660648114653, 4⟩)
  · have h := mod1_sn 34569899870302456583150739054451596332129622930 2
    rw [show 3 * 34569899870302456583150739054451596332129622930 + 1 = 103709699610907369749452217163354788996388868791 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 34569899870302456583150739054451596332129622930 + 3 = 172849499351512282915753695272257981660648114653 from by ring, show 2 + 2 = 4 from by ring,
      show 12 * 34569899870302456583150739054451596332129622930 + 8 = 414838798443629478997808868653419155985555475168 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 691397997406049131663014781089031926642592458615) (c₂ := ⟨0, 0, 0, 288082498919187138192922825453763302767746857756, 4⟩)
  · have h := mod0_sn 57616499783837427638584565090752660553549371551 3
    rw [show 3 * 57616499783837427638584565090752660553549371551 = 172849499351512282915753695272257981660648114653 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 57616499783837427638584565090752660553549371551 + 1 = 288082498919187138192922825453763302767746857756 from by ring, show 12 * 57616499783837427638584565090752660553549371551 + 3 = 691397997406049131663014781089031926642592458615 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1152329995676748552771691301815053211070987431028) (c₂ := ⟨0, 0, 0, 480137498198645230321538042422938837946244762928, 5⟩)
  · have h := mod1_sn 96027499639729046064307608484587767589248952585 3
    rw [show 3 * 96027499639729046064307608484587767589248952585 + 1 = 288082498919187138192922825453763302767746857756 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 96027499639729046064307608484587767589248952585 + 3 = 480137498198645230321538042422938837946244762928 from by ring, show 3 + 2 = 5 from by ring,
      show 12 * 96027499639729046064307608484587767589248952585 + 8 = 1152329995676748552771691301815053211070987431028 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1920549992794580921286152169691755351784979051715) (c₂ := ⟨0, 0, 0, 800229163664408717202563404038231396577074604881, 5⟩)
  · have h := mod0_sn 160045832732881743440512680807646279315414920976 4
    rw [show 3 * 160045832732881743440512680807646279315414920976 = 480137498198645230321538042422938837946244762928 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 160045832732881743440512680807646279315414920976 + 1 = 800229163664408717202563404038231396577074604881 from by ring, show 12 * 160045832732881743440512680807646279315414920976 + 3 = 1920549992794580921286152169691755351784979051715 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 3200916654657634868810253616152925586308298419527) (c₂ := ⟨0, 0, 0, 1333715272774014528670939006730385660961791008136, 5⟩)
  · have h := mod0_sn 266743054554802905734187801346077132192358201627 4
    rw [show 3 * 266743054554802905734187801346077132192358201627 = 800229163664408717202563404038231396577074604881 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 266743054554802905734187801346077132192358201627 + 1 = 1333715272774014528670939006730385660961791008136 from by ring, show 12 * 266743054554802905734187801346077132192358201627 + 3 = 3200916654657634868810253616152925586308298419527 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 5334861091096058114683756026921542643847164032547) (c₂ := ⟨0, 0, 0, 2222858787956690881118231677883976101602985013561, 5⟩)
  · have h := mod0_sn 444571757591338176223646335576795220320597002712 4
    rw [show 3 * 444571757591338176223646335576795220320597002712 = 1333715272774014528670939006730385660961791008136 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 444571757591338176223646335576795220320597002712 + 1 = 2222858787956690881118231677883976101602985013561 from by ring, show 12 * 444571757591338176223646335576795220320597002712 + 3 = 5334861091096058114683756026921542643847164032547 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 8891435151826763524472926711535904406411940054247) (c₂ := ⟨0, 0, 0, 3704764646594484801863719463139960169338308355936, 5⟩)
  · have h := mod0_sn 740952929318896960372743892627992033867661671187 4
    rw [show 3 * 740952929318896960372743892627992033867661671187 = 2222858787956690881118231677883976101602985013561 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 740952929318896960372743892627992033867661671187 + 1 = 3704764646594484801863719463139960169338308355936 from by ring, show 12 * 740952929318896960372743892627992033867661671187 + 3 = 8891435151826763524472926711535904406411940054247 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 14819058586377939207454877852559840677353233423747) (c₂ := ⟨0, 0, 0, 6174607744324141336439532438566600282230513926561, 5⟩)
  · have h := mod0_sn 1234921548864828267287906487713320056446102785312 4
    rw [show 3 * 1234921548864828267287906487713320056446102785312 = 3704764646594484801863719463139960169338308355936 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 1234921548864828267287906487713320056446102785312 + 1 = 6174607744324141336439532438566600282230513926561 from by ring, show 12 * 1234921548864828267287906487713320056446102785312 + 3 = 14819058586377939207454877852559840677353233423747 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 24698430977296565345758129754266401128922055706247) (c₂ := ⟨0, 0, 0, 10291012907206902227399220730944333803717523210936, 5⟩)
  · have h := mod0_sn 2058202581441380445479844146188866760743504642187 4
    rw [show 3 * 2058202581441380445479844146188866760743504642187 = 6174607744324141336439532438566600282230513926561 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 2058202581441380445479844146188866760743504642187 + 1 = 10291012907206902227399220730944333803717523210936 from by ring, show 12 * 2058202581441380445479844146188866760743504642187 + 3 = 24698430977296565345758129754266401128922055706247 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 41164051628827608909596882923777335214870092843747) (c₂ := ⟨0, 0, 0, 17151688178678170378998701218240556339529205351561, 5⟩)
  · have h := mod0_sn 3430337635735634075799740243648111267905841070312 4
    rw [show 3 * 3430337635735634075799740243648111267905841070312 = 10291012907206902227399220730944333803717523210936 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 3430337635735634075799740243648111267905841070312 + 1 = 17151688178678170378998701218240556339529205351561 from by ring, show 12 * 3430337635735634075799740243648111267905841070312 + 3 = 41164051628827608909596882923777335214870092843747 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 68606752714712681515994804872962225358116821406248) (c₂ := ⟨0, 0, 0, 28586146964463617298331168697067593899215342252603, 6⟩)
  · have h := mod1_sn 5717229392892723459666233739413518779843068450520 4
    rw [show 3 * 5717229392892723459666233739413518779843068450520 + 1 = 17151688178678170378998701218240556339529205351561 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 5717229392892723459666233739413518779843068450520 + 3 = 28586146964463617298331168697067593899215342252603 from by ring, show 4 + 2 = 6 from by ring,
      show 12 * 5717229392892723459666233739413518779843068450520 + 8 = 68606752714712681515994804872962225358116821406248 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 114344587857854469193324674788270375596861369010415) (c₂ := ⟨0, 0, 0, 47643578274106028830551947828445989832025570421006, 6⟩)
  · have h := mod0_sn 9528715654821205766110389565689197966405114084201 5
    rw [show 3 * 9528715654821205766110389565689197966405114084201 = 28586146964463617298331168697067593899215342252603 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 9528715654821205766110389565689197966405114084201 + 1 = 47643578274106028830551947828445989832025570421006 from by ring, show 12 * 9528715654821205766110389565689197966405114084201 + 3 = 114344587857854469193324674788270375596861369010415 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 190574313096424115322207791313783959328102281684026) (c₂ := ⟨0, 0, 0, 79405963790176714717586579714076649720042617368344, 5⟩)
  · have h := mod2_sn 15881192758035342943517315942815329944008523473668 5
    rw [show 3 * 15881192758035342943517315942815329944008523473668 + 2 = 47643578274106028830551947828445989832025570421006 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 15881192758035342943517315942815329944008523473668 + 4 = 79405963790176714717586579714076649720042617368344 from by ring, show 12 * 15881192758035342943517315942815329944008523473668 + 10 = 190574313096424115322207791313783959328102281684026 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 317623855160706858870346318856306598880170469473380) (c₂ := ⟨0, 0, 0, 132343272983627857862644299523461082866737695613908, 6⟩)
  · have h := mod1_sn 26468654596725571572528859904692216573347539122781 4
    rw [show 3 * 26468654596725571572528859904692216573347539122781 + 1 = 79405963790176714717586579714076649720042617368344 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 26468654596725571572528859904692216573347539122781 + 3 = 132343272983627857862644299523461082866737695613908 from by ring, show 4 + 2 = 6 from by ring,
      show 12 * 26468654596725571572528859904692216573347539122781 + 8 = 317623855160706858870346318856306598880170469473380 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 529373091934511431450577198093844331466950782455636) (c₂ := ⟨0, 0, 0, 220572121639379763104407165872435138111229492689848, 7⟩)
  · have h := mod1_sn 44114424327875952620881433174487027622245898537969 5
    rw [show 3 * 44114424327875952620881433174487027622245898537969 + 1 = 132343272983627857862644299523461082866737695613908 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 44114424327875952620881433174487027622245898537969 + 3 = 220572121639379763104407165872435138111229492689848 from by ring, show 5 + 2 = 7 from by ring,
      show 12 * 44114424327875952620881433174487027622245898537969 + 8 = 529373091934511431450577198093844331466950782455636 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 882288486557519052417628663489740552444917970759394) (c₂ := ⟨0, 0, 0, 367620202732299605174011943120725230185382487816414, 6⟩)
  · have h := mod2_sn 73524040546459921034802388624145046037076497563282 6
    rw [show 3 * 73524040546459921034802388624145046037076497563282 + 2 = 220572121639379763104407165872435138111229492689848 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 73524040546459921034802388624145046037076497563282 + 4 = 367620202732299605174011943120725230185382487816414 from by ring, show 12 * 73524040546459921034802388624145046037076497563282 + 10 = 882288486557519052417628663489740552444917970759394 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1470480810929198420696047772482900920741529951265660) (c₂ := ⟨0, 0, 0, 612700337887166008623353238534542050308970813027358, 7⟩)
  · have h := mod1_sn 122540067577433201724670647706908410061794162605471 5
    rw [show 3 * 122540067577433201724670647706908410061794162605471 + 1 = 367620202732299605174011943120725230185382487816414 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 122540067577433201724670647706908410061794162605471 + 3 = 612700337887166008623353238534542050308970813027358 from by ring, show 5 + 2 = 7 from by ring,
      show 12 * 122540067577433201724670647706908410061794162605471 + 8 = 1470480810929198420696047772482900920741529951265660 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2450801351548664034493412954138168201235883252109434) (c₂ := ⟨0, 0, 0, 1021167229811943347705588730890903417181618021712264, 6⟩)
  · have h := mod2_sn 204233445962388669541117746178180683436323604342452 6
    rw [show 3 * 204233445962388669541117746178180683436323604342452 + 2 = 612700337887166008623353238534542050308970813027358 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 204233445962388669541117746178180683436323604342452 + 4 = 1021167229811943347705588730890903417181618021712264 from by ring, show 12 * 204233445962388669541117746178180683436323604342452 + 10 = 2450801351548664034493412954138168201235883252109434 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 4084668919247773390822354923563613668726472086849060) (c₂ := ⟨0, 0, 0, 1701945383019905579509314551484839028636030036187108, 7⟩)
  · have h := mod1_sn 340389076603981115901862910296967805727206007237421 5
    rw [show 3 * 340389076603981115901862910296967805727206007237421 + 1 = 1021167229811943347705588730890903417181618021712264 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 340389076603981115901862910296967805727206007237421 + 3 = 1701945383019905579509314551484839028636030036187108 from by ring, show 5 + 2 = 7 from by ring,
      show 12 * 340389076603981115901862910296967805727206007237421 + 8 = 4084668919247773390822354923563613668726472086849060 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 6807781532079622318037258205939356114544120144748436) (c₂ := ⟨0, 0, 0, 2836575638366509299182190919141398381060050060311848, 8⟩)
  · have h := mod1_sn 567315127673301859836438183828279676212010012062369 6
    rw [show 3 * 567315127673301859836438183828279676212010012062369 + 1 = 1701945383019905579509314551484839028636030036187108 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 567315127673301859836438183828279676212010012062369 + 3 = 2836575638366509299182190919141398381060050060311848 from by ring, show 6 + 2 = 8 from by ring,
      show 12 * 567315127673301859836438183828279676212010012062369 + 8 = 6807781532079622318037258205939356114544120144748436 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 11346302553466037196728763676565593524240200241247395) (c₂ := ⟨0, 0, 0, 4727626063944182165303651531902330635100083433853081, 8⟩)
  · have h := mod0_sn 945525212788836433060730306380466127020016686770616 7
    rw [show 3 * 945525212788836433060730306380466127020016686770616 = 2836575638366509299182190919141398381060050060311848 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 945525212788836433060730306380466127020016686770616 + 1 = 4727626063944182165303651531902330635100083433853081 from by ring, show 12 * 945525212788836433060730306380466127020016686770616 + 3 = 11346302553466037196728763676565593524240200241247395 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 18910504255776728661214606127609322540400333735412326) (c₂ := ⟨0, 0, 0, 7879376773240303608839419219837217725166805723088469, 7⟩)
  · have h := mod2_sn 1575875354648060721767883843967443545033361144617693 7
    rw [show 3 * 1575875354648060721767883843967443545033361144617693 + 2 = 4727626063944182165303651531902330635100083433853081 from by ring, show 7 + 1 = 8 from by ring,
      show 5 * 1575875354648060721767883843967443545033361144617693 + 4 = 7879376773240303608839419219837217725166805723088469 from by ring, show 12 * 1575875354648060721767883843967443545033361144617693 + 10 = 18910504255776728661214606127609322540400333735412326 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 31517507092961214435357676879348870900667222892353878) (c₂ := ⟨0, 0, 0, 13132294622067172681399032033062029541944676205147449, 6⟩)
  · have h := mod2_sn 2626458924413434536279806406612405908388935241029489 6
    rw [show 3 * 2626458924413434536279806406612405908388935241029489 + 2 = 7879376773240303608839419219837217725166805723088469 from by ring, show 6 + 1 = 7 from by ring,
      show 5 * 2626458924413434536279806406612405908388935241029489 + 4 = 13132294622067172681399032033062029541944676205147449 from by ring, show 12 * 2626458924413434536279806406612405908388935241029489 + 10 = 31517507092961214435357676879348870900667222892353878 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 52529178488268690725596128132248118167778704820589798) (c₂ := ⟨0, 0, 0, 21887157703445287802331720055103382569907793675245749, 5⟩)
  · have h := mod2_sn 4377431540689057560466344011020676513981558735049149 5
    rw [show 3 * 4377431540689057560466344011020676513981558735049149 + 2 = 13132294622067172681399032033062029541944676205147449 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 4377431540689057560466344011020676513981558735049149 + 4 = 21887157703445287802331720055103382569907793675245749 from by ring, show 12 * 4377431540689057560466344011020676513981558735049149 + 10 = 52529178488268690725596128132248118167778704820589798 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 87548630813781151209326880220413530279631174700982998) (c₂ := ⟨0, 0, 0, 36478596172408813003886200091838970949846322792076249, 4⟩)
  · have h := mod2_sn 7295719234481762600777240018367794189969264558415249 4
    rw [show 3 * 7295719234481762600777240018367794189969264558415249 + 2 = 21887157703445287802331720055103382569907793675245749 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 7295719234481762600777240018367794189969264558415249 + 4 = 36478596172408813003886200091838970949846322792076249 from by ring, show 12 * 7295719234481762600777240018367794189969264558415249 + 10 = 87548630813781151209326880220413530279631174700982998 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 145914384689635252015544800367355883799385291168305000) (c₂ := ⟨0, 0, 0, 60797660287348021673143666819731618249743871320127083, 5⟩)
  · have h := mod1_sn 12159532057469604334628733363946323649948774264025416 3
    rw [show 3 * 12159532057469604334628733363946323649948774264025416 + 1 = 36478596172408813003886200091838970949846322792076249 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 12159532057469604334628733363946323649948774264025416 + 3 = 60797660287348021673143666819731618249743871320127083 from by ring, show 3 + 2 = 5 from by ring,
      show 12 * 12159532057469604334628733363946323649948774264025416 + 8 = 145914384689635252015544800367355883799385291168305000 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 243190641149392086692574667278926472998975485280508334) (c₂ := ⟨0, 0, 0, 101329433812246702788572778032886030416239785533545139, 4⟩)
  · have h := mod2_sn 20265886762449340557714555606577206083247957106709027 4
    rw [show 3 * 20265886762449340557714555606577206083247957106709027 + 2 = 60797660287348021673143666819731618249743871320127083 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 20265886762449340557714555606577206083247957106709027 + 4 = 101329433812246702788572778032886030416239785533545139 from by ring, show 12 * 20265886762449340557714555606577206083247957106709027 + 10 = 243190641149392086692574667278926472998975485280508334 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 405317735248986811154291112131544121664959142134180558) (c₂ := ⟨0, 0, 0, 168882389687077837980954630054810050693732975889241899, 3⟩)
  · have h := mod2_sn 33776477937415567596190926010962010138746595177848379 3
    rw [show 3 * 33776477937415567596190926010962010138746595177848379 + 2 = 101329433812246702788572778032886030416239785533545139 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 33776477937415567596190926010962010138746595177848379 + 4 = 168882389687077837980954630054810050693732975889241899 from by ring, show 12 * 33776477937415567596190926010962010138746595177848379 + 10 = 405317735248986811154291112131544121664959142134180558 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 675529558748311351923818520219240202774931903556967599) (c₂ := ⟨0, 0, 0, 281470649478463063301591050091350084489554959815403166, 3⟩)
  · have h := mod0_sn 56294129895692612660318210018270016897910991963080633 2
    rw [show 3 * 56294129895692612660318210018270016897910991963080633 = 168882389687077837980954630054810050693732975889241899 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 56294129895692612660318210018270016897910991963080633 + 1 = 281470649478463063301591050091350084489554959815403166 from by ring, show 12 * 56294129895692612660318210018270016897910991963080633 + 3 = 675529558748311351923818520219240202774931903556967599 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1125882597913852253206364200365400337958219839261612667) (c₂ := ⟨0, 0, 0, 469117749130771772169318416818916807482591599692338611, 3⟩)
  · have h := mod0_sn 93823549826154354433863683363783361496518319938467722 2
    rw [show 3 * 93823549826154354433863683363783361496518319938467722 = 281470649478463063301591050091350084489554959815403166 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 93823549826154354433863683363783361496518319938467722 + 1 = 469117749130771772169318416818916807482591599692338611 from by ring, show 12 * 93823549826154354433863683363783361496518319938467722 + 3 = 1125882597913852253206364200365400337958219839261612667 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1876470996523087088677273667275667229930366398769354447) (c₂ := ⟨0, 0, 0, 781862915217952953615530694698194679137652666153897686, 3⟩)
  · have h := mod0_sn 156372583043590590723106138939638935827530533230779537 2
    rw [show 3 * 156372583043590590723106138939638935827530533230779537 = 469117749130771772169318416818916807482591599692338611 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 156372583043590590723106138939638935827530533230779537 + 1 = 781862915217952953615530694698194679137652666153897686 from by ring, show 12 * 156372583043590590723106138939638935827530533230779537 + 3 = 1876470996523087088677273667275667229930366398769354447 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 3127451660871811814462122778792778716550610664615590748) (c₂ := ⟨0, 0, 0, 1303104858696588256025884491163657798562754443589829478, 4⟩)
  · have h := mod1_sn 260620971739317651205176898232731559712550888717965895 2
    rw [show 3 * 260620971739317651205176898232731559712550888717965895 + 1 = 781862915217952953615530694698194679137652666153897686 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 260620971739317651205176898232731559712550888717965895 + 3 = 1303104858696588256025884491163657798562754443589829478 from by ring, show 2 + 2 = 4 from by ring,
      show 12 * 260620971739317651205176898232731559712550888717965895 + 8 = 3127451660871811814462122778792778716550610664615590748 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 5212419434786353024103537964654631194251017774359317914) (c₂ := ⟨0, 0, 0, 2171841431160980426709807485272762997604590739316382464, 3⟩)
  · have h := mod2_sn 434368286232196085341961497054552599520918147863276492 3
    rw [show 3 * 434368286232196085341961497054552599520918147863276492 + 2 = 1303104858696588256025884491163657798562754443589829478 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 434368286232196085341961497054552599520918147863276492 + 4 = 2171841431160980426709807485272762997604590739316382464 from by ring, show 12 * 434368286232196085341961497054552599520918147863276492 + 10 = 5212419434786353024103537964654631194251017774359317914 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 8687365724643921706839229941091051990418362957265529860) (c₂ := ⟨0, 0, 0, 3619735718601634044516345808787938329340984565527304108, 4⟩)
  · have h := mod1_sn 723947143720326808903269161757587665868196913105460821 2
    rw [show 3 * 723947143720326808903269161757587665868196913105460821 + 1 = 2171841431160980426709807485272762997604590739316382464 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 723947143720326808903269161757587665868196913105460821 + 3 = 3619735718601634044516345808787938329340984565527304108 from by ring, show 2 + 2 = 4 from by ring,
      show 12 * 723947143720326808903269161757587665868196913105460821 + 8 = 8687365724643921706839229941091051990418362957265529860 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 14478942874406536178065383235151753317363938262109216434) (c₂ := ⟨0, 0, 0, 6032892864336056740860576347979897215568307609212173514, 3⟩)
  · have h := mod2_sn 1206578572867211348172115269595979443113661521842434702 3
    rw [show 3 * 1206578572867211348172115269595979443113661521842434702 + 2 = 3619735718601634044516345808787938329340984565527304108 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 1206578572867211348172115269595979443113661521842434702 + 4 = 6032892864336056740860576347979897215568307609212173514 from by ring, show 12 * 1206578572867211348172115269595979443113661521842434702 + 10 = 14478942874406536178065383235151753317363938262109216434 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 24131571457344226963442305391919588862273230436848694059) (c₂ := ⟨0, 0, 0, 10054821440560094568100960579966495359280512682020289191, 3⟩)
  · have h := mod0_sn 2010964288112018913620192115993299071856102536404057838 2
    rw [show 3 * 2010964288112018913620192115993299071856102536404057838 = 6032892864336056740860576347979897215568307609212173514 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 2010964288112018913620192115993299071856102536404057838 + 1 = 10054821440560094568100960579966495359280512682020289191 from by ring, show 12 * 2010964288112018913620192115993299071856102536404057838 + 3 = 24131571457344226963442305391919588862273230436848694059 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 40219285762240378272403842319865981437122050728081156767) (c₂ := ⟨0, 0, 0, 16758035734266824280168267633277492265467521136700481986, 3⟩)
  · have h := mod0_sn 3351607146853364856033653526655498453093504227340096397 2
    rw [show 3 * 3351607146853364856033653526655498453093504227340096397 = 10054821440560094568100960579966495359280512682020289191 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 3351607146853364856033653526655498453093504227340096397 + 1 = 16758035734266824280168267633277492265467521136700481986 from by ring, show 12 * 3351607146853364856033653526655498453093504227340096397 + 3 = 40219285762240378272403842319865981437122050728081156767 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 67032142937067297120673070533109969061870084546801927946) (c₂ := ⟨0, 0, 0, 27930059557111373800280446055462487109112535227834136644, 2⟩)
  · have h := mod2_sn 5586011911422274760056089211092497421822507045566827328 2
    rw [show 3 * 5586011911422274760056089211092497421822507045566827328 + 2 = 16758035734266824280168267633277492265467521136700481986 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 5586011911422274760056089211092497421822507045566827328 + 4 = 27930059557111373800280446055462487109112535227834136644 from by ring, show 12 * 5586011911422274760056089211092497421822507045566827328 + 10 = 67032142937067297120673070533109969061870084546801927946 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 111720238228445495201121784221849948436450140911336546578) (c₂ := ⟨0, 0, 0, 46550099261852289667134076759104145181854225379723561074, 1⟩)
  · have h := mod2_sn 9310019852370457933426815351820829036370845075944712214 1
    rw [show 3 * 9310019852370457933426815351820829036370845075944712214 + 2 = 27930059557111373800280446055462487109112535227834136644 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 9310019852370457933426815351820829036370845075944712214 + 4 = 46550099261852289667134076759104145181854225379723561074 from by ring, show 12 * 9310019852370457933426815351820829036370845075944712214 + 10 = 111720238228445495201121784221849948436450140911336546578 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 186200397047409158668536307036416580727416901518894244300) (c₂ := ⟨0, 0, 0, 77583498769753816111890127931840241969757042299539268458, 2⟩)
  · have h := mod1_sn 15516699753950763222378025586368048393951408459907853691 0
    rw [show 3 * 15516699753950763222378025586368048393951408459907853691 + 1 = 46550099261852289667134076759104145181854225379723561074 from by ring, show 0 + 1 = 1 from by ring,
      show 5 * 15516699753950763222378025586368048393951408459907853691 + 3 = 77583498769753816111890127931840241969757042299539268458 from by ring, show 0 + 2 = 2 from by ring,
      show 12 * 15516699753950763222378025586368048393951408459907853691 + 8 = 186200397047409158668536307036416580727416901518894244300 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 310333995079015264447560511727360967879028169198157073834) (c₂ := ⟨0, 0, 0, 129305831282923026853150213219733736616261737165898780764, 1⟩)
  · have h := mod2_sn 25861166256584605370630042643946747323252347433179756152 1
    rw [show 3 * 25861166256584605370630042643946747323252347433179756152 + 2 = 77583498769753816111890127931840241969757042299539268458 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 25861166256584605370630042643946747323252347433179756152 + 4 = 129305831282923026853150213219733736616261737165898780764 from by ring, show 12 * 25861166256584605370630042643946747323252347433179756152 + 10 = 310333995079015264447560511727360967879028169198157073834 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 517223325131692107412600852878934946465046948663595123059) (c₂ := ⟨0, 0, 0, 215509718804871711421917022032889561027102895276497967941, 1⟩)
  · have h := mod0_sn 43101943760974342284383404406577912205420579055299593588 0
    rw [show 3 * 43101943760974342284383404406577912205420579055299593588 = 129305831282923026853150213219733736616261737165898780764 from by ring, show 0 + 1 = 1 from by ring,
      show 5 * 43101943760974342284383404406577912205420579055299593588 + 1 = 215509718804871711421917022032889561027102895276497967941 from by ring, show 12 * 43101943760974342284383404406577912205420579055299593588 + 3 = 517223325131692107412600852878934946465046948663595123059 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 862038875219486845687668088131558244108411581105991871768) (c₂ := ⟨0, 0, 0, 359182864674786185703195036721482601711838158794163279903, 2⟩)
  · have h := mod1_sn 71836572934957237140639007344296520342367631758832655980 0
    rw [show 3 * 71836572934957237140639007344296520342367631758832655980 + 1 = 215509718804871711421917022032889561027102895276497967941 from by ring, show 0 + 1 = 1 from by ring,
      show 5 * 71836572934957237140639007344296520342367631758832655980 + 3 = 359182864674786185703195036721482601711838158794163279903 from by ring, show 0 + 2 = 2 from by ring,
      show 12 * 71836572934957237140639007344296520342367631758832655980 + 8 = 862038875219486845687668088131558244108411581105991871768 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1436731458699144742812780146885930406847352635176653119616) (c₂ := ⟨0, 0, 0, 598638107791310309505325061202471002853063597990272133173, 3⟩)
  · have h := mod1_sn 119727621558262061901065012240494200570612719598054426634 1
    rw [show 3 * 119727621558262061901065012240494200570612719598054426634 + 1 = 359182864674786185703195036721482601711838158794163279903 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 119727621558262061901065012240494200570612719598054426634 + 3 = 598638107791310309505325061202471002853063597990272133173 from by ring, show 1 + 2 = 3 from by ring,
      show 12 * 119727621558262061901065012240494200570612719598054426634 + 8 = 1436731458699144742812780146885930406847352635176653119616 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 2394552431165241238021300244809884011412254391961088532694) (c₂ := ⟨0, 0, 0, 997730179652183849175541768670785004755105996650453555289, 2⟩)
  · have h := mod2_sn 199546035930436769835108353734157000951021199330090711057 2
    rw [show 3 * 199546035930436769835108353734157000951021199330090711057 + 2 = 598638107791310309505325061202471002853063597990272133173 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 199546035930436769835108353734157000951021199330090711057 + 4 = 997730179652183849175541768670785004755105996650453555289 from by ring, show 12 * 199546035930436769835108353734157000951021199330090711057 + 10 = 2394552431165241238021300244809884011412254391961088532694 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 3990920718608735396702167074683140019020423986601814221160) (c₂ := ⟨0, 0, 0, 1662883632753639748625902947784641674591843327750755925483, 3⟩)
  · have h := mod1_sn 332576726550727949725180589556928334918368665550151185096 1
    rw [show 3 * 332576726550727949725180589556928334918368665550151185096 + 1 = 997730179652183849175541768670785004755105996650453555289 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 332576726550727949725180589556928334918368665550151185096 + 3 = 1662883632753639748625902947784641674591843327750755925483 from by ring, show 1 + 2 = 3 from by ring,
      show 12 * 332576726550727949725180589556928334918368665550151185096 + 8 = 3990920718608735396702167074683140019020423986601814221160 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 6651534531014558994503611791138566698367373311003023701934) (c₂ := ⟨0, 0, 0, 2771472721256066247709838246307736124319738879584593209139, 2⟩)
  · have h := mod2_sn 554294544251213249541967649261547224863947775916918641827 2
    rw [show 3 * 554294544251213249541967649261547224863947775916918641827 + 2 = 1662883632753639748625902947784641674591843327750755925483 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 554294544251213249541967649261547224863947775916918641827 + 4 = 2771472721256066247709838246307736124319738879584593209139 from by ring, show 12 * 554294544251213249541967649261547224863947775916918641827 + 10 = 6651534531014558994503611791138566698367373311003023701934 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 11085890885024264990839352985230944497278955518338372836560) (c₂ := ⟨0, 0, 0, 4619121202093443746183063743846226873866231465974322015233, 3⟩)
  · have h := mod1_sn 923824240418688749236612748769245374773246293194864403046 1
    rw [show 3 * 923824240418688749236612748769245374773246293194864403046 + 1 = 2771472721256066247709838246307736124319738879584593209139 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 923824240418688749236612748769245374773246293194864403046 + 3 = 4619121202093443746183063743846226873866231465974322015233 from by ring, show 1 + 2 = 3 from by ring,
      show 12 * 923824240418688749236612748769245374773246293194864403046 + 8 = 11085890885024264990839352985230944497278955518338372836560 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 18476484808373774984732254975384907495464925863897288060935) (c₂ := ⟨0, 0, 0, 7698535336822406243638439573077044789777052443290536692056, 3⟩)
  · have h := mod0_sn 1539707067364481248727687914615408957955410488658107338411 2
    rw [show 3 * 1539707067364481248727687914615408957955410488658107338411 = 4619121202093443746183063743846226873866231465974322015233 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 1539707067364481248727687914615408957955410488658107338411 + 1 = 7698535336822406243638439573077044789777052443290536692056 from by ring, show 12 * 1539707067364481248727687914615408957955410488658107338411 + 3 = 18476484808373774984732254975384907495464925863897288060935 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 30794141347289624974553758292308179159108209773162146768226) (c₂ := ⟨0, 0, 0, 12830892228037343739397399288461741316295087405484227820094, 2⟩)
  · have h := mod2_sn 2566178445607468747879479857692348263259017481096845564018 2
    rw [show 3 * 2566178445607468747879479857692348263259017481096845564018 + 2 = 7698535336822406243638439573077044789777052443290536692056 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 2566178445607468747879479857692348263259017481096845564018 + 4 = 12830892228037343739397399288461741316295087405484227820094 from by ring, show 12 * 2566178445607468747879479857692348263259017481096845564018 + 10 = 30794141347289624974553758292308179159108209773162146768226 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 51323568912149374957589597153846965265180349621936911280380) (c₂ := ⟨0, 0, 0, 21384820380062239565662332147436235527158479009140379700158, 3⟩)
  · have h := mod1_sn 4276964076012447913132466429487247105431695801828075940031 1
    rw [show 3 * 4276964076012447913132466429487247105431695801828075940031 + 1 = 12830892228037343739397399288461741316295087405484227820094 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 4276964076012447913132466429487247105431695801828075940031 + 3 = 21384820380062239565662332147436235527158479009140379700158 from by ring, show 1 + 2 = 3 from by ring,
      show 12 * 4276964076012447913132466429487247105431695801828075940031 + 8 = 51323568912149374957589597153846965265180349621936911280380 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 85539281520248958262649328589744942108633916036561518800634) (c₂ := ⟨0, 0, 0, 35641367300103732609437220245727059211930798348567299500264, 2⟩)
  · have h := mod2_sn 7128273460020746521887444049145411842386159669713459900052 2
    rw [show 3 * 7128273460020746521887444049145411842386159669713459900052 + 2 = 21384820380062239565662332147436235527158479009140379700158 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 7128273460020746521887444049145411842386159669713459900052 + 4 = 35641367300103732609437220245727059211930798348567299500264 from by ring, show 12 * 7128273460020746521887444049145411842386159669713459900052 + 10 = 85539281520248958262649328589744942108633916036561518800634 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 142565469200414930437748880982908236847723193394269198001060) (c₂ := ⟨0, 0, 0, 59402278833506221015728700409545098686551330580945499167108, 3⟩)
  · have h := mod1_sn 11880455766701244203145740081909019737310266116189099833421 1
    rw [show 3 * 11880455766701244203145740081909019737310266116189099833421 + 1 = 35641367300103732609437220245727059211930798348567299500264 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 11880455766701244203145740081909019737310266116189099833421 + 3 = 59402278833506221015728700409545098686551330580945499167108 from by ring, show 1 + 2 = 3 from by ring,
      show 12 * 11880455766701244203145740081909019737310266116189099833421 + 8 = 142565469200414930437748880982908236847723193394269198001060 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 237609115334024884062914801638180394746205322323781996668434) (c₂ := ⟨0, 0, 0, 99003798055843701692881167349241831144252217634909165278514, 2⟩)
  · have h := mod2_sn 19800759611168740338576233469848366228850443526981833055702 2
    rw [show 3 * 19800759611168740338576233469848366228850443526981833055702 + 2 = 59402278833506221015728700409545098686551330580945499167108 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 19800759611168740338576233469848366228850443526981833055702 + 4 = 99003798055843701692881167349241831144252217634909165278514 from by ring, show 12 * 19800759611168740338576233469848366228850443526981833055702 + 10 = 237609115334024884062914801638180394746205322323781996668434 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 396015192223374806771524669396967324577008870539636661114060) (c₂ := ⟨0, 0, 0, 165006330093072836154801945582069718573753696058181942130858, 3⟩)
  · have h := mod1_sn 33001266018614567230960389116413943714750739211636388426171 1
    rw [show 3 * 33001266018614567230960389116413943714750739211636388426171 + 1 = 99003798055843701692881167349241831144252217634909165278514 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 33001266018614567230960389116413943714750739211636388426171 + 3 = 165006330093072836154801945582069718573753696058181942130858 from by ring, show 1 + 2 = 3 from by ring,
      show 12 * 33001266018614567230960389116413943714750739211636388426171 + 8 = 396015192223374806771524669396967324577008870539636661114060 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 660025320372291344619207782328278874295014784232727768523436) (c₂ := ⟨0, 0, 0, 275010550155121393591336575970116197622922826763636570218098, 4⟩)
  · have h := mod1_sn 55002110031024278718267315194023239524584565352727314043619 2
    rw [show 3 * 55002110031024278718267315194023239524584565352727314043619 + 1 = 165006330093072836154801945582069718573753696058181942130858 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 55002110031024278718267315194023239524584565352727314043619 + 3 = 275010550155121393591336575970116197622922826763636570218098 from by ring, show 2 + 2 = 4 from by ring,
      show 12 * 55002110031024278718267315194023239524584565352727314043619 + 8 = 660025320372291344619207782328278874295014784232727768523436 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1100042200620485574365346303880464790491691307054546280872396) (c₂ := ⟨0, 0, 0, 458350916925202322652227626616860329371538044606060950363498, 5⟩)
  · have h := mod1_sn 91670183385040464530445525323372065874307608921212190072699 3
    rw [show 3 * 91670183385040464530445525323372065874307608921212190072699 + 1 = 275010550155121393591336575970116197622922826763636570218098 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 91670183385040464530445525323372065874307608921212190072699 + 3 = 458350916925202322652227626616860329371538044606060950363498 from by ring, show 3 + 2 = 5 from by ring,
      show 12 * 91670183385040464530445525323372065874307608921212190072699 + 8 = 1100042200620485574365346303880464790491691307054546280872396 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 1833403667700809290608910506467441317486152178424243801453996) (c₂ := ⟨0, 0, 0, 763918194875337204420379377694767215619230074343434917272498, 6⟩)
  · have h := mod1_sn 152783638975067440884075875538953443123846014868686983454499 4
    rw [show 3 * 152783638975067440884075875538953443123846014868686983454499 + 1 = 458350916925202322652227626616860329371538044606060950363498 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 152783638975067440884075875538953443123846014868686983454499 + 3 = 763918194875337204420379377694767215619230074343434917272498 from by ring, show 4 + 2 = 6 from by ring,
      show 12 * 152783638975067440884075875538953443123846014868686983454499 + 8 = 1833403667700809290608910506467441317486152178424243801453996 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 3055672779501348817681517510779068862476920297373739669089994) (c₂ := ⟨0, 0, 0, 1273196991458895340700632296157945359365383457239058195454164, 5⟩)
  · have h := mod2_sn 254639398291779068140126459231589071873076691447811639090832 5
    rw [show 3 * 254639398291779068140126459231589071873076691447811639090832 + 2 = 763918194875337204420379377694767215619230074343434917272498 from by ring, show 5 + 1 = 6 from by ring,
      show 5 * 254639398291779068140126459231589071873076691447811639090832 + 4 = 1273196991458895340700632296157945359365383457239058195454164 from by ring, show 12 * 254639398291779068140126459231589071873076691447811639090832 + 10 = 3055672779501348817681517510779068862476920297373739669089994 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 5092787965835581362802529184631781437461533828956232781816658) (c₂ := ⟨0, 0, 0, 2121994985764825567834387160263242265608972428731763659090274, 4⟩)
  · have h := mod2_sn 424398997152965113566877432052648453121794485746352731818054 4
    rw [show 3 * 424398997152965113566877432052648453121794485746352731818054 + 2 = 1273196991458895340700632296157945359365383457239058195454164 from by ring, show 4 + 1 = 5 from by ring,
      show 5 * 424398997152965113566877432052648453121794485746352731818054 + 4 = 2121994985764825567834387160263242265608972428731763659090274 from by ring, show 12 * 424398997152965113566877432052648453121794485746352731818054 + 10 = 5092787965835581362802529184631781437461533828956232781816658 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 8487979943059302271337548641052969062435889714927054636361098) (c₂ := ⟨0, 0, 0, 3536658309608042613057311933772070442681620714552939431817124, 3⟩)
  · have h := mod2_sn 707331661921608522611462386754414088536324142910587886363424 3
    rw [show 3 * 707331661921608522611462386754414088536324142910587886363424 + 2 = 2121994985764825567834387160263242265608972428731763659090274 from by ring, show 3 + 1 = 4 from by ring,
      show 5 * 707331661921608522611462386754414088536324142910587886363424 + 4 = 3536658309608042613057311933772070442681620714552939431817124 from by ring, show 12 * 707331661921608522611462386754414088536324142910587886363424 + 10 = 8487979943059302271337548641052969062435889714927054636361098 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 14146633238432170452229247735088281770726482858211757727268498) (c₂ := ⟨0, 0, 0, 5894430516013404355095519889620117404469367857588232386361874, 2⟩)
  · have h := mod2_sn 1178886103202680871019103977924023480893873571517646477272374 2
    rw [show 3 * 1178886103202680871019103977924023480893873571517646477272374 + 2 = 3536658309608042613057311933772070442681620714552939431817124 from by ring, show 2 + 1 = 3 from by ring,
      show 5 * 1178886103202680871019103977924023480893873571517646477272374 + 4 = 5894430516013404355095519889620117404469367857588232386361874 from by ring, show 12 * 1178886103202680871019103977924023480893873571517646477272374 + 10 = 14146633238432170452229247735088281770726482858211757727268498 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 23577722064053617420382079558480469617877471430352929545447498) (c₂ := ⟨0, 0, 0, 9824050860022340591825866482700195674115613095980387310603124, 1⟩)
  · have h := mod2_sn 1964810172004468118365173296540039134823122619196077462120624 1
    rw [show 3 * 1964810172004468118365173296540039134823122619196077462120624 + 2 = 5894430516013404355095519889620117404469367857588232386361874 from by ring, show 1 + 1 = 2 from by ring,
      show 5 * 1964810172004468118365173296540039134823122619196077462120624 + 4 = 9824050860022340591825866482700195674115613095980387310603124 from by ring, show 12 * 1964810172004468118365173296540039134823122619196077462120624 + 10 = 23577722064053617420382079558480469617877471430352929545447498 from by ring] at h; exact h
  apply stepNat_haltsIn_add (m := 39296203440089362367303465930800782696462452383921549242412498) (c₂ := ⟨0, 0, 0, 16373418100037234319709777471166992790192688493300645517671874, 0⟩)
  · have h := mod2_sn 3274683620007446863941955494233398558038537698660129103534374 0
    rw [show 3 * 3274683620007446863941955494233398558038537698660129103534374 + 2 = 9824050860022340591825866482700195674115613095980387310603124 from by ring, show 0 + 1 = 1 from by ring,
      show 5 * 3274683620007446863941955494233398558038537698660129103534374 + 4 = 16373418100037234319709777471166992790192688493300645517671874 from by ring, show 12 * 3274683620007446863941955494233398558038537698660129103534374 + 10 = 39296203440089362367303465930800782696462452383921549242412498 from by ring] at h; exact h
  exact halt_sn 16373418100037234319709777471166992790192688493300645517671874

end Sz22_halted_692_5