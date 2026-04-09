import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_halted_692 #1: [1/12, 9/10, 14/3, 11/2, 5/7, 3/11]

Vector representation:
```
-2 -1  0  0  0
-1  2 -1  0  0
 1 -1  0  1  0
-1  0  0  0  1
 0  0  1 -1  0
 0  1  0  0 -1
```

This Fractran program halts in 114613926700260640237968442298168949531348819453104518623702295 steps.

Author: Claude
-/

namespace Sz22_halted_692_1

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+2, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

private theorem r5_sn : ∀ k c d e, (⟨0, 0, c, d + k, e⟩ : Q) [fm]⊢^{k} ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; rfl
  rw [show d + (k + 1) = (d + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨0, 0, c, (d + k) + 1, e⟩ = some ⟨0, 0, c + 1, d + k, e⟩; rfl
  have h := ih (c + 1) d e; rw [show (c + 1) + k = c + (1 + k) from by ring] at h; exact h

private theorem r1r3_sn : ∀ k, ∀ b c d e, (⟨1, b, c + k, d, e⟩ : Q) [fm]⊢^{2 * k} ⟨1, b + k, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · simp; rfl
  rw [show c + (k + 1) = (c + k) + 1 from by ring, show 2 * (k + 1) = 2 + 2 * k from by ring]
  apply stepNat_trans 2 (2 * k)
  · show stepNat fm 2 ⟨1, b, (c + k) + 1, d, e⟩ = some ⟨1, b + 1, c + k, d + 1, e⟩; rfl
  have h := ih (b + 1) c (d + 1) e
  rw [show (b + 1) + k = b + (k + 1) from by ring,
    show (d + 1) + k = d + (k + 1) from by ring] at h; exact h

private theorem drain_b_sn : ∀ k, ∀ b d e, (⟨1, 3 * k + b, 0, d, e⟩ : Q) [fm]⊢^{3 * k} ⟨1, b, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · simp; rfl
  rw [show 3 * (k + 1) + b = 3 * k + (b + 3) from by ring, show 3 * (k + 1) = 3 + 3 * k from by ring]
  apply stepNat_trans 3 (3 * k)
  · show stepNat fm 3 ⟨1, 3 * k + (b + 3), 0, d, e⟩ = some ⟨1, 3 * k + b, 0, d + 2, e⟩; rfl
  have h := ih b (d + 2) e; rw [show (d + 2) + 2 * k = d + 2 * (k + 1) from by ring] at h; exact h

private theorem tail_b0_sn : ∀ d e, (⟨1, 0, 0, d, e⟩ : Q) [fm]⊢^{1} ⟨0, 0, 0, d, e + 1⟩ := by
  intro d e; rfl

private theorem tail_b1_sn : ∀ d e, (⟨1, 1, 0, d, e⟩ : Q) [fm]⊢^{3} ⟨0, 0, 0, d + 1, e + 2⟩ := by
  intro d e; rfl

private theorem tail_b2_sn : ∀ d e, (⟨1, 2, 0, d, e⟩ : Q) [fm]⊢^{2} ⟨0, 0, 0, d + 1, e⟩ := by
  intro d e; rfl

private theorem mod0_sn : ∀ k E, (⟨0, 0, 0, 3 * k, E + 1⟩ : Q) [fm]⊢^{12 * k + 3} ⟨0, 0, 0, 5 * k + 1, E + 1⟩ := by
  intro k E
  have h1 := r5_sn (3 * k) 0 0 (E + 1)
  simp only [Nat.zero_add] at h1
  have h2 : (⟨0, 0, 3 * k, 0, E + 1⟩ : Q) [fm]⊢^{1} ⟨0, 1, 3 * k, 0, E⟩ := rfl
  have h3 : (⟨0, 1, 3 * k, 0, E⟩ : Q) [fm]⊢^{1} ⟨1, 0, 3 * k, 1, E⟩ := rfl
  have h4 := r1r3_sn (3 * k) 0 0 1 E
  simp only [Nat.zero_add] at h4
  rw [show 1 + 3 * k = 3 * k + 1 from by ring] at h4
  have h5 := drain_b_sn k 0 (3 * k + 1) E
  rw [show 3 * k + 1 + 2 * k = 5 * k + 1 from by ring] at h5
  have h6 := tail_b0_sn (5 * k + 1) E
  have := stepNat_trans (3 * k) 1 h1 h2
  have := stepNat_trans (3 * k + 1) 1 this h3
  have := stepNat_trans (3 * k + 1 + 1) (2 * (3 * k)) this h4
  have := stepNat_trans (3 * k + 1 + 1 + 2 * (3 * k)) (3 * k) this h5
  have := stepNat_trans (3 * k + 1 + 1 + 2 * (3 * k) + 3 * k) 1 this h6
  rw [show 3 * k + 1 + 1 + 2 * (3 * k) + 3 * k + 1 = 12 * k + 3 from by ring] at this
  exact this

private theorem mod1_sn : ∀ k E, (⟨0, 0, 0, 3 * k + 1, E + 1⟩ : Q) [fm]⊢^{12 * k + 8} ⟨0, 0, 0, 5 * k + 3, E + 2⟩ := by
  intro k E
  have h1 := r5_sn (3 * k + 1) 0 0 (E + 1)
  simp only [Nat.zero_add] at h1
  have h2 : (⟨0, 0, 3 * k + 1, 0, E + 1⟩ : Q) [fm]⊢^{1} ⟨0, 1, 3 * k + 1, 0, E⟩ := rfl
  have h3 : (⟨0, 1, 3 * k + 1, 0, E⟩ : Q) [fm]⊢^{1} ⟨1, 0, 3 * k + 1, 1, E⟩ := rfl
  have h4 := r1r3_sn (3 * k + 1) 0 0 1 E
  simp only [Nat.zero_add] at h4
  rw [show 1 + (3 * k + 1) = 3 * k + 2 from by ring] at h4
  have h5 := drain_b_sn k 1 (3 * k + 2) E
  rw [show 3 * k + 2 + 2 * k = 5 * k + 2 from by ring] at h5
  have h6 := tail_b1_sn (5 * k + 2) E
  rw [show 5 * k + 2 + 1 = 5 * k + 3 from by ring] at h6
  have := stepNat_trans (3 * k + 1) 1 h1 h2
  have := stepNat_trans (3 * k + 1 + 1) 1 this h3
  have := stepNat_trans (3 * k + 1 + 1 + 1) (2 * (3 * k + 1)) this h4
  have := stepNat_trans (3 * k + 1 + 1 + 1 + 2 * (3 * k + 1)) (3 * k) this h5
  have := stepNat_trans (3 * k + 1 + 1 + 1 + 2 * (3 * k + 1) + 3 * k) 3 this h6
  rw [show 3 * k + 1 + 1 + 1 + 2 * (3 * k + 1) + 3 * k + 3 = 12 * k + 8 from by ring] at this
  exact this

private theorem mod2_sn : ∀ k E, (⟨0, 0, 0, 3 * k + 2, E + 1⟩ : Q) [fm]⊢^{12 * k + 10} ⟨0, 0, 0, 5 * k + 4, E⟩ := by
  intro k E
  have h1 := r5_sn (3 * k + 2) 0 0 (E + 1)
  simp only [Nat.zero_add] at h1
  have h2 : (⟨0, 0, 3 * k + 2, 0, E + 1⟩ : Q) [fm]⊢^{1} ⟨0, 1, 3 * k + 2, 0, E⟩ := rfl
  have h3 : (⟨0, 1, 3 * k + 2, 0, E⟩ : Q) [fm]⊢^{1} ⟨1, 0, 3 * k + 2, 1, E⟩ := rfl
  have h4 := r1r3_sn (3 * k + 2) 0 0 1 E
  simp only [Nat.zero_add] at h4
  rw [show 1 + (3 * k + 2) = 3 * k + 3 from by ring] at h4
  have h5 := drain_b_sn k 2 (3 * k + 3) E
  rw [show 3 * k + 3 + 2 * k = 5 * k + 3 from by ring] at h5
  have h6 := tail_b2_sn (5 * k + 3) E
  rw [show 5 * k + 3 + 1 = 5 * k + 4 from by ring] at h6
  have := stepNat_trans (3 * k + 2) 1 h1 h2
  have := stepNat_trans (3 * k + 2 + 1) 1 this h3
  have := stepNat_trans (3 * k + 2 + 1 + 1) (2 * (3 * k + 2)) this h4
  have := stepNat_trans (3 * k + 2 + 1 + 1 + 2 * (3 * k + 2)) (3 * k) this h5
  have := stepNat_trans (3 * k + 2 + 1 + 1 + 2 * (3 * k + 2) + 3 * k) 2 this h6
  rw [show 3 * k + 2 + 1 + 1 + 2 * (3 * k + 2) + 3 * k + 2 = 12 * k + 10 from by ring] at this
  exact this

private theorem halt_sn : ∀ D, haltsIn fm (⟨0, 0, 0, D, 0⟩ : Q) D := by
  intro D; refine ⟨⟨0, 0, D, 0, 0⟩, ?_, rfl⟩
  have h := r5_sn D 0 0 0
  simp only [Nat.zero_add] at h; exact h

theorem fm_haltsIn : haltsIn fm c₀ 114613926700260640237968442298168949531348819453104518623702295 := by
    apply stepNat_haltsIn_add (m := 12) (c₂ := ⟨0, 0, 0, 3, 2⟩)
    · show stepNat fm 12 c₀ = some ⟨0, 0, 0, 3, 2⟩; rfl
    apply stepNat_haltsIn_add (m := 15) (c₂ := ⟨0, 0, 0, 6, 2⟩)
    · have h := mod0_sn 1 1
      exact h
    apply stepNat_haltsIn_add (m := 27) (c₂ := ⟨0, 0, 0, 11, 2⟩)
    · have h := mod0_sn 2 1
      exact h
    apply stepNat_haltsIn_add (m := 46) (c₂ := ⟨0, 0, 0, 19, 1⟩)
    · have h := mod2_sn 3 1
      exact h
    apply stepNat_haltsIn_add (m := 80) (c₂ := ⟨0, 0, 0, 33, 2⟩)
    · have h := mod1_sn 6 0
      exact h
    apply stepNat_haltsIn_add (m := 135) (c₂ := ⟨0, 0, 0, 56, 2⟩)
    · have h := mod0_sn 11 1
      exact h
    apply stepNat_haltsIn_add (m := 226) (c₂ := ⟨0, 0, 0, 94, 1⟩)
    · have h := mod2_sn 18 1
      exact h
    apply stepNat_haltsIn_add (m := 380) (c₂ := ⟨0, 0, 0, 158, 2⟩)
    · have h := mod1_sn 31 0
      exact h
    apply stepNat_haltsIn_add (m := 634) (c₂ := ⟨0, 0, 0, 264, 1⟩)
    · have h := mod2_sn 52 1
      exact h
    apply stepNat_haltsIn_add (m := 1059) (c₂ := ⟨0, 0, 0, 441, 1⟩)
    · have h := mod0_sn 88 0
      exact h
    apply stepNat_haltsIn_add (m := 1767) (c₂ := ⟨0, 0, 0, 736, 1⟩)
    · have h := mod0_sn 147 0
      exact h
    apply stepNat_haltsIn_add (m := 2948) (c₂ := ⟨0, 0, 0, 1228, 2⟩)
    · have h := mod1_sn 245 0
      exact h
    apply stepNat_haltsIn_add (m := 4916) (c₂ := ⟨0, 0, 0, 2048, 3⟩)
    · have h := mod1_sn 409 1
      exact h
    apply stepNat_haltsIn_add (m := 8194) (c₂ := ⟨0, 0, 0, 3414, 2⟩)
    · have h := mod2_sn 682 2
      exact h
    apply stepNat_haltsIn_add (m := 13659) (c₂ := ⟨0, 0, 0, 5691, 2⟩)
    · have h := mod0_sn 1138 1
      exact h
    apply stepNat_haltsIn_add (m := 22767) (c₂ := ⟨0, 0, 0, 9486, 2⟩)
    · have h := mod0_sn 1897 1
      exact h
    apply stepNat_haltsIn_add (m := 37947) (c₂ := ⟨0, 0, 0, 15811, 2⟩)
    · have h := mod0_sn 3162 1
      exact h
    apply stepNat_haltsIn_add (m := 63248) (c₂ := ⟨0, 0, 0, 26353, 3⟩)
    · have h := mod1_sn 5270 1
      exact h
    apply stepNat_haltsIn_add (m := 105416) (c₂ := ⟨0, 0, 0, 43923, 4⟩)
    · have h := mod1_sn 8784 2
      exact h
    apply stepNat_haltsIn_add (m := 175695) (c₂ := ⟨0, 0, 0, 73206, 4⟩)
    · have h := mod0_sn 14641 3
      exact h
    apply stepNat_haltsIn_add (m := 292827) (c₂ := ⟨0, 0, 0, 122011, 4⟩)
    · have h := mod0_sn 24402 3
      exact h
    apply stepNat_haltsIn_add (m := 488048) (c₂ := ⟨0, 0, 0, 203353, 5⟩)
    · have h := mod1_sn 40670 3
      exact h
    apply stepNat_haltsIn_add (m := 813416) (c₂ := ⟨0, 0, 0, 338923, 6⟩)
    · have h := mod1_sn 67784 4
      exact h
    apply stepNat_haltsIn_add (m := 1355696) (c₂ := ⟨0, 0, 0, 564873, 7⟩)
    · have h := mod1_sn 112974 5
      exact h
    apply stepNat_haltsIn_add (m := 2259495) (c₂ := ⟨0, 0, 0, 941456, 7⟩)
    · have h := mod0_sn 188291 6
      exact h
    apply stepNat_haltsIn_add (m := 3765826) (c₂ := ⟨0, 0, 0, 1569094, 6⟩)
    · have h := mod2_sn 313818 6
      exact h
    apply stepNat_haltsIn_add (m := 6276380) (c₂ := ⟨0, 0, 0, 2615158, 7⟩)
    · have h := mod1_sn 523031 5
      exact h
    apply stepNat_haltsIn_add (m := 10460636) (c₂ := ⟨0, 0, 0, 4358598, 8⟩)
    · have h := mod1_sn 871719 6
      exact h
    apply stepNat_haltsIn_add (m := 17434395) (c₂ := ⟨0, 0, 0, 7264331, 8⟩)
    · have h := mod0_sn 1452866 7
      exact h
    apply stepNat_haltsIn_add (m := 29057326) (c₂ := ⟨0, 0, 0, 12107219, 7⟩)
    · have h := mod2_sn 2421443 7
      exact h
    apply stepNat_haltsIn_add (m := 48428878) (c₂ := ⟨0, 0, 0, 20178699, 6⟩)
    · have h := mod2_sn 4035739 6
      exact h
    apply stepNat_haltsIn_add (m := 80714799) (c₂ := ⟨0, 0, 0, 33631166, 6⟩)
    · have h := mod0_sn 6726233 5
      exact h
    apply stepNat_haltsIn_add (m := 134524666) (c₂ := ⟨0, 0, 0, 56051944, 5⟩)
    · have h := mod2_sn 11210388 5
      exact h
    apply stepNat_haltsIn_add (m := 224207780) (c₂ := ⟨0, 0, 0, 93419908, 6⟩)
    · have h := mod1_sn 18683981 4
      exact h
    apply stepNat_haltsIn_add (m := 373679636) (c₂ := ⟨0, 0, 0, 155699848, 7⟩)
    · have h := mod1_sn 31139969 5
      exact h
    apply stepNat_haltsIn_add (m := 622799396) (c₂ := ⟨0, 0, 0, 259499748, 8⟩)
    · have h := mod1_sn 51899949 6
      exact h
    apply stepNat_haltsIn_add (m := 1037998995) (c₂ := ⟨0, 0, 0, 432499581, 8⟩)
    · have h := mod0_sn 86499916 7
      exact h
    apply stepNat_haltsIn_add (m := 1729998327) (c₂ := ⟨0, 0, 0, 720832636, 8⟩)
    · have h := mod0_sn 144166527 7
      exact h
    apply stepNat_haltsIn_add (m := 2883330548) (c₂ := ⟨0, 0, 0, 1201387728, 9⟩)
    · have h := mod1_sn 240277545 7
      exact h
    apply stepNat_haltsIn_add (m := 4805550915) (c₂ := ⟨0, 0, 0, 2002312881, 9⟩)
    · have h := mod0_sn 400462576 8
      exact h
    apply stepNat_haltsIn_add (m := 8009251527) (c₂ := ⟨0, 0, 0, 3337188136, 9⟩)
    · have h := mod0_sn 667437627 8
      exact h
    apply stepNat_haltsIn_add (m := 13348752548) (c₂ := ⟨0, 0, 0, 5561980228, 10⟩)
    · have h := mod1_sn 1112396045 8
      exact h
    apply stepNat_haltsIn_add (m := 22247920916) (c₂ := ⟨0, 0, 0, 9269967048, 11⟩)
    · have h := mod1_sn 1853993409 9
      exact h
    apply stepNat_haltsIn_add (m := 37079868195) (c₂ := ⟨0, 0, 0, 15449945081, 11⟩)
    · have h := mod0_sn 3089989016 10
      exact h
    apply stepNat_haltsIn_add (m := 61799780326) (c₂ := ⟨0, 0, 0, 25749908469, 10⟩)
    · have h := mod2_sn 5149981693 10
      exact h
    apply stepNat_haltsIn_add (m := 102999633879) (c₂ := ⟨0, 0, 0, 42916514116, 10⟩)
    · have h := mod0_sn 8583302823 9
      exact h
    apply stepNat_haltsIn_add (m := 171666056468) (c₂ := ⟨0, 0, 0, 71527523528, 11⟩)
    · have h := mod1_sn 14305504705 9
      exact h
    apply stepNat_haltsIn_add (m := 286110094114) (c₂ := ⟨0, 0, 0, 119212539214, 10⟩)
    · have h := mod2_sn 23842507842 10
      exact h
    apply stepNat_haltsIn_add (m := 476850156860) (c₂ := ⟨0, 0, 0, 198687565358, 11⟩)
    · have h := mod1_sn 39737513071 9
      exact h
    apply stepNat_haltsIn_add (m := 794750261434) (c₂ := ⟨0, 0, 0, 331145942264, 10⟩)
    · have h := mod2_sn 66229188452 10
      exact h
    apply stepNat_haltsIn_add (m := 1324583769058) (c₂ := ⟨0, 0, 0, 551909903774, 9⟩)
    · have h := mod2_sn 110381980754 9
      exact h
    apply stepNat_haltsIn_add (m := 2207639615098) (c₂ := ⟨0, 0, 0, 919849839624, 8⟩)
    · have h := mod2_sn 183969967924 8
      exact h
    apply stepNat_haltsIn_add (m := 3679399358499) (c₂ := ⟨0, 0, 0, 1533083066041, 8⟩)
    · have h := mod0_sn 306616613208 7
      exact h
    apply stepNat_haltsIn_add (m := 6132332264168) (c₂ := ⟨0, 0, 0, 2555138443403, 9⟩)
    · have h := mod1_sn 511027688680 7
      exact h
    apply stepNat_haltsIn_add (m := 10220553773614) (c₂ := ⟨0, 0, 0, 4258564072339, 8⟩)
    · have h := mod2_sn 851712814467 8
      exact h
    apply stepNat_haltsIn_add (m := 17034256289360) (c₂ := ⟨0, 0, 0, 7097606787233, 9⟩)
    · have h := mod1_sn 1419521357446 7
      exact h
    apply stepNat_haltsIn_add (m := 28390427148934) (c₂ := ⟨0, 0, 0, 11829344645389, 8⟩)
    · have h := mod2_sn 2365868929077 8
      exact h
    apply stepNat_haltsIn_add (m := 47317378581560) (c₂ := ⟨0, 0, 0, 19715574408983, 9⟩)
    · have h := mod1_sn 3943114881796 7
      exact h
    apply stepNat_haltsIn_add (m := 78862297635934) (c₂ := ⟨0, 0, 0, 32859290681639, 8⟩)
    · have h := mod2_sn 6571858136327 8
      exact h
    apply stepNat_haltsIn_add (m := 131437162726558) (c₂ := ⟨0, 0, 0, 54765484469399, 7⟩)
    · have h := mod2_sn 10953096893879 7
      exact h
    apply stepNat_haltsIn_add (m := 219061937877598) (c₂ := ⟨0, 0, 0, 91275807448999, 6⟩)
    · have h := mod2_sn 18255161489799 6
      exact h
    apply stepNat_haltsIn_add (m := 365103229796000) (c₂ := ⟨0, 0, 0, 152126345748333, 7⟩)
    · have h := mod1_sn 30425269149666 5
      exact h
    apply stepNat_haltsIn_add (m := 608505382993335) (c₂ := ⟨0, 0, 0, 253543909580556, 7⟩)
    · have h := mod0_sn 50708781916111 6
      exact h
    apply stepNat_haltsIn_add (m := 1014175638322227) (c₂ := ⟨0, 0, 0, 422573182634261, 7⟩)
    · have h := mod0_sn 84514636526852 6
      exact h
    apply stepNat_haltsIn_add (m := 1690292730537046) (c₂ := ⟨0, 0, 0, 704288637723769, 6⟩)
    · have h := mod2_sn 140857727544753 6
      exact h
    apply stepNat_haltsIn_add (m := 2817154550895080) (c₂ := ⟨0, 0, 0, 1173814396206283, 7⟩)
    · have h := mod1_sn 234762879241256 5
      exact h
    apply stepNat_haltsIn_add (m := 4695257584825136) (c₂ := ⟨0, 0, 0, 1956357327010473, 8⟩)
    · have h := mod1_sn 391271465402094 6
      exact h
    apply stepNat_haltsIn_add (m := 7825429308041895) (c₂ := ⟨0, 0, 0, 3260595545017456, 8⟩)
    · have h := mod0_sn 652119109003491 7
      exact h
    apply stepNat_haltsIn_add (m := 13042382180069828) (c₂ := ⟨0, 0, 0, 5434325908362428, 9⟩)
    · have h := mod1_sn 1086865181672485 7
      exact h
    apply stepNat_haltsIn_add (m := 21737303633449714) (c₂ := ⟨0, 0, 0, 9057209847270714, 8⟩)
    · have h := mod2_sn 1811441969454142 8
      exact h
    apply stepNat_haltsIn_add (m := 36228839389082859) (c₂ := ⟨0, 0, 0, 15095349745451191, 8⟩)
    · have h := mod0_sn 3019069949090238 7
      exact h
    apply stepNat_haltsIn_add (m := 60381398981804768) (c₂ := ⟨0, 0, 0, 25158916242418653, 9⟩)
    · have h := mod1_sn 5031783248483730 7
      exact h
    apply stepNat_haltsIn_add (m := 100635664969674615) (c₂ := ⟨0, 0, 0, 41931527070697756, 9⟩)
    · have h := mod0_sn 8386305414139551 8
      exact h
    apply stepNat_haltsIn_add (m := 167726108282791028) (c₂ := ⟨0, 0, 0, 69885878451162928, 10⟩)
    · have h := mod1_sn 13977175690232585 8
      exact h
    apply stepNat_haltsIn_add (m := 279543513804651716) (c₂ := ⟨0, 0, 0, 116476464085271548, 11⟩)
    · have h := mod1_sn 23295292817054309 9
      exact h
    apply stepNat_haltsIn_add (m := 465905856341086196) (c₂ := ⟨0, 0, 0, 194127440142119248, 12⟩)
    · have h := mod1_sn 38825488028423849 10
      exact h
    apply stepNat_haltsIn_add (m := 776509760568476996) (c₂ := ⟨0, 0, 0, 323545733570198748, 13⟩)
    · have h := mod1_sn 64709146714039749 11
      exact h
    apply stepNat_haltsIn_add (m := 1294182934280794995) (c₂ := ⟨0, 0, 0, 539242889283664581, 13⟩)
    · have h := mod0_sn 107848577856732916 12
      exact h
    apply stepNat_haltsIn_add (m := 2156971557134658327) (c₂ := ⟨0, 0, 0, 898738148806107636, 13⟩)
    · have h := mod0_sn 179747629761221527 12
      exact h
    apply stepNat_haltsIn_add (m := 3594952595224430547) (c₂ := ⟨0, 0, 0, 1497896914676846061, 13⟩)
    · have h := mod0_sn 299579382935369212 12
      exact h
    apply stepNat_haltsIn_add (m := 5991587658707384247) (c₂ := ⟨0, 0, 0, 2496494857794743436, 13⟩)
    · have h := mod0_sn 499298971558948687 12
      exact h
    apply stepNat_haltsIn_add (m := 9985979431178973747) (c₂ := ⟨0, 0, 0, 4160824762991239061, 13⟩)
    · have h := mod0_sn 832164952598247812 12
      exact h
    apply stepNat_haltsIn_add (m := 16643299051964956246) (c₂ := ⟨0, 0, 0, 6934707938318731769, 12⟩)
    · have h := mod2_sn 1386941587663746353 12
      exact h
    apply stepNat_haltsIn_add (m := 27738831753274927078) (c₂ := ⟨0, 0, 0, 11557846563864552949, 11⟩)
    · have h := mod2_sn 2311569312772910589 11
      exact h
    apply stepNat_haltsIn_add (m := 46231386255458211800) (c₂ := ⟨0, 0, 0, 19263077606440921583, 12⟩)
    · have h := mod1_sn 3852615521288184316 10
      exact h
    apply stepNat_haltsIn_add (m := 77052310425763686334) (c₂ := ⟨0, 0, 0, 32105129344068202639, 11⟩)
    · have h := mod2_sn 6421025868813640527 11
      exact h
    apply stepNat_haltsIn_add (m := 128420517376272810560) (c₂ := ⟨0, 0, 0, 53508548906780337733, 12⟩)
    · have h := mod1_sn 10701709781356067546 10
      exact h
    apply stepNat_haltsIn_add (m := 214034195627121350936) (c₂ := ⟨0, 0, 0, 89180914844633896223, 13⟩)
    · have h := mod1_sn 17836182968926779244 11
      exact h
    apply stepNat_haltsIn_add (m := 356723659378535584894) (c₂ := ⟨0, 0, 0, 148634858074389827039, 12⟩)
    · have h := mod2_sn 29726971614877965407 12
      exact h
    apply stepNat_haltsIn_add (m := 594539432297559308158) (c₂ := ⟨0, 0, 0, 247724763457316378399, 11⟩)
    · have h := mod2_sn 49544952691463275679 11
      exact h
    apply stepNat_haltsIn_add (m := 990899053829265513598) (c₂ := ⟨0, 0, 0, 412874605762193963999, 10⟩)
    · have h := mod2_sn 82574921152438792799 10
      exact h
    apply stepNat_haltsIn_add (m := 1651498423048775855998) (c₂ := ⟨0, 0, 0, 688124342936989939999, 9⟩)
    · have h := mod2_sn 137624868587397987999 9
      exact h
    apply stepNat_haltsIn_add (m := 2752497371747959760000) (c₂ := ⟨0, 0, 0, 1146873904894983233333, 10⟩)
    · have h := mod1_sn 229374780978996646666 8
      exact h
    apply stepNat_haltsIn_add (m := 4587495619579932933334) (c₂ := ⟨0, 0, 0, 1911456508158305388889, 9⟩)
    · have h := mod2_sn 382291301631661077777 9
      exact h
    apply stepNat_haltsIn_add (m := 7645826032633221555560) (c₂ := ⟨0, 0, 0, 3185760846930508981483, 10⟩)
    · have h := mod1_sn 637152169386101796296 8
      exact h
    apply stepNat_haltsIn_add (m := 12743043387722035925936) (c₂ := ⟨0, 0, 0, 5309601411550848302473, 11⟩)
    · have h := mod1_sn 1061920282310169660494 9
      exact h
    apply stepNat_haltsIn_add (m := 21238405646203393209896) (c₂ := ⟨0, 0, 0, 8849335685918080504123, 12⟩)
    · have h := mod1_sn 1769867137183616100824 10
      exact h
    apply stepNat_haltsIn_add (m := 35397342743672322016496) (c₂ := ⟨0, 0, 0, 14748892809863467506873, 13⟩)
    · have h := mod1_sn 2949778561972693501374 11
      exact h
    apply stepNat_haltsIn_add (m := 58995571239453870027495) (c₂ := ⟨0, 0, 0, 24581488016439112511456, 13⟩)
    · have h := mod0_sn 4916297603287822502291 12
      exact h
    apply stepNat_haltsIn_add (m := 98325952065756450045826) (c₂ := ⟨0, 0, 0, 40969146694065187519094, 12⟩)
    · have h := mod2_sn 8193829338813037503818 12
      exact h
    apply stepNat_haltsIn_add (m := 163876586776260750076378) (c₂ := ⟨0, 0, 0, 68281911156775312531824, 11⟩)
    · have h := mod2_sn 13656382231355062506364 11
      exact h
    apply stepNat_haltsIn_add (m := 273127644627101250127299) (c₂ := ⟨0, 0, 0, 113803185261292187553041, 11⟩)
    · have h := mod0_sn 22760637052258437510608 10
      exact h
    apply stepNat_haltsIn_add (m := 455212741045168750212166) (c₂ := ⟨0, 0, 0, 189671975435486979255069, 10⟩)
    · have h := mod2_sn 37934395087097395851013 10
      exact h
    apply stepNat_haltsIn_add (m := 758687901741947917020279) (c₂ := ⟨0, 0, 0, 316119959059144965425116, 10⟩)
    · have h := mod0_sn 63223991811828993085023 9
      exact h
    apply stepNat_haltsIn_add (m := 1264479836236579861700468) (c₂ := ⟨0, 0, 0, 526866598431908275708528, 11⟩)
    · have h := mod1_sn 105373319686381655141705 9
      exact h
    apply stepNat_haltsIn_add (m := 2107466393727633102834116) (c₂ := ⟨0, 0, 0, 878110997386513792847548, 12⟩)
    · have h := mod1_sn 175622199477302758569509 10
      exact h
    apply stepNat_haltsIn_add (m := 3512443989546055171390196) (c₂ := ⟨0, 0, 0, 1463518328977522988079248, 13⟩)
    · have h := mod1_sn 292703665795504597615849 11
      exact h
    apply stepNat_haltsIn_add (m := 5854073315910091952316994) (c₂ := ⟨0, 0, 0, 2439197214962538313465414, 12⟩)
    · have h := mod2_sn 487839442992507662693082 12
      exact h
    apply stepNat_haltsIn_add (m := 9756788859850153253861660) (c₂ := ⟨0, 0, 0, 4065328691604230522442358, 13⟩)
    · have h := mod1_sn 813065738320846104488471 11
      exact h
    apply stepNat_haltsIn_add (m := 16261314766416922089769436) (c₂ := ⟨0, 0, 0, 6775547819340384204070598, 14⟩)
    · have h := mod1_sn 1355109563868076840814119 12
      exact h
    apply stepNat_haltsIn_add (m := 27102191277361536816282394) (c₂ := ⟨0, 0, 0, 11292579698900640340117664, 13⟩)
    · have h := mod2_sn 2258515939780128068023532 13
      exact h
    apply stepNat_haltsIn_add (m := 45170318795602561360470658) (c₂ := ⟨0, 0, 0, 18820966164834400566862774, 12⟩)
    · have h := mod2_sn 3764193232966880113372554 12
      exact h
    apply stepNat_haltsIn_add (m := 75283864659337602267451100) (c₂ := ⟨0, 0, 0, 31368276941390667611437958, 13⟩)
    · have h := mod1_sn 6273655388278133522287591 11
      exact h
    apply stepNat_haltsIn_add (m := 125473107765562670445751834) (c₂ := ⟨0, 0, 0, 52280461568984446019063264, 12⟩)
    · have h := mod2_sn 10456092313796889203812652 12
      exact h
    apply stepNat_haltsIn_add (m := 209121846275937784076253058) (c₂ := ⟨0, 0, 0, 87134102614974076698438774, 11⟩)
    · have h := mod2_sn 17426820522994815339687754 11
      exact h
    apply stepNat_haltsIn_add (m := 348536410459896306793755099) (c₂ := ⟨0, 0, 0, 145223504358290127830731291, 11⟩)
    · have h := mod0_sn 29044700871658025566146258 10
      exact h
    apply stepNat_haltsIn_add (m := 580894017433160511322925168) (c₂ := ⟨0, 0, 0, 242039173930483546384552153, 12⟩)
    · have h := mod1_sn 48407834786096709276910430 10
      exact h
    apply stepNat_haltsIn_add (m := 968156695721934185538208616) (c₂ := ⟨0, 0, 0, 403398623217472577307586923, 13⟩)
    · have h := mod1_sn 80679724643494515461517384 11
      exact h
    apply stepNat_haltsIn_add (m := 1613594492869890309230347695) (c₂ := ⟨0, 0, 0, 672331038695787628845978206, 13⟩)
    · have h := mod0_sn 134466207739157525769195641 12
      exact h
    apply stepNat_haltsIn_add (m := 2689324154783150515383912826) (c₂ := ⟨0, 0, 0, 1120551731159646048076630344, 12⟩)
    · have h := mod2_sn 224110346231929209615326068 12
      exact h
    apply stepNat_haltsIn_add (m := 4482206924638584192306521379) (c₂ := ⟨0, 0, 0, 1867586218599410080127717241, 12⟩)
    · have h := mod0_sn 373517243719882016025543448 11
      exact h
    apply stepNat_haltsIn_add (m := 7470344874397640320510868967) (c₂ := ⟨0, 0, 0, 3112643697665683466879528736, 12⟩)
    · have h := mod0_sn 622528739533136693375905747 11
      exact h
    apply stepNat_haltsIn_add (m := 12450574790662733867518114947) (c₂ := ⟨0, 0, 0, 5187739496109472444799214561, 12⟩)
    · have h := mod0_sn 1037547899221894488959842912 11
      exact h
    apply stepNat_haltsIn_add (m := 20750957984437889779196858247) (c₂ := ⟨0, 0, 0, 8646232493515787407998690936, 12⟩)
    · have h := mod0_sn 1729246498703157481599738187 11
      exact h
    apply stepNat_haltsIn_add (m := 34584929974063149631994763747) (c₂ := ⟨0, 0, 0, 14410387489192979013331151561, 12⟩)
    · have h := mod0_sn 2882077497838595802666230312 11
      exact h
    apply stepNat_haltsIn_add (m := 57641549956771916053324606246) (c₂ := ⟨0, 0, 0, 24017312481988298355551919269, 11⟩)
    · have h := mod2_sn 4803462496397659671110383853 11
      exact h
    apply stepNat_haltsIn_add (m := 96069249927953193422207677078) (c₂ := ⟨0, 0, 0, 40028854136647163925919865449, 10⟩)
    · have h := mod2_sn 8005770827329432785183973089 10
      exact h
    apply stepNat_haltsIn_add (m := 160115416546588655703679461800) (c₂ := ⟨0, 0, 0, 66714756894411939876533109083, 11⟩)
    · have h := mod1_sn 13342951378882387975306621816 9
      exact h
    apply stepNat_haltsIn_add (m := 266859027577647759506132436334) (c₂ := ⟨0, 0, 0, 111191261490686566460888515139, 10⟩)
    · have h := mod2_sn 22238252298137313292177703027 10
      exact h
    apply stepNat_haltsIn_add (m := 444765045962746265843554060558) (c₂ := ⟨0, 0, 0, 185318769151144277434814191899, 9⟩)
    · have h := mod2_sn 37063753830228855486962838379 9
      exact h
    apply stepNat_haltsIn_add (m := 741275076604577109739256767599) (c₂ := ⟨0, 0, 0, 308864615251907129058023653166, 9⟩)
    · have h := mod0_sn 61772923050381425811604730633 8
      exact h
    apply stepNat_haltsIn_add (m := 1235458461007628516232094612666) (c₂ := ⟨0, 0, 0, 514774358753178548430039421944, 8⟩)
    · have h := mod2_sn 102954871750635709686007884388 8
      exact h
    apply stepNat_haltsIn_add (m := 2059097435012714193720157687779) (c₂ := ⟨0, 0, 0, 857957264588630914050065703241, 8⟩)
    · have h := mod0_sn 171591452917726182810013140648 7
      exact h
    apply stepNat_haltsIn_add (m := 3431829058354523656200262812968) (c₂ := ⟨0, 0, 0, 1429928774314384856750109505403, 9⟩)
    · have h := mod1_sn 285985754862876971350021901080 7
      exact h
    apply stepNat_haltsIn_add (m := 5719715097257539427000438021614) (c₂ := ⟨0, 0, 0, 2383214623857308094583515842339, 8⟩)
    · have h := mod2_sn 476642924771461618916703168467 8
      exact h
    apply stepNat_haltsIn_add (m := 9532858495429232378334063369358) (c₂ := ⟨0, 0, 0, 3972024373095513490972526403899, 7⟩)
    · have h := mod2_sn 794404874619102698194505280779 7
      exact h
    apply stepNat_haltsIn_add (m := 15888097492382053963890105615598) (c₂ := ⟨0, 0, 0, 6620040621825855818287544006499, 6⟩)
    · have h := mod2_sn 1324008124365171163657508801299 6
      exact h
    apply stepNat_haltsIn_add (m := 26480162487303423273150176025999) (c₂ := ⟨0, 0, 0, 11033401036376426363812573344166, 6⟩)
    · have h := mod0_sn 2206680207275285272762514668833 5
      exact h
    apply stepNat_haltsIn_add (m := 44133604145505705455250293376668) (c₂ := ⟨0, 0, 0, 18389001727294043939687622240278, 7⟩)
    · have h := mod1_sn 3677800345458808787937524448055 5
      exact h
    apply stepNat_haltsIn_add (m := 73556006909176175758750488961114) (c₂ := ⟨0, 0, 0, 30648336212156739899479370400464, 6⟩)
    · have h := mod2_sn 6129667242431347979895874080092 6
      exact h
    apply stepNat_haltsIn_add (m := 122593344848626959597917481601858) (c₂ := ⟨0, 0, 0, 51080560353594566499132284000774, 5⟩)
    · have h := mod2_sn 10216112070718913299826456800154 5
      exact h
    apply stepNat_haltsIn_add (m := 204322241414378265996529136003098) (c₂ := ⟨0, 0, 0, 85134267255990944165220473334624, 4⟩)
    · have h := mod2_sn 17026853451198188833044094666924 4
      exact h
    apply stepNat_haltsIn_add (m := 340537069023963776660881893338499) (c₂ := ⟨0, 0, 0, 141890445426651573608700788891041, 4⟩)
    · have h := mod0_sn 28378089085330314721740157778208 3
      exact h
    apply stepNat_haltsIn_add (m := 567561781706606294434803155564168) (c₂ := ⟨0, 0, 0, 236484075711085956014501314818403, 5⟩)
    · have h := mod1_sn 47296815142217191202900262963680 3
      exact h
    apply stepNat_haltsIn_add (m := 945936302844343824058005259273616) (c₂ := ⟨0, 0, 0, 394140126185143260024168858030673, 6⟩)
    · have h := mod1_sn 78828025237028652004833771606134 4
      exact h
    apply stepNat_haltsIn_add (m := 1576560504740573040096675432122696) (c₂ := ⟨0, 0, 0, 656900210308572100040281430051123, 7⟩)
    · have h := mod1_sn 131380042061714420008056286010224 5
      exact h
    apply stepNat_haltsIn_add (m := 2627600841234288400161125720204494) (c₂ := ⟨0, 0, 0, 1094833683847620166733802383418539, 6⟩)
    · have h := mod2_sn 218966736769524033346760476683707 6
      exact h
    apply stepNat_haltsIn_add (m := 4379334735390480666935209533674158) (c₂ := ⟨0, 0, 0, 1824722806412700277889670639030899, 5⟩)
    · have h := mod2_sn 364944561282540055577934127806179 5
      exact h
    apply stepNat_haltsIn_add (m := 7298891225650801111558682556123598) (c₂ := ⟨0, 0, 0, 3041204677354500463149451065051499, 4⟩)
    · have h := mod2_sn 608240935470900092629890213010299 4
      exact h
    apply stepNat_haltsIn_add (m := 12164818709418001852597804260206000) (c₂ := ⟨0, 0, 0, 5068674462257500771915751775085833, 5⟩)
    · have h := mod1_sn 1013734892451500154383150355017166 3
      exact h
    apply stepNat_haltsIn_add (m := 20274697849030003087663007100343335) (c₂ := ⟨0, 0, 0, 8447790770429167953192919625143056, 5⟩)
    · have h := mod0_sn 1689558154085833590638583925028611 4
      exact h
    apply stepNat_haltsIn_add (m := 33791163081716671812771678500572227) (c₂ := ⟨0, 0, 0, 14079651284048613255321532708571761, 5⟩)
    · have h := mod0_sn 2815930256809722651064306541714352 4
      exact h
    apply stepNat_haltsIn_add (m := 56318605136194453021286130834287048) (c₂ := ⟨0, 0, 0, 23466085473414355425535887847619603, 6⟩)
    · have h := mod1_sn 4693217094682871085107177569523920 4
      exact h
    apply stepNat_haltsIn_add (m := 93864341893657421702143551390478414) (c₂ := ⟨0, 0, 0, 39110142455690592375893146412699339, 5⟩)
    · have h := mod2_sn 7822028491138118475178629282539867 5
      exact h
    apply stepNat_haltsIn_add (m := 156440569822762369503572585650797358) (c₂ := ⟨0, 0, 0, 65183570759484320626488577354498899, 4⟩)
    · have h := mod2_sn 13036714151896864125297715470899779 4
      exact h
    apply stepNat_haltsIn_add (m := 260734283037937282505954309417995599) (c₂ := ⟨0, 0, 0, 108639284599140534377480962257498166, 4⟩)
    · have h := mod0_sn 21727856919828106875496192451499633 3
      exact h
    apply stepNat_haltsIn_add (m := 434557138396562137509923849029992668) (c₂ := ⟨0, 0, 0, 181065474331900890629134937095830278, 5⟩)
    · have h := mod1_sn 36213094866380178125826987419166055 3
      exact h
    apply stepNat_haltsIn_add (m := 724261897327603562516539748383321114) (c₂ := ⟨0, 0, 0, 301775790553168151048558228493050464, 4⟩)
    · have h := mod2_sn 60355158110633630209711645698610092 4
      exact h
    apply stepNat_haltsIn_add (m := 1207103162212672604194232913972201860) (c₂ := ⟨0, 0, 0, 502959650921946918414263714155084108, 5⟩)
    · have h := mod1_sn 100591930184389383682852742831016821 3
      exact h
    apply stepNat_haltsIn_add (m := 2011838603687787673657054856620336436) (c₂ := ⟨0, 0, 0, 838266084869911530690439523591806848, 6⟩)
    · have h := mod1_sn 167653216973982306138087904718361369 4
      exact h
    apply stepNat_haltsIn_add (m := 3353064339479646122761758094367227395) (c₂ := ⟨0, 0, 0, 1397110141449852551150732539319678081, 6⟩)
    · have h := mod0_sn 279422028289970510230146507863935616 5
      exact h
    apply stepNat_haltsIn_add (m := 5588440565799410204602930157278712326) (c₂ := ⟨0, 0, 0, 2328516902416420918584554232199463469, 5⟩)
    · have h := mod2_sn 465703380483284183716910846439892693 5
      exact h
    apply stepNat_haltsIn_add (m := 9314067609665683674338216928797853879) (c₂ := ⟨0, 0, 0, 3880861504027368197640923720332439116, 5⟩)
    · have h := mod0_sn 776172300805473639528184744066487823 4
      exact h
    apply stepNat_haltsIn_add (m := 15523446016109472790563694881329756468) (c₂ := ⟨0, 0, 0, 6468102506712280329401539533887398528, 6⟩)
    · have h := mod1_sn 1293620501342456065880307906777479705 4
      exact h
    apply stepNat_haltsIn_add (m := 25872410026849121317606158135549594116) (c₂ := ⟨0, 0, 0, 10780170844520467215669232556478997548, 7⟩)
    · have h := mod1_sn 2156034168904093443133846511295799509 5
      exact h
    apply stepNat_haltsIn_add (m := 43120683378081868862676930225915990195) (c₂ := ⟨0, 0, 0, 17966951407534112026115387594131662581, 7⟩)
    · have h := mod0_sn 3593390281506822405223077518826332516 6
      exact h
    apply stepNat_haltsIn_add (m := 71867805630136448104461550376526650326) (c₂ := ⟨0, 0, 0, 29944919012556853376858979323552770969, 6⟩)
    · have h := mod2_sn 5988983802511370675371795864710554193 6
      exact h
    apply stepNat_haltsIn_add (m := 119779676050227413507435917294211083880) (c₂ := ⟨0, 0, 0, 49908198354261422294764965539254618283, 7⟩)
    · have h := mod1_sn 9981639670852284458952993107850923656 5
      exact h
    apply stepNat_haltsIn_add (m := 199632793417045689179059862157018473134) (c₂ := ⟨0, 0, 0, 83180330590435703824608275898757697139, 6⟩)
    · have h := mod2_sn 16636066118087140764921655179751539427 6
      exact h
    apply stepNat_haltsIn_add (m := 332721322361742815298433103595030788559) (c₂ := ⟨0, 0, 0, 138633884317392839707680459831262828566, 6⟩)
    · have h := mod0_sn 27726776863478567941536091966252565713 5
      exact h
    apply stepNat_haltsIn_add (m := 554535537269571358830721839325051314267) (c₂ := ⟨0, 0, 0, 231056473862321399512800766385438047611, 6⟩)
    · have h := mod0_sn 46211294772464279902560153277087609522 5
      exact h
    apply stepNat_haltsIn_add (m := 924225895449285598051203065541752190447) (c₂ := ⟨0, 0, 0, 385094123103868999188001277309063412686, 6⟩)
    · have h := mod0_sn 77018824620773799837600255461812682537 5
      exact h
    apply stepNat_haltsIn_add (m := 1540376492415475996752005109236253650746) (c₂ := ⟨0, 0, 0, 641823538506448331980002128848439021144, 5⟩)
    · have h := mod2_sn 128364707701289666396000425769687804228 5
      exact h
    apply stepNat_haltsIn_add (m := 2567294154025793327920008515393756084578) (c₂ := ⟨0, 0, 0, 1069705897510747219966670214747398368574, 4⟩)
    · have h := mod2_sn 213941179502149443993334042949479673714 4
      exact h
    apply stepNat_haltsIn_add (m := 4278823590042988879866680858989593474298) (c₂ := ⟨0, 0, 0, 1782843162517912033277783691245663947624, 3⟩)
    · have h := mod2_sn 356568632503582406655556738249132789524 3
      exact h
    apply stepNat_haltsIn_add (m := 7131372650071648133111134764982655790500) (c₂ := ⟨0, 0, 0, 2971405270863186722129639485409439912708, 4⟩)
    · have h := mod1_sn 594281054172637344425927897081887982541 2
      exact h
    apply stepNat_haltsIn_add (m := 11885621083452746888518557941637759650835) (c₂ := ⟨0, 0, 0, 4952342118105311203549399142349066521181, 4⟩)
    · have h := mod0_sn 990468423621062240709879828469813304236 3
      exact h
    apply stepNat_haltsIn_add (m := 19809368472421244814197596569396266084727) (c₂ := ⟨0, 0, 0, 8253903530175518672582331903915110868636, 4⟩)
    · have h := mod0_sn 1650780706035103734516466380783022173727 3
      exact h
    apply stepNat_haltsIn_add (m := 33015614120702074690329327615660443474547) (c₂ := ⟨0, 0, 0, 13756505883625864454303886506525184781061, 4⟩)
    · have h := mod0_sn 2751301176725172890860777301305036956212 3
      exact h
    apply stepNat_haltsIn_add (m := 55026023534503457817215546026100739124246) (c₂ := ⟨0, 0, 0, 22927509806043107423839810844208641301769, 3⟩)
    · have h := mod2_sn 4585501961208621484767962168841728260353 3
      exact h
    apply stepNat_haltsIn_add (m := 91710039224172429695359243376834565207080) (c₂ := ⟨0, 0, 0, 38212516343405179039733018073681068836283, 4⟩)
    · have h := mod1_sn 7642503268681035807946603614736213767256 2
      exact h
    apply stepNat_haltsIn_add (m := 152850065373620716158932072294724275345134) (c₂ := ⟨0, 0, 0, 63687527239008631732888363456135114727139, 3⟩)
    · have h := mod2_sn 12737505447801726346577672691227022945427 3
      exact h
    apply stepNat_haltsIn_add (m := 254750108956034526931553453824540458908559) (c₂ := ⟨0, 0, 0, 106145878731681052888147272426891857878566, 3⟩)
    · have h := mod0_sn 21229175746336210577629454485378371575713 2
      exact h
    apply stepNat_haltsIn_add (m := 424583514926724211552589089707567431514267) (c₂ := ⟨0, 0, 0, 176909797886135088146912120711486429797611, 3⟩)
    · have h := mod0_sn 35381959577227017629382424142297285959522 2
      exact h
    apply stepNat_haltsIn_add (m := 707639191544540352587648482845945719190447) (c₂ := ⟨0, 0, 0, 294849663143558480244853534519144049662686, 3⟩)
    · have h := mod0_sn 58969932628711696048970706903828809932537 2
      exact h
    apply stepNat_haltsIn_add (m := 1179398652574233920979414138076576198650747) (c₂ := ⟨0, 0, 0, 491416105239264133741422557531906749437811, 3⟩)
    · have h := mod0_sn 98283221047852826748284511506381349887562 2
      exact h
    apply stepNat_haltsIn_add (m := 1965664420957056534965690230127626997751248) (c₂ := ⟨0, 0, 0, 819026842065440222902370929219844582396353, 4⟩)
    · have h := mod1_sn 163805368413088044580474185843968916479270 2
      exact h
    apply stepNat_haltsIn_add (m := 3276107368261760891609483716879378329585416) (c₂ := ⟨0, 0, 0, 1365044736775733704837284882033074303993923, 5⟩)
    · have h := mod1_sn 273008947355146740967456976406614860798784 3
      exact h
    apply stepNat_haltsIn_add (m := 5460178947102934819349139528132297215975696) (c₂ := ⟨0, 0, 0, 2275074561292889508062141470055123839989873, 6⟩)
    · have h := mod1_sn 455014912258577901612428294011024767997974 4
      exact h
    apply stepNat_haltsIn_add (m := 9100298245171558032248565880220495359959495) (c₂ := ⟨0, 0, 0, 3791790935488149180103569116758539733316456, 6⟩)
    · have h := mod0_sn 758358187097629836020713823351707946663291 5
      exact h
    apply stepNat_haltsIn_add (m := 15167163741952596720414276467034158933265826) (c₂ := ⟨0, 0, 0, 6319651559146915300172615194597566222194094, 5⟩)
    · have h := mod2_sn 1263930311829383060034523038919513244438818 5
      exact h
    apply stepNat_haltsIn_add (m := 25278606236587661200690460778390264888776379) (c₂ := ⟨0, 0, 0, 10532752598578192166954358657662610370323491, 5⟩)
    · have h := mod0_sn 2106550519715638433390871731532522074064698 4
      exact h
    apply stepNat_haltsIn_add (m := 42131010394312768667817434630650441481293966) (c₂ := ⟨0, 0, 0, 17554587664296986944923931096104350617205819, 4⟩)
    · have h := mod2_sn 3510917532859397388984786219220870123441163 4
      exact h
    apply stepNat_haltsIn_add (m := 70218350657187947779695724384417402468823278) (c₂ := ⟨0, 0, 0, 29257646107161644908206551826840584362009699, 3⟩)
    · have h := mod2_sn 5851529221432328981641310365368116872401939 3
      exact h
    apply stepNat_haltsIn_add (m := 117030584428646579632826207307362337448038800) (c₂ := ⟨0, 0, 0, 48762743511936074847010919711400973936682833, 4⟩)
    · have h := mod1_sn 9752548702387214969402183942280194787336566 2
      exact h
    apply stepNat_haltsIn_add (m := 195050974047744299388043678845603895746731336) (c₂ := ⟨0, 0, 0, 81271239186560124745018199519001623227804723, 5⟩)
    · have h := mod1_sn 16254247837312024949003639903800324645560944 3
      exact h
    apply stepNat_haltsIn_add (m := 325084956746240498980072798076006492911218896) (c₂ := ⟨0, 0, 0, 135452065310933541241696999198336038713007873, 6⟩)
    · have h := mod1_sn 27090413062186708248339399839667207742601574 4
      exact h
    apply stepNat_haltsIn_add (m := 541808261243734164966787996793344154852031495) (c₂ := ⟨0, 0, 0, 225753442184889235402828331997226731188346456, 6⟩)
    · have h := mod0_sn 45150688436977847080565666399445346237669291 5
      exact h
    apply stepNat_haltsIn_add (m := 903013768739556941611313327988906924753385827) (c₂ := ⟨0, 0, 0, 376255736974815392338047219995377885313910761, 6⟩)
    · have h := mod0_sn 75251147394963078467609443999075577062782152 5
      exact h
    apply stepNat_haltsIn_add (m := 1505022947899261569352188879981511541255643046) (c₂ := ⟨0, 0, 0, 627092894958025653896745366658963142189851269, 5⟩)
    · have h := mod2_sn 125418578991605130779349073331792628437970253 5
      exact h
    apply stepNat_haltsIn_add (m := 2508371579832102615586981466635852568759405079) (c₂ := ⟨0, 0, 0, 1045154824930042756494575611098271903649752116, 5⟩)
    · have h := mod0_sn 209030964986008551298915122219654380729950423 4
      exact h
    apply stepNat_haltsIn_add (m := 4180619299720171025978302444393087614599008467) (c₂ := ⟨0, 0, 0, 1741924708216737927490959351830453172749586861, 5⟩)
    · have h := mod0_sn 348384941643347585498191870366090634549917372 4
      exact h
    apply stepNat_haltsIn_add (m := 6967698832866951709963837407321812690998347447) (c₂ := ⟨0, 0, 0, 2903207847027896545818265586384088621249311436, 5⟩)
    · have h := mod0_sn 580641569405579309163653117276817724249862287 4
      exact h
    apply stepNat_haltsIn_add (m := 11612831388111586183273062345536354484997245747) (c₂ := ⟨0, 0, 0, 4838679745046494243030442643973481035415519061, 5⟩)
    · have h := mod0_sn 967735949009298848606088528794696207083103812 4
      exact h
    apply stepNat_haltsIn_add (m := 19354718980185976972121770575893924141662076247) (c₂ := ⟨0, 0, 0, 8064466241744157071717404406622468392359198436, 5⟩)
    · have h := mod0_sn 1612893248348831414343480881324493678471839687 4
      exact h
    apply stepNat_haltsIn_add (m := 32257864966976628286869617626489873569436793746) (c₂ := ⟨0, 0, 0, 13440777069573595119529007344370780653931997394, 4⟩)
    · have h := mod2_sn 2688155413914719023905801468874156130786399478 4
      exact h
    apply stepNat_haltsIn_add (m := 53763108278294380478116029377483122615727989580) (c₂ := ⟨0, 0, 0, 22401295115955991865881678907284634423219995658, 5⟩)
    · have h := mod1_sn 4480259023191198373176335781456926884643999131 3
      exact h
    apply stepNat_haltsIn_add (m := 89605180463823967463526715629138537692879982634) (c₂ := ⟨0, 0, 0, 37335491859926653109802798178807724038699992764, 4⟩)
    · have h := mod2_sn 7467098371985330621960559635761544807739998552 4
      exact h
    apply stepNat_haltsIn_add (m := 149341967439706612439211192715230896154799971058) (c₂ := ⟨0, 0, 0, 62225819766544421849671330298012873397833321274, 3⟩)
    · have h := mod2_sn 12445163953308884369934266059602574679566664254 3
      exact h
    apply stepNat_haltsIn_add (m := 248903279066177687398685321192051493591333285099) (c₂ := ⟨0, 0, 0, 103709699610907369749452217163354788996388868791, 3⟩)
    · have h := mod0_sn 20741939922181473949890443432670957799277773758 2
      exact h
    apply stepNat_haltsIn_add (m := 414838798443629478997808868653419155985555475168) (c₂ := ⟨0, 0, 0, 172849499351512282915753695272257981660648114653, 4⟩)
    · have h := mod1_sn 34569899870302456583150739054451596332129622930 2
      exact h
    apply stepNat_haltsIn_add (m := 691397997406049131663014781089031926642592458615) (c₂ := ⟨0, 0, 0, 288082498919187138192922825453763302767746857756, 4⟩)
    · have h := mod0_sn 57616499783837427638584565090752660553549371551 3
      exact h
    apply stepNat_haltsIn_add (m := 1152329995676748552771691301815053211070987431028) (c₂ := ⟨0, 0, 0, 480137498198645230321538042422938837946244762928, 5⟩)
    · have h := mod1_sn 96027499639729046064307608484587767589248952585 3
      exact h
    apply stepNat_haltsIn_add (m := 1920549992794580921286152169691755351784979051715) (c₂ := ⟨0, 0, 0, 800229163664408717202563404038231396577074604881, 5⟩)
    · have h := mod0_sn 160045832732881743440512680807646279315414920976 4
      exact h
    apply stepNat_haltsIn_add (m := 3200916654657634868810253616152925586308298419527) (c₂ := ⟨0, 0, 0, 1333715272774014528670939006730385660961791008136, 5⟩)
    · have h := mod0_sn 266743054554802905734187801346077132192358201627 4
      exact h
    apply stepNat_haltsIn_add (m := 5334861091096058114683756026921542643847164032547) (c₂ := ⟨0, 0, 0, 2222858787956690881118231677883976101602985013561, 5⟩)
    · have h := mod0_sn 444571757591338176223646335576795220320597002712 4
      exact h
    apply stepNat_haltsIn_add (m := 8891435151826763524472926711535904406411940054247) (c₂ := ⟨0, 0, 0, 3704764646594484801863719463139960169338308355936, 5⟩)
    · have h := mod0_sn 740952929318896960372743892627992033867661671187 4
      exact h
    apply stepNat_haltsIn_add (m := 14819058586377939207454877852559840677353233423747) (c₂ := ⟨0, 0, 0, 6174607744324141336439532438566600282230513926561, 5⟩)
    · have h := mod0_sn 1234921548864828267287906487713320056446102785312 4
      exact h
    apply stepNat_haltsIn_add (m := 24698430977296565345758129754266401128922055706247) (c₂ := ⟨0, 0, 0, 10291012907206902227399220730944333803717523210936, 5⟩)
    · have h := mod0_sn 2058202581441380445479844146188866760743504642187 4
      exact h
    apply stepNat_haltsIn_add (m := 41164051628827608909596882923777335214870092843747) (c₂ := ⟨0, 0, 0, 17151688178678170378998701218240556339529205351561, 5⟩)
    · have h := mod0_sn 3430337635735634075799740243648111267905841070312 4
      exact h
    apply stepNat_haltsIn_add (m := 68606752714712681515994804872962225358116821406248) (c₂ := ⟨0, 0, 0, 28586146964463617298331168697067593899215342252603, 6⟩)
    · have h := mod1_sn 5717229392892723459666233739413518779843068450520 4
      exact h
    apply stepNat_haltsIn_add (m := 114344587857854469193324674788270375596861369010415) (c₂ := ⟨0, 0, 0, 47643578274106028830551947828445989832025570421006, 6⟩)
    · have h := mod0_sn 9528715654821205766110389565689197966405114084201 5
      exact h
    apply stepNat_haltsIn_add (m := 190574313096424115322207791313783959328102281684026) (c₂ := ⟨0, 0, 0, 79405963790176714717586579714076649720042617368344, 5⟩)
    · have h := mod2_sn 15881192758035342943517315942815329944008523473668 5
      exact h
    apply stepNat_haltsIn_add (m := 317623855160706858870346318856306598880170469473380) (c₂ := ⟨0, 0, 0, 132343272983627857862644299523461082866737695613908, 6⟩)
    · have h := mod1_sn 26468654596725571572528859904692216573347539122781 4
      exact h
    apply stepNat_haltsIn_add (m := 529373091934511431450577198093844331466950782455636) (c₂ := ⟨0, 0, 0, 220572121639379763104407165872435138111229492689848, 7⟩)
    · have h := mod1_sn 44114424327875952620881433174487027622245898537969 5
      exact h
    apply stepNat_haltsIn_add (m := 882288486557519052417628663489740552444917970759394) (c₂ := ⟨0, 0, 0, 367620202732299605174011943120725230185382487816414, 6⟩)
    · have h := mod2_sn 73524040546459921034802388624145046037076497563282 6
      exact h
    apply stepNat_haltsIn_add (m := 1470480810929198420696047772482900920741529951265660) (c₂ := ⟨0, 0, 0, 612700337887166008623353238534542050308970813027358, 7⟩)
    · have h := mod1_sn 122540067577433201724670647706908410061794162605471 5
      exact h
    apply stepNat_haltsIn_add (m := 2450801351548664034493412954138168201235883252109434) (c₂ := ⟨0, 0, 0, 1021167229811943347705588730890903417181618021712264, 6⟩)
    · have h := mod2_sn 204233445962388669541117746178180683436323604342452 6
      exact h
    apply stepNat_haltsIn_add (m := 4084668919247773390822354923563613668726472086849060) (c₂ := ⟨0, 0, 0, 1701945383019905579509314551484839028636030036187108, 7⟩)
    · have h := mod1_sn 340389076603981115901862910296967805727206007237421 5
      exact h
    apply stepNat_haltsIn_add (m := 6807781532079622318037258205939356114544120144748436) (c₂ := ⟨0, 0, 0, 2836575638366509299182190919141398381060050060311848, 8⟩)
    · have h := mod1_sn 567315127673301859836438183828279676212010012062369 6
      exact h
    apply stepNat_haltsIn_add (m := 11346302553466037196728763676565593524240200241247395) (c₂ := ⟨0, 0, 0, 4727626063944182165303651531902330635100083433853081, 8⟩)
    · have h := mod0_sn 945525212788836433060730306380466127020016686770616 7
      exact h
    apply stepNat_haltsIn_add (m := 18910504255776728661214606127609322540400333735412326) (c₂ := ⟨0, 0, 0, 7879376773240303608839419219837217725166805723088469, 7⟩)
    · have h := mod2_sn 1575875354648060721767883843967443545033361144617693 7
      exact h
    apply stepNat_haltsIn_add (m := 31517507092961214435357676879348870900667222892353878) (c₂ := ⟨0, 0, 0, 13132294622067172681399032033062029541944676205147449, 6⟩)
    · have h := mod2_sn 2626458924413434536279806406612405908388935241029489 6
      exact h
    apply stepNat_haltsIn_add (m := 52529178488268690725596128132248118167778704820589798) (c₂ := ⟨0, 0, 0, 21887157703445287802331720055103382569907793675245749, 5⟩)
    · have h := mod2_sn 4377431540689057560466344011020676513981558735049149 5
      exact h
    apply stepNat_haltsIn_add (m := 87548630813781151209326880220413530279631174700982998) (c₂ := ⟨0, 0, 0, 36478596172408813003886200091838970949846322792076249, 4⟩)
    · have h := mod2_sn 7295719234481762600777240018367794189969264558415249 4
      exact h
    apply stepNat_haltsIn_add (m := 145914384689635252015544800367355883799385291168305000) (c₂ := ⟨0, 0, 0, 60797660287348021673143666819731618249743871320127083, 5⟩)
    · have h := mod1_sn 12159532057469604334628733363946323649948774264025416 3
      exact h
    apply stepNat_haltsIn_add (m := 243190641149392086692574667278926472998975485280508334) (c₂ := ⟨0, 0, 0, 101329433812246702788572778032886030416239785533545139, 4⟩)
    · have h := mod2_sn 20265886762449340557714555606577206083247957106709027 4
      exact h
    apply stepNat_haltsIn_add (m := 405317735248986811154291112131544121664959142134180558) (c₂ := ⟨0, 0, 0, 168882389687077837980954630054810050693732975889241899, 3⟩)
    · have h := mod2_sn 33776477937415567596190926010962010138746595177848379 3
      exact h
    apply stepNat_haltsIn_add (m := 675529558748311351923818520219240202774931903556967599) (c₂ := ⟨0, 0, 0, 281470649478463063301591050091350084489554959815403166, 3⟩)
    · have h := mod0_sn 56294129895692612660318210018270016897910991963080633 2
      exact h
    apply stepNat_haltsIn_add (m := 1125882597913852253206364200365400337958219839261612667) (c₂ := ⟨0, 0, 0, 469117749130771772169318416818916807482591599692338611, 3⟩)
    · have h := mod0_sn 93823549826154354433863683363783361496518319938467722 2
      exact h
    apply stepNat_haltsIn_add (m := 1876470996523087088677273667275667229930366398769354447) (c₂ := ⟨0, 0, 0, 781862915217952953615530694698194679137652666153897686, 3⟩)
    · have h := mod0_sn 156372583043590590723106138939638935827530533230779537 2
      exact h
    apply stepNat_haltsIn_add (m := 3127451660871811814462122778792778716550610664615590748) (c₂ := ⟨0, 0, 0, 1303104858696588256025884491163657798562754443589829478, 4⟩)
    · have h := mod1_sn 260620971739317651205176898232731559712550888717965895 2
      exact h
    apply stepNat_haltsIn_add (m := 5212419434786353024103537964654631194251017774359317914) (c₂ := ⟨0, 0, 0, 2171841431160980426709807485272762997604590739316382464, 3⟩)
    · have h := mod2_sn 434368286232196085341961497054552599520918147863276492 3
      exact h
    apply stepNat_haltsIn_add (m := 8687365724643921706839229941091051990418362957265529860) (c₂ := ⟨0, 0, 0, 3619735718601634044516345808787938329340984565527304108, 4⟩)
    · have h := mod1_sn 723947143720326808903269161757587665868196913105460821 2
      exact h
    apply stepNat_haltsIn_add (m := 14478942874406536178065383235151753317363938262109216434) (c₂ := ⟨0, 0, 0, 6032892864336056740860576347979897215568307609212173514, 3⟩)
    · have h := mod2_sn 1206578572867211348172115269595979443113661521842434702 3
      exact h
    apply stepNat_haltsIn_add (m := 24131571457344226963442305391919588862273230436848694059) (c₂ := ⟨0, 0, 0, 10054821440560094568100960579966495359280512682020289191, 3⟩)
    · have h := mod0_sn 2010964288112018913620192115993299071856102536404057838 2
      exact h
    apply stepNat_haltsIn_add (m := 40219285762240378272403842319865981437122050728081156767) (c₂ := ⟨0, 0, 0, 16758035734266824280168267633277492265467521136700481986, 3⟩)
    · have h := mod0_sn 3351607146853364856033653526655498453093504227340096397 2
      exact h
    apply stepNat_haltsIn_add (m := 67032142937067297120673070533109969061870084546801927946) (c₂ := ⟨0, 0, 0, 27930059557111373800280446055462487109112535227834136644, 2⟩)
    · have h := mod2_sn 5586011911422274760056089211092497421822507045566827328 2
      exact h
    apply stepNat_haltsIn_add (m := 111720238228445495201121784221849948436450140911336546578) (c₂ := ⟨0, 0, 0, 46550099261852289667134076759104145181854225379723561074, 1⟩)
    · have h := mod2_sn 9310019852370457933426815351820829036370845075944712214 1
      exact h
    apply stepNat_haltsIn_add (m := 186200397047409158668536307036416580727416901518894244300) (c₂ := ⟨0, 0, 0, 77583498769753816111890127931840241969757042299539268458, 2⟩)
    · have h := mod1_sn 15516699753950763222378025586368048393951408459907853691 0
      exact h
    apply stepNat_haltsIn_add (m := 310333995079015264447560511727360967879028169198157073834) (c₂ := ⟨0, 0, 0, 129305831282923026853150213219733736616261737165898780764, 1⟩)
    · have h := mod2_sn 25861166256584605370630042643946747323252347433179756152 1
      exact h
    apply stepNat_haltsIn_add (m := 517223325131692107412600852878934946465046948663595123059) (c₂ := ⟨0, 0, 0, 215509718804871711421917022032889561027102895276497967941, 1⟩)
    · have h := mod0_sn 43101943760974342284383404406577912205420579055299593588 0
      exact h
    apply stepNat_haltsIn_add (m := 862038875219486845687668088131558244108411581105991871768) (c₂ := ⟨0, 0, 0, 359182864674786185703195036721482601711838158794163279903, 2⟩)
    · have h := mod1_sn 71836572934957237140639007344296520342367631758832655980 0
      exact h
    apply stepNat_haltsIn_add (m := 1436731458699144742812780146885930406847352635176653119616) (c₂ := ⟨0, 0, 0, 598638107791310309505325061202471002853063597990272133173, 3⟩)
    · have h := mod1_sn 119727621558262061901065012240494200570612719598054426634 1
      exact h
    apply stepNat_haltsIn_add (m := 2394552431165241238021300244809884011412254391961088532694) (c₂ := ⟨0, 0, 0, 997730179652183849175541768670785004755105996650453555289, 2⟩)
    · have h := mod2_sn 199546035930436769835108353734157000951021199330090711057 2
      exact h
    apply stepNat_haltsIn_add (m := 3990920718608735396702167074683140019020423986601814221160) (c₂ := ⟨0, 0, 0, 1662883632753639748625902947784641674591843327750755925483, 3⟩)
    · have h := mod1_sn 332576726550727949725180589556928334918368665550151185096 1
      exact h
    apply stepNat_haltsIn_add (m := 6651534531014558994503611791138566698367373311003023701934) (c₂ := ⟨0, 0, 0, 2771472721256066247709838246307736124319738879584593209139, 2⟩)
    · have h := mod2_sn 554294544251213249541967649261547224863947775916918641827 2
      exact h
    apply stepNat_haltsIn_add (m := 11085890885024264990839352985230944497278955518338372836560) (c₂ := ⟨0, 0, 0, 4619121202093443746183063743846226873866231465974322015233, 3⟩)
    · have h := mod1_sn 923824240418688749236612748769245374773246293194864403046 1
      exact h
    apply stepNat_haltsIn_add (m := 18476484808373774984732254975384907495464925863897288060935) (c₂ := ⟨0, 0, 0, 7698535336822406243638439573077044789777052443290536692056, 3⟩)
    · have h := mod0_sn 1539707067364481248727687914615408957955410488658107338411 2
      exact h
    apply stepNat_haltsIn_add (m := 30794141347289624974553758292308179159108209773162146768226) (c₂ := ⟨0, 0, 0, 12830892228037343739397399288461741316295087405484227820094, 2⟩)
    · have h := mod2_sn 2566178445607468747879479857692348263259017481096845564018 2
      exact h
    apply stepNat_haltsIn_add (m := 51323568912149374957589597153846965265180349621936911280380) (c₂ := ⟨0, 0, 0, 21384820380062239565662332147436235527158479009140379700158, 3⟩)
    · have h := mod1_sn 4276964076012447913132466429487247105431695801828075940031 1
      exact h
    apply stepNat_haltsIn_add (m := 85539281520248958262649328589744942108633916036561518800634) (c₂ := ⟨0, 0, 0, 35641367300103732609437220245727059211930798348567299500264, 2⟩)
    · have h := mod2_sn 7128273460020746521887444049145411842386159669713459900052 2
      exact h
    apply stepNat_haltsIn_add (m := 142565469200414930437748880982908236847723193394269198001060) (c₂ := ⟨0, 0, 0, 59402278833506221015728700409545098686551330580945499167108, 3⟩)
    · have h := mod1_sn 11880455766701244203145740081909019737310266116189099833421 1
      exact h
    apply stepNat_haltsIn_add (m := 237609115334024884062914801638180394746205322323781996668434) (c₂ := ⟨0, 0, 0, 99003798055843701692881167349241831144252217634909165278514, 2⟩)
    · have h := mod2_sn 19800759611168740338576233469848366228850443526981833055702 2
      exact h
    apply stepNat_haltsIn_add (m := 396015192223374806771524669396967324577008870539636661114060) (c₂ := ⟨0, 0, 0, 165006330093072836154801945582069718573753696058181942130858, 3⟩)
    · have h := mod1_sn 33001266018614567230960389116413943714750739211636388426171 1
      exact h
    apply stepNat_haltsIn_add (m := 660025320372291344619207782328278874295014784232727768523436) (c₂ := ⟨0, 0, 0, 275010550155121393591336575970116197622922826763636570218098, 4⟩)
    · have h := mod1_sn 55002110031024278718267315194023239524584565352727314043619 2
      exact h
    apply stepNat_haltsIn_add (m := 1100042200620485574365346303880464790491691307054546280872396) (c₂ := ⟨0, 0, 0, 458350916925202322652227626616860329371538044606060950363498, 5⟩)
    · have h := mod1_sn 91670183385040464530445525323372065874307608921212190072699 3
      exact h
    apply stepNat_haltsIn_add (m := 1833403667700809290608910506467441317486152178424243801453996) (c₂ := ⟨0, 0, 0, 763918194875337204420379377694767215619230074343434917272498, 6⟩)
    · have h := mod1_sn 152783638975067440884075875538953443123846014868686983454499 4
      exact h
    apply stepNat_haltsIn_add (m := 3055672779501348817681517510779068862476920297373739669089994) (c₂ := ⟨0, 0, 0, 1273196991458895340700632296157945359365383457239058195454164, 5⟩)
    · have h := mod2_sn 254639398291779068140126459231589071873076691447811639090832 5
      exact h
    apply stepNat_haltsIn_add (m := 5092787965835581362802529184631781437461533828956232781816658) (c₂ := ⟨0, 0, 0, 2121994985764825567834387160263242265608972428731763659090274, 4⟩)
    · have h := mod2_sn 424398997152965113566877432052648453121794485746352731818054 4
      exact h
    apply stepNat_haltsIn_add (m := 8487979943059302271337548641052969062435889714927054636361098) (c₂ := ⟨0, 0, 0, 3536658309608042613057311933772070442681620714552939431817124, 3⟩)
    · have h := mod2_sn 707331661921608522611462386754414088536324142910587886363424 3
      exact h
    apply stepNat_haltsIn_add (m := 14146633238432170452229247735088281770726482858211757727268498) (c₂ := ⟨0, 0, 0, 5894430516013404355095519889620117404469367857588232386361874, 2⟩)
    · have h := mod2_sn 1178886103202680871019103977924023480893873571517646477272374 2
      exact h
    apply stepNat_haltsIn_add (m := 23577722064053617420382079558480469617877471430352929545447498) (c₂ := ⟨0, 0, 0, 9824050860022340591825866482700195674115613095980387310603124, 1⟩)
    · have h := mod2_sn 1964810172004468118365173296540039134823122619196077462120624 1
      exact h
    apply stepNat_haltsIn_add (m := 39296203440089362367303465930800782696462452383921549242412498) (c₂ := ⟨0, 0, 0, 16373418100037234319709777471166992790192688493300645517671874, 0⟩)
    · have h := mod2_sn 3274683620007446863941955494233398558038537698660129103534374 0
      exact h
    exact halt_sn 16373418100037234319709777471166992790192688493300645517671874
