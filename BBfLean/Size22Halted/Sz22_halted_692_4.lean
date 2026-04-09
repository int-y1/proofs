import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_halted_692 #4: [9/35, 1/75, 55/3, 2/5, 7/11, 3/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1 -2  0  0
 0 -1  1  0  1
 1  0 -1  0  0
 0  0  0  1 -1
-1  1  0  0  0
```

This Fractran program halts in 114613926700260640237968442298168949531348819453104518623702294 steps.

Author: Claude
-/

namespace Sz22_halted_692_4

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+2, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

private theorem r5_sn : ∀ k a d e, (⟨a, 0, 0, d, e + k⟩ : Q) [fm]⊢^{k} ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · simp; rfl
  rw [show e + (k + 1) = (e + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨a, 0, 0, d, (e + k) + 1⟩ = some ⟨a, 0, 0, d + 1, e + k⟩; rfl
  have h := ih a (d + 1) e; rw [show (d + 1) + k = d + (1 + k) from by ring] at h; exact h

private theorem r31_sn : ∀ k, ∀ a b d e, (⟨a, b + 1, 0, d + k, e⟩ : Q) [fm]⊢^{2 * k} ⟨a, b + k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · simp; rfl
  rw [show d + (k + 1) = (d + k) + 1 from by ring, show 2 * (k + 1) = 2 + 2 * k from by ring]
  apply stepNat_trans 2 (2 * k)
  · show stepNat fm 2 ⟨a, b + 1, 0, (d + k) + 1, e⟩ = some ⟨a, b + 2, 0, d + k, e + 1⟩; rfl
  have h := ih a (b + 1) d (e + 1)
  rw [show (b + 1) + k + 1 = b + (k + 1) + 1 from by ring,
    show (e + 1) + k = e + (k + 1) from by ring] at h
  rw [show b + 2 = (b + 1) + 1 from by ring]; exact h

private theorem drain_sn : ∀ k, ∀ a b e, (⟨a, b + 3 * k, 0, 0, e⟩ : Q) [fm]⊢^{3 * k} ⟨a, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · simp; rfl
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring, show 3 * (k + 1) = 3 + 3 * k from by ring]
  apply stepNat_trans 3 (3 * k)
  · show stepNat fm 3 ⟨a, (b + 3 * k) + 3, 0, 0, e⟩ = some ⟨a, b + 3 * k, 0, 0, e + 2⟩; rfl
  have h := ih a b (e + 2); rw [show (e + 2) + 2 * k = e + 2 * (k + 1) from by ring] at h; exact h

private theorem tail1_sn : ∀ a e, (⟨a, 1, 0, 0, e⟩ : Q) [fm]⊢^{2} ⟨a + 1, 0, 0, 0, e + 1⟩ := by
  intro a e; rfl

private theorem tail2_sn : ∀ a e, (⟨a, 2, 0, 0, e⟩ : Q) [fm]⊢^{4} ⟨a + 2, 0, 0, 0, e + 2⟩ := by
  intro a e; rfl

private theorem halt_sn : ∀ D, haltsIn fm (⟨0, 0, 0, D, 0⟩ : Q) 0 := by
  intro D; refine ⟨⟨0, 0, 0, D, 0⟩, ?_, rfl⟩; rfl

private theorem mod0_sn : ∀ k A, (⟨A + 1, 0, 0, 3 * k, 0⟩ : Q) [fm]⊢^{14 * k + 4} ⟨A + 1, 0, 0, 5 * k + 1, 0⟩ := by
  intro k A
  have h1 : (⟨A + 1, 0, 0, 3 * k, 0⟩ : Q) [fm]⊢^{1} ⟨A, 1, 0, 3 * k, 0⟩ := rfl
  have h2 := r31_sn (3 * k) A 0 0 0
  simp only [Nat.zero_add] at h2
  rw [show 3 * k + 1 = 1 + 3 * k from by ring] at h2
  have h3 := drain_sn k A 1 (3 * k)
  rw [show 3 * k + 2 * k = 5 * k from by ring] at h3
  have h4 := tail1_sn A (5 * k)
  have h5 := r5_sn (5 * k + 1) (A + 1) 0 0
  simp only [Nat.zero_add] at h5
  have h12 := stepNat_trans 1 (2 * (3 * k)) h1 h2
  have h123 := stepNat_trans (1 + 2 * (3 * k)) (3 * k) h12 h3
  have h1234 := stepNat_trans (1 + 2 * (3 * k) + 3 * k) 2 h123 h4
  have h12345 := stepNat_trans (1 + 2 * (3 * k) + 3 * k + 2) (5 * k + 1) h1234 h5
  rw [show 1 + 2 * (3 * k) + 3 * k + 2 + (5 * k + 1) = 14 * k + 4 from by ring] at h12345
  exact h12345

private theorem mod1_sn : ∀ k A, (⟨A + 1, 0, 0, 3 * k + 1, 0⟩ : Q) [fm]⊢^{14 * k + 10} ⟨A + 2, 0, 0, 5 * k + 3, 0⟩ := by
  intro k A
  have h1 : (⟨A + 1, 0, 0, 3 * k + 1, 0⟩ : Q) [fm]⊢^{1} ⟨A, 1, 0, 3 * k + 1, 0⟩ := rfl
  have h2 := r31_sn (3 * k + 1) A 0 0 0
  simp only [Nat.zero_add] at h2
  rw [show 3 * k + 1 + 1 = 2 + 3 * k from by ring] at h2
  have h3 := drain_sn k A 2 (3 * k + 1)
  rw [show 3 * k + 1 + 2 * k = 5 * k + 1 from by ring] at h3
  have h4 := tail2_sn A (5 * k + 1)
  rw [show 5 * k + 1 + 2 = 5 * k + 3 from by ring] at h4
  have h5 := r5_sn (5 * k + 3) (A + 2) 0 0
  simp only [Nat.zero_add] at h5
  have h12 := stepNat_trans 1 (2 * (3 * k + 1)) h1 h2
  have h123 := stepNat_trans (1 + 2 * (3 * k + 1)) (3 * k) h12 h3
  have h1234 := stepNat_trans (1 + 2 * (3 * k + 1) + 3 * k) 4 h123 h4
  have h12345 := stepNat_trans (1 + 2 * (3 * k + 1) + 3 * k + 4) (5 * k + 3) h1234 h5
  rw [show 1 + 2 * (3 * k + 1) + 3 * k + 4 + (5 * k + 3) = 14 * k + 10 from by ring] at h12345
  exact h12345

private theorem mod2_sn : ∀ k A, (⟨A + 1, 0, 0, 3 * k + 2, 0⟩ : Q) [fm]⊢^{14 * k + 12} ⟨A, 0, 0, 5 * k + 4, 0⟩ := by
  intro k A
  have h1 : (⟨A + 1, 0, 0, 3 * k + 2, 0⟩ : Q) [fm]⊢^{1} ⟨A, 1, 0, 3 * k + 2, 0⟩ := rfl
  have h2 := r31_sn (3 * k + 2) A 0 0 0
  simp only [Nat.zero_add] at h2
  rw [show 3 * k + 2 + 1 = 3 * (k + 1) from by ring] at h2
  have h3 := drain_sn (k + 1) A 0 (3 * k + 2)
  simp only [Nat.zero_add] at h3
  rw [show 3 * k + 2 + 2 * (k + 1) = 5 * k + 4 from by ring] at h3
  have h4 := r5_sn (5 * k + 4) A 0 0
  simp only [Nat.zero_add] at h4
  have h12 := stepNat_trans 1 (2 * (3 * k + 2)) h1 h2
  have h123 := stepNat_trans (1 + 2 * (3 * k + 2)) (3 * (k + 1)) h12 h3
  have h1234 := stepNat_trans (1 + 2 * (3 * k + 2) + 3 * (k + 1)) (5 * k + 4) h123 h4
  rw [show 1 + 2 * (3 * k + 2) + 3 * (k + 1) + (5 * k + 4) = 14 * k + 12 from by ring] at h1234
  exact h1234

theorem fm_haltsIn : haltsIn fm c₀ 114613926700260640237968442298168949531348819453104518623702294 := by
  apply stepNat_haltsIn_add (m := 4) (c₂ := ⟨1, 0, 0, 1, 0⟩)
  · have h := mod0_sn 0 0
    exact h
  apply stepNat_haltsIn_add (m := 10) (c₂ := ⟨2, 0, 0, 3, 0⟩)
  · have h := mod1_sn 0 0
    exact h
  apply stepNat_haltsIn_add (m := 18) (c₂ := ⟨2, 0, 0, 6, 0⟩)
  · have h := mod0_sn 1 1
    exact h
  apply stepNat_haltsIn_add (m := 32) (c₂ := ⟨2, 0, 0, 11, 0⟩)
  · have h := mod0_sn 2 1
    exact h
  apply stepNat_haltsIn_add (m := 54) (c₂ := ⟨1, 0, 0, 19, 0⟩)
  · have h := mod2_sn 3 1
    exact h
  apply stepNat_haltsIn_add (m := 94) (c₂ := ⟨2, 0, 0, 33, 0⟩)
  · have h := mod1_sn 6 0
    exact h
  apply stepNat_haltsIn_add (m := 158) (c₂ := ⟨2, 0, 0, 56, 0⟩)
  · have h := mod0_sn 11 1
    exact h
  apply stepNat_haltsIn_add (m := 264) (c₂ := ⟨1, 0, 0, 94, 0⟩)
  · have h := mod2_sn 18 1
    exact h
  apply stepNat_haltsIn_add (m := 444) (c₂ := ⟨2, 0, 0, 158, 0⟩)
  · have h := mod1_sn 31 0
    exact h
  apply stepNat_haltsIn_add (m := 740) (c₂ := ⟨1, 0, 0, 264, 0⟩)
  · have h := mod2_sn 52 1
    exact h
  apply stepNat_haltsIn_add (m := 1236) (c₂ := ⟨1, 0, 0, 441, 0⟩)
  · have h := mod0_sn 88 0
    exact h
  apply stepNat_haltsIn_add (m := 2062) (c₂ := ⟨1, 0, 0, 736, 0⟩)
  · have h := mod0_sn 147 0
    exact h
  apply stepNat_haltsIn_add (m := 3440) (c₂ := ⟨2, 0, 0, 1228, 0⟩)
  · have h := mod1_sn 245 0
    exact h
  apply stepNat_haltsIn_add (m := 5736) (c₂ := ⟨3, 0, 0, 2048, 0⟩)
  · have h := mod1_sn 409 1
    exact h
  apply stepNat_haltsIn_add (m := 9560) (c₂ := ⟨2, 0, 0, 3414, 0⟩)
  · have h := mod2_sn 682 2
    exact h
  apply stepNat_haltsIn_add (m := 15936) (c₂ := ⟨2, 0, 0, 5691, 0⟩)
  · have h := mod0_sn 1138 1
    exact h
  apply stepNat_haltsIn_add (m := 26562) (c₂ := ⟨2, 0, 0, 9486, 0⟩)
  · have h := mod0_sn 1897 1
    exact h
  apply stepNat_haltsIn_add (m := 44272) (c₂ := ⟨2, 0, 0, 15811, 0⟩)
  · have h := mod0_sn 3162 1
    exact h
  apply stepNat_haltsIn_add (m := 73790) (c₂ := ⟨3, 0, 0, 26353, 0⟩)
  · have h := mod1_sn 5270 1
    exact h
  apply stepNat_haltsIn_add (m := 122986) (c₂ := ⟨4, 0, 0, 43923, 0⟩)
  · have h := mod1_sn 8784 2
    exact h
  apply stepNat_haltsIn_add (m := 204978) (c₂ := ⟨4, 0, 0, 73206, 0⟩)
  · have h := mod0_sn 14641 3
    exact h
  apply stepNat_haltsIn_add (m := 341632) (c₂ := ⟨4, 0, 0, 122011, 0⟩)
  · have h := mod0_sn 24402 3
    exact h
  apply stepNat_haltsIn_add (m := 569390) (c₂ := ⟨5, 0, 0, 203353, 0⟩)
  · have h := mod1_sn 40670 3
    exact h
  apply stepNat_haltsIn_add (m := 948986) (c₂ := ⟨6, 0, 0, 338923, 0⟩)
  · have h := mod1_sn 67784 4
    exact h
  apply stepNat_haltsIn_add (m := 1581646) (c₂ := ⟨7, 0, 0, 564873, 0⟩)
  · have h := mod1_sn 112974 5
    exact h
  apply stepNat_haltsIn_add (m := 2636078) (c₂ := ⟨7, 0, 0, 941456, 0⟩)
  · have h := mod0_sn 188291 6
    exact h
  apply stepNat_haltsIn_add (m := 4393464) (c₂ := ⟨6, 0, 0, 1569094, 0⟩)
  · have h := mod2_sn 313818 6
    exact h
  apply stepNat_haltsIn_add (m := 7322444) (c₂ := ⟨7, 0, 0, 2615158, 0⟩)
  · have h := mod1_sn 523031 5
    exact h
  apply stepNat_haltsIn_add (m := 12204076) (c₂ := ⟨8, 0, 0, 4358598, 0⟩)
  · have h := mod1_sn 871719 6
    exact h
  apply stepNat_haltsIn_add (m := 20340128) (c₂ := ⟨8, 0, 0, 7264331, 0⟩)
  · have h := mod0_sn 1452866 7
    exact h
  apply stepNat_haltsIn_add (m := 33900214) (c₂ := ⟨7, 0, 0, 12107219, 0⟩)
  · have h := mod2_sn 2421443 7
    exact h
  apply stepNat_haltsIn_add (m := 56500358) (c₂ := ⟨6, 0, 0, 20178699, 0⟩)
  · have h := mod2_sn 4035739 6
    exact h
  apply stepNat_haltsIn_add (m := 94167266) (c₂ := ⟨6, 0, 0, 33631166, 0⟩)
  · have h := mod0_sn 6726233 5
    exact h
  apply stepNat_haltsIn_add (m := 156945444) (c₂ := ⟨5, 0, 0, 56051944, 0⟩)
  · have h := mod2_sn 11210388 5
    exact h
  apply stepNat_haltsIn_add (m := 261575744) (c₂ := ⟨6, 0, 0, 93419908, 0⟩)
  · have h := mod1_sn 18683981 4
    exact h
  apply stepNat_haltsIn_add (m := 435959576) (c₂ := ⟨7, 0, 0, 155699848, 0⟩)
  · have h := mod1_sn 31139969 5
    exact h
  apply stepNat_haltsIn_add (m := 726599296) (c₂ := ⟨8, 0, 0, 259499748, 0⟩)
  · have h := mod1_sn 51899949 6
    exact h
  apply stepNat_haltsIn_add (m := 1210998828) (c₂ := ⟨8, 0, 0, 432499581, 0⟩)
  · have h := mod0_sn 86499916 7
    exact h
  apply stepNat_haltsIn_add (m := 2018331382) (c₂ := ⟨8, 0, 0, 720832636, 0⟩)
  · have h := mod0_sn 144166527 7
    exact h
  apply stepNat_haltsIn_add (m := 3363885640) (c₂ := ⟨9, 0, 0, 1201387728, 0⟩)
  · have h := mod1_sn 240277545 7
    exact h
  apply stepNat_haltsIn_add (m := 5606476068) (c₂ := ⟨9, 0, 0, 2002312881, 0⟩)
  · have h := mod0_sn 400462576 8
    exact h
  apply stepNat_haltsIn_add (m := 9344126782) (c₂ := ⟨9, 0, 0, 3337188136, 0⟩)
  · have h := mod0_sn 667437627 8
    exact h
  apply stepNat_haltsIn_add (m := 15573544640) (c₂ := ⟨10, 0, 0, 5561980228, 0⟩)
  · have h := mod1_sn 1112396045 8
    exact h
  apply stepNat_haltsIn_add (m := 25955907736) (c₂ := ⟨11, 0, 0, 9269967048, 0⟩)
  · have h := mod1_sn 1853993409 9
    exact h
  apply stepNat_haltsIn_add (m := 43259846228) (c₂ := ⟨11, 0, 0, 15449945081, 0⟩)
  · have h := mod0_sn 3089989016 10
    exact h
  apply stepNat_haltsIn_add (m := 72099743714) (c₂ := ⟨10, 0, 0, 25749908469, 0⟩)
  · have h := mod2_sn 5149981693 10
    exact h
  apply stepNat_haltsIn_add (m := 120166239526) (c₂ := ⟨10, 0, 0, 42916514116, 0⟩)
  · have h := mod0_sn 8583302823 9
    exact h
  apply stepNat_haltsIn_add (m := 200277065880) (c₂ := ⟨11, 0, 0, 71527523528, 0⟩)
  · have h := mod1_sn 14305504705 9
    exact h
  apply stepNat_haltsIn_add (m := 333795109800) (c₂ := ⟨10, 0, 0, 119212539214, 0⟩)
  · have h := mod2_sn 23842507842 10
    exact h
  apply stepNat_haltsIn_add (m := 556325183004) (c₂ := ⟨11, 0, 0, 198687565358, 0⟩)
  · have h := mod1_sn 39737513071 9
    exact h
  apply stepNat_haltsIn_add (m := 927208638340) (c₂ := ⟨10, 0, 0, 331145942264, 0⟩)
  · have h := mod2_sn 66229188452 10
    exact h
  apply stepNat_haltsIn_add (m := 1545347730568) (c₂ := ⟨9, 0, 0, 551909903774, 0⟩)
  · have h := mod2_sn 110381980754 9
    exact h
  apply stepNat_haltsIn_add (m := 2575579550948) (c₂ := ⟨8, 0, 0, 919849839624, 0⟩)
  · have h := mod2_sn 183969967924 8
    exact h
  apply stepNat_haltsIn_add (m := 4292632584916) (c₂ := ⟨8, 0, 0, 1533083066041, 0⟩)
  · have h := mod0_sn 306616613208 7
    exact h
  apply stepNat_haltsIn_add (m := 7154387641530) (c₂ := ⟨9, 0, 0, 2555138443403, 0⟩)
  · have h := mod1_sn 511027688680 7
    exact h
  apply stepNat_haltsIn_add (m := 11923979402550) (c₂ := ⟨8, 0, 0, 4258564072339, 0⟩)
  · have h := mod2_sn 851712814467 8
    exact h
  apply stepNat_haltsIn_add (m := 19873299004254) (c₂ := ⟨9, 0, 0, 7097606787233, 0⟩)
  · have h := mod1_sn 1419521357446 7
    exact h
  apply stepNat_haltsIn_add (m := 33122165007090) (c₂ := ⟨8, 0, 0, 11829344645389, 0⟩)
  · have h := mod2_sn 2365868929077 8
    exact h
  apply stepNat_haltsIn_add (m := 55203608345154) (c₂ := ⟨9, 0, 0, 19715574408983, 0⟩)
  · have h := mod1_sn 3943114881796 7
    exact h
  apply stepNat_haltsIn_add (m := 92006013908590) (c₂ := ⟨8, 0, 0, 32859290681639, 0⟩)
  · have h := mod2_sn 6571858136327 8
    exact h
  apply stepNat_haltsIn_add (m := 153343356514318) (c₂ := ⟨7, 0, 0, 54765484469399, 0⟩)
  · have h := mod2_sn 10953096893879 7
    exact h
  apply stepNat_haltsIn_add (m := 255572260857198) (c₂ := ⟨6, 0, 0, 91275807448999, 0⟩)
  · have h := mod2_sn 18255161489799 6
    exact h
  apply stepNat_haltsIn_add (m := 425953768095334) (c₂ := ⟨7, 0, 0, 152126345748333, 0⟩)
  · have h := mod1_sn 30425269149666 5
    exact h
  apply stepNat_haltsIn_add (m := 709922946825558) (c₂ := ⟨7, 0, 0, 253543909580556, 0⟩)
  · have h := mod0_sn 50708781916111 6
    exact h
  apply stepNat_haltsIn_add (m := 1183204911375932) (c₂ := ⟨7, 0, 0, 422573182634261, 0⟩)
  · have h := mod0_sn 84514636526852 6
    exact h
  apply stepNat_haltsIn_add (m := 1972008185626554) (c₂ := ⟨6, 0, 0, 704288637723769, 0⟩)
  · have h := mod2_sn 140857727544753 6
    exact h
  apply stepNat_haltsIn_add (m := 3286680309377594) (c₂ := ⟨7, 0, 0, 1173814396206283, 0⟩)
  · have h := mod1_sn 234762879241256 5
    exact h
  apply stepNat_haltsIn_add (m := 5477800515629326) (c₂ := ⟨8, 0, 0, 1956357327010473, 0⟩)
  · have h := mod1_sn 391271465402094 6
    exact h
  apply stepNat_haltsIn_add (m := 9129667526048878) (c₂ := ⟨8, 0, 0, 3260595545017456, 0⟩)
  · have h := mod0_sn 652119109003491 7
    exact h
  apply stepNat_haltsIn_add (m := 15216112543414800) (c₂ := ⟨9, 0, 0, 5434325908362428, 0⟩)
  · have h := mod1_sn 1086865181672485 7
    exact h
  apply stepNat_haltsIn_add (m := 25360187572358000) (c₂ := ⟨8, 0, 0, 9057209847270714, 0⟩)
  · have h := mod2_sn 1811441969454142 8
    exact h
  apply stepNat_haltsIn_add (m := 42266979287263336) (c₂ := ⟨8, 0, 0, 15095349745451191, 0⟩)
  · have h := mod0_sn 3019069949090238 7
    exact h
  apply stepNat_haltsIn_add (m := 70444965478772230) (c₂ := ⟨9, 0, 0, 25158916242418653, 0⟩)
  · have h := mod1_sn 5031783248483730 7
    exact h
  apply stepNat_haltsIn_add (m := 117408275797953718) (c₂ := ⟨9, 0, 0, 41931527070697756, 0⟩)
  · have h := mod0_sn 8386305414139551 8
    exact h
  apply stepNat_haltsIn_add (m := 195680459663256200) (c₂ := ⟨10, 0, 0, 69885878451162928, 0⟩)
  · have h := mod1_sn 13977175690232585 8
    exact h
  apply stepNat_haltsIn_add (m := 326134099438760336) (c₂ := ⟨11, 0, 0, 116476464085271548, 0⟩)
  · have h := mod1_sn 23295292817054309 9
    exact h
  apply stepNat_haltsIn_add (m := 543556832397933896) (c₂ := ⟨12, 0, 0, 194127440142119248, 0⟩)
  · have h := mod1_sn 38825488028423849 10
    exact h
  apply stepNat_haltsIn_add (m := 905928053996556496) (c₂ := ⟨13, 0, 0, 323545733570198748, 0⟩)
  · have h := mod1_sn 64709146714039749 11
    exact h
  apply stepNat_haltsIn_add (m := 1509880089994260828) (c₂ := ⟨13, 0, 0, 539242889283664581, 0⟩)
  · have h := mod0_sn 107848577856732916 12
    exact h
  apply stepNat_haltsIn_add (m := 2516466816657101382) (c₂ := ⟨13, 0, 0, 898738148806107636, 0⟩)
  · have h := mod0_sn 179747629761221527 12
    exact h
  apply stepNat_haltsIn_add (m := 4194111361095168972) (c₂ := ⟨13, 0, 0, 1497896914676846061, 0⟩)
  · have h := mod0_sn 299579382935369212 12
    exact h
  apply stepNat_haltsIn_add (m := 6990185601825281622) (c₂ := ⟨13, 0, 0, 2496494857794743436, 0⟩)
  · have h := mod0_sn 499298971558948687 12
    exact h
  apply stepNat_haltsIn_add (m := 11650309336375469372) (c₂ := ⟨13, 0, 0, 4160824762991239061, 0⟩)
  · have h := mod0_sn 832164952598247812 12
    exact h
  apply stepNat_haltsIn_add (m := 19417182227292448954) (c₂ := ⟨12, 0, 0, 6934707938318731769, 0⟩)
  · have h := mod2_sn 1386941587663746353 12
    exact h
  apply stepNat_haltsIn_add (m := 32361970378820748258) (c₂ := ⟨11, 0, 0, 11557846563864552949, 0⟩)
  · have h := mod2_sn 2311569312772910589 11
    exact h
  apply stepNat_haltsIn_add (m := 53936617298034580434) (c₂ := ⟨12, 0, 0, 19263077606440921583, 0⟩)
  · have h := mod1_sn 3852615521288184316 10
    exact h
  apply stepNat_haltsIn_add (m := 89894362163390967390) (c₂ := ⟨11, 0, 0, 32105129344068202639, 0⟩)
  · have h := mod2_sn 6421025868813640527 11
    exact h
  apply stepNat_haltsIn_add (m := 149823936938984945654) (c₂ := ⟨12, 0, 0, 53508548906780337733, 0⟩)
  · have h := mod1_sn 10701709781356067546 10
    exact h
  apply stepNat_haltsIn_add (m := 249706561564974909426) (c₂ := ⟨13, 0, 0, 89180914844633896223, 0⟩)
  · have h := mod1_sn 17836182968926779244 11
    exact h
  apply stepNat_haltsIn_add (m := 416177602608291515710) (c₂ := ⟨12, 0, 0, 148634858074389827039, 0⟩)
  · have h := mod2_sn 29726971614877965407 12
    exact h
  apply stepNat_haltsIn_add (m := 693629337680485859518) (c₂ := ⟨11, 0, 0, 247724763457316378399, 0⟩)
  · have h := mod2_sn 49544952691463275679 11
    exact h
  apply stepNat_haltsIn_add (m := 1156048896134143099198) (c₂ := ⟨10, 0, 0, 412874605762193963999, 0⟩)
  · have h := mod2_sn 82574921152438792799 10
    exact h
  apply stepNat_haltsIn_add (m := 1926748160223571831998) (c₂ := ⟨9, 0, 0, 688124342936989939999, 0⟩)
  · have h := mod2_sn 137624868587397987999 9
    exact h
  apply stepNat_haltsIn_add (m := 3211246933705953053334) (c₂ := ⟨10, 0, 0, 1146873904894983233333, 0⟩)
  · have h := mod1_sn 229374780978996646666 8
    exact h
  apply stepNat_haltsIn_add (m := 5352078222843255088890) (c₂ := ⟨9, 0, 0, 1911456508158305388889, 0⟩)
  · have h := mod2_sn 382291301631661077777 9
    exact h
  apply stepNat_haltsIn_add (m := 8920130371405425148154) (c₂ := ⟨10, 0, 0, 3185760846930508981483, 0⟩)
  · have h := mod1_sn 637152169386101796296 8
    exact h
  apply stepNat_haltsIn_add (m := 14866883952342375246926) (c₂ := ⟨11, 0, 0, 5309601411550848302473, 0⟩)
  · have h := mod1_sn 1061920282310169660494 9
    exact h
  apply stepNat_haltsIn_add (m := 24778139920570625411546) (c₂ := ⟨12, 0, 0, 8849335685918080504123, 0⟩)
  · have h := mod1_sn 1769867137183616100824 10
    exact h
  apply stepNat_haltsIn_add (m := 41296899867617709019246) (c₂ := ⟨13, 0, 0, 14748892809863467506873, 0⟩)
  · have h := mod1_sn 2949778561972693501374 11
    exact h
  apply stepNat_haltsIn_add (m := 68828166446029515032078) (c₂ := ⟨13, 0, 0, 24581488016439112511456, 0⟩)
  · have h := mod0_sn 4916297603287822502291 12
    exact h
  apply stepNat_haltsIn_add (m := 114713610743382525053464) (c₂ := ⟨12, 0, 0, 40969146694065187519094, 0⟩)
  · have h := mod2_sn 8193829338813037503818 12
    exact h
  apply stepNat_haltsIn_add (m := 191189351238970875089108) (c₂ := ⟨11, 0, 0, 68281911156775312531824, 0⟩)
  · have h := mod2_sn 13656382231355062506364 11
    exact h
  apply stepNat_haltsIn_add (m := 318648918731618125148516) (c₂ := ⟨11, 0, 0, 113803185261292187553041, 0⟩)
  · have h := mod0_sn 22760637052258437510608 10
    exact h
  apply stepNat_haltsIn_add (m := 531081531219363541914194) (c₂ := ⟨10, 0, 0, 189671975435486979255069, 0⟩)
  · have h := mod2_sn 37934395087097395851013 10
    exact h
  apply stepNat_haltsIn_add (m := 885135885365605903190326) (c₂ := ⟨10, 0, 0, 316119959059144965425116, 0⟩)
  · have h := mod0_sn 63223991811828993085023 9
    exact h
  apply stepNat_haltsIn_add (m := 1475226475609343171983880) (c₂ := ⟨11, 0, 0, 526866598431908275708528, 0⟩)
  · have h := mod1_sn 105373319686381655141705 9
    exact h
  apply stepNat_haltsIn_add (m := 2458710792682238619973136) (c₂ := ⟨12, 0, 0, 878110997386513792847548, 0⟩)
  · have h := mod1_sn 175622199477302758569509 10
    exact h
  apply stepNat_haltsIn_add (m := 4097851321137064366621896) (c₂ := ⟨13, 0, 0, 1463518328977522988079248, 0⟩)
  · have h := mod1_sn 292703665795504597615849 11
    exact h
  apply stepNat_haltsIn_add (m := 6829752201895107277703160) (c₂ := ⟨12, 0, 0, 2439197214962538313465414, 0⟩)
  · have h := mod2_sn 487839442992507662693082 12
    exact h
  apply stepNat_haltsIn_add (m := 11382920336491845462838604) (c₂ := ⟨13, 0, 0, 4065328691604230522442358, 0⟩)
  · have h := mod1_sn 813065738320846104488471 11
    exact h
  apply stepNat_haltsIn_add (m := 18971533894153075771397676) (c₂ := ⟨14, 0, 0, 6775547819340384204070598, 0⟩)
  · have h := mod1_sn 1355109563868076840814119 12
    exact h
  apply stepNat_haltsIn_add (m := 31619223156921792952329460) (c₂ := ⟨13, 0, 0, 11292579698900640340117664, 0⟩)
  · have h := mod2_sn 2258515939780128068023532 13
    exact h
  apply stepNat_haltsIn_add (m := 52698705261536321587215768) (c₂ := ⟨12, 0, 0, 18820966164834400566862774, 0⟩)
  · have h := mod2_sn 3764193232966880113372554 12
    exact h
  apply stepNat_haltsIn_add (m := 87831175435893869312026284) (c₂ := ⟨13, 0, 0, 31368276941390667611437958, 0⟩)
  · have h := mod1_sn 6273655388278133522287591 11
    exact h
  apply stepNat_haltsIn_add (m := 146385292393156448853377140) (c₂ := ⟨12, 0, 0, 52280461568984446019063264, 0⟩)
  · have h := mod2_sn 10456092313796889203812652 12
    exact h
  apply stepNat_haltsIn_add (m := 243975487321927414755628568) (c₂ := ⟨11, 0, 0, 87134102614974076698438774, 0⟩)
  · have h := mod2_sn 17426820522994815339687754 11
    exact h
  apply stepNat_haltsIn_add (m := 406625812203212357926047616) (c₂ := ⟨11, 0, 0, 145223504358290127830731291, 0⟩)
  · have h := mod0_sn 29044700871658025566146258 10
    exact h
  apply stepNat_haltsIn_add (m := 677709687005353929876746030) (c₂ := ⟨12, 0, 0, 242039173930483546384552153, 0⟩)
  · have h := mod1_sn 48407834786096709276910430 10
    exact h
  apply stepNat_haltsIn_add (m := 1129516145008923216461243386) (c₂ := ⟨13, 0, 0, 403398623217472577307586923, 0⟩)
  · have h := mod1_sn 80679724643494515461517384 11
    exact h
  apply stepNat_haltsIn_add (m := 1882526908348205360768738978) (c₂ := ⟨13, 0, 0, 672331038695787628845978206, 0⟩)
  · have h := mod0_sn 134466207739157525769195641 12
    exact h
  apply stepNat_haltsIn_add (m := 3137544847247008934614564964) (c₂ := ⟨12, 0, 0, 1120551731159646048076630344, 0⟩)
  · have h := mod2_sn 224110346231929209615326068 12
    exact h
  apply stepNat_haltsIn_add (m := 5229241412078348224357608276) (c₂ := ⟨12, 0, 0, 1867586218599410080127717241, 0⟩)
  · have h := mod0_sn 373517243719882016025543448 11
    exact h
  apply stepNat_haltsIn_add (m := 8715402353463913707262680462) (c₂ := ⟨12, 0, 0, 3112643697665683466879528736, 0⟩)
  · have h := mod0_sn 622528739533136693375905747 11
    exact h
  apply stepNat_haltsIn_add (m := 14525670589106522845437800772) (c₂ := ⟨12, 0, 0, 5187739496109472444799214561, 0⟩)
  · have h := mod0_sn 1037547899221894488959842912 11
    exact h
  apply stepNat_haltsIn_add (m := 24209450981844204742396334622) (c₂ := ⟨12, 0, 0, 8646232493515787407998690936, 0⟩)
  · have h := mod0_sn 1729246498703157481599738187 11
    exact h
  apply stepNat_haltsIn_add (m := 40349084969740341237327224372) (c₂ := ⟨12, 0, 0, 14410387489192979013331151561, 0⟩)
  · have h := mod0_sn 2882077497838595802666230312 11
    exact h
  apply stepNat_haltsIn_add (m := 67248474949567235395545373954) (c₂ := ⟨11, 0, 0, 24017312481988298355551919269, 0⟩)
  · have h := mod2_sn 4803462496397659671110383853 11
    exact h
  apply stepNat_haltsIn_add (m := 112080791582612058992575623258) (c₂ := ⟨10, 0, 0, 40028854136647163925919865449, 0⟩)
  · have h := mod2_sn 8005770827329432785183973089 10
    exact h
  apply stepNat_haltsIn_add (m := 186801319304353431654292705434) (c₂ := ⟨11, 0, 0, 66714756894411939876533109083, 0⟩)
  · have h := mod1_sn 13342951378882387975306621816 9
    exact h
  apply stepNat_haltsIn_add (m := 311335532173922386090487842390) (c₂ := ⟨10, 0, 0, 111191261490686566460888515139, 0⟩)
  · have h := mod2_sn 22238252298137313292177703027 10
    exact h
  apply stepNat_haltsIn_add (m := 518892553623203976817479737318) (c₂ := ⟨9, 0, 0, 185318769151144277434814191899, 0⟩)
  · have h := mod2_sn 37063753830228855486962838379 9
    exact h
  apply stepNat_haltsIn_add (m := 864820922705339961362466228866) (c₂ := ⟨9, 0, 0, 308864615251907129058023653166, 0⟩)
  · have h := mod0_sn 61772923050381425811604730633 8
    exact h
  apply stepNat_haltsIn_add (m := 1441368204508899935604110381444) (c₂ := ⟨8, 0, 0, 514774358753178548430039421944, 0⟩)
  · have h := mod2_sn 102954871750635709686007884388 8
    exact h
  apply stepNat_haltsIn_add (m := 2402280340848166559340183969076) (c₂ := ⟨8, 0, 0, 857957264588630914050065703241, 0⟩)
  · have h := mod0_sn 171591452917726182810013140648 7
    exact h
  apply stepNat_haltsIn_add (m := 4003800568080277598900306615130) (c₂ := ⟨9, 0, 0, 1429928774314384856750109505403, 0⟩)
  · have h := mod1_sn 285985754862876971350021901080 7
    exact h
  apply stepNat_haltsIn_add (m := 6673000946800462664833844358550) (c₂ := ⟨8, 0, 0, 2383214623857308094583515842339, 0⟩)
  · have h := mod2_sn 476642924771461618916703168467 8
    exact h
  apply stepNat_haltsIn_add (m := 11121668244667437774723073930918) (c₂ := ⟨7, 0, 0, 3972024373095513490972526403899, 0⟩)
  · have h := mod2_sn 794404874619102698194505280779 7
    exact h
  apply stepNat_haltsIn_add (m := 18536113741112396291205123218198) (c₂ := ⟨6, 0, 0, 6620040621825855818287544006499, 0⟩)
  · have h := mod2_sn 1324008124365171163657508801299 6
    exact h
  apply stepNat_haltsIn_add (m := 30893522901853993818675205363666) (c₂ := ⟨6, 0, 0, 11033401036376426363812573344166, 0⟩)
  · have h := mod0_sn 2206680207275285272762514668833 5
    exact h
  apply stepNat_haltsIn_add (m := 51489204836423323031125342272780) (c₂ := ⟨7, 0, 0, 18389001727294043939687622240278, 0⟩)
  · have h := mod1_sn 3677800345458808787937524448055 5
    exact h
  apply stepNat_haltsIn_add (m := 85815341394038871718542237121300) (c₂ := ⟨6, 0, 0, 30648336212156739899479370400464, 0⟩)
  · have h := mod2_sn 6129667242431347979895874080092 6
    exact h
  apply stepNat_haltsIn_add (m := 143025568990064786197570395202168) (c₂ := ⟨5, 0, 0, 51080560353594566499132284000774, 0⟩)
  · have h := mod2_sn 10216112070718913299826456800154 5
    exact h
  apply stepNat_haltsIn_add (m := 238375948316774643662617325336948) (c₂ := ⟨4, 0, 0, 85134267255990944165220473334624, 0⟩)
  · have h := mod2_sn 17026853451198188833044094666924 4
    exact h
  apply stepNat_haltsIn_add (m := 397293247194624406104362208894916) (c₂ := ⟨4, 0, 0, 141890445426651573608700788891041, 0⟩)
  · have h := mod0_sn 28378089085330314721740157778208 3
    exact h
  apply stepNat_haltsIn_add (m := 662155411991040676840603681491530) (c₂ := ⟨5, 0, 0, 236484075711085956014501314818403, 0⟩)
  · have h := mod1_sn 47296815142217191202900262963680 3
    exact h
  apply stepNat_haltsIn_add (m := 1103592353318401128067672802485886) (c₂ := ⟨6, 0, 0, 394140126185143260024168858030673, 0⟩)
  · have h := mod1_sn 78828025237028652004833771606134 4
    exact h
  apply stepNat_haltsIn_add (m := 1839320588864001880112788004143146) (c₂ := ⟨7, 0, 0, 656900210308572100040281430051123, 0⟩)
  · have h := mod1_sn 131380042061714420008056286010224 5
    exact h
  apply stepNat_haltsIn_add (m := 3065534314773336466854646673571910) (c₂ := ⟨6, 0, 0, 1094833683847620166733802383418539, 0⟩)
  · have h := mod2_sn 218966736769524033346760476683707 6
    exact h
  apply stepNat_haltsIn_add (m := 5109223857955560778091077789286518) (c₂ := ⟨5, 0, 0, 1824722806412700277889670639030899, 0⟩)
  · have h := mod2_sn 364944561282540055577934127806179 5
    exact h
  apply stepNat_haltsIn_add (m := 8515373096592601296818462982144198) (c₂ := ⟨4, 0, 0, 3041204677354500463149451065051499, 0⟩)
  · have h := mod2_sn 608240935470900092629890213010299 4
    exact h
  apply stepNat_haltsIn_add (m := 14192288494321002161364104970240334) (c₂ := ⟨5, 0, 0, 5068674462257500771915751775085833, 0⟩)
  · have h := mod1_sn 1013734892451500154383150355017166 3
    exact h
  apply stepNat_haltsIn_add (m := 23653814157201670268940174950400558) (c₂ := ⟨5, 0, 0, 8447790770429167953192919625143056, 0⟩)
  · have h := mod0_sn 1689558154085833590638583925028611 4
    exact h
  apply stepNat_haltsIn_add (m := 39423023595336117114900291584000932) (c₂ := ⟨5, 0, 0, 14079651284048613255321532708571761, 0⟩)
  · have h := mod0_sn 2815930256809722651064306541714352 4
    exact h
  apply stepNat_haltsIn_add (m := 65705039325560195191500485973334890) (c₂ := ⟨6, 0, 0, 23466085473414355425535887847619603, 0⟩)
  · have h := mod1_sn 4693217094682871085107177569523920 4
    exact h
  apply stepNat_haltsIn_add (m := 109508398875933658652500809955558150) (c₂ := ⟨5, 0, 0, 39110142455690592375893146412699339, 0⟩)
  · have h := mod2_sn 7822028491138118475178629282539867 5
    exact h
  apply stepNat_haltsIn_add (m := 182513998126556097754168016592596918) (c₂ := ⟨4, 0, 0, 65183570759484320626488577354498899, 0⟩)
  · have h := mod2_sn 13036714151896864125297715470899779 4
    exact h
  apply stepNat_haltsIn_add (m := 304189996877593496256946694320994866) (c₂ := ⟨4, 0, 0, 108639284599140534377480962257498166, 0⟩)
  · have h := mod0_sn 21727856919828106875496192451499633 3
    exact h
  apply stepNat_haltsIn_add (m := 506983328129322493761577823868324780) (c₂ := ⟨5, 0, 0, 181065474331900890629134937095830278, 0⟩)
  · have h := mod1_sn 36213094866380178125826987419166055 3
    exact h
  apply stepNat_haltsIn_add (m := 844972213548870822935963039780541300) (c₂ := ⟨4, 0, 0, 301775790553168151048558228493050464, 0⟩)
  · have h := mod2_sn 60355158110633630209711645698610092 4
    exact h
  apply stepNat_haltsIn_add (m := 1408287022581451371559938399634235504) (c₂ := ⟨5, 0, 0, 502959650921946918414263714155084108, 0⟩)
  · have h := mod1_sn 100591930184389383682852742831016821 3
    exact h
  apply stepNat_haltsIn_add (m := 2347145037635752285933230666057059176) (c₂ := ⟨6, 0, 0, 838266084869911530690439523591806848, 0⟩)
  · have h := mod1_sn 167653216973982306138087904718361369 4
    exact h
  apply stepNat_haltsIn_add (m := 3911908396059587143222051110095098628) (c₂ := ⟨6, 0, 0, 1397110141449852551150732539319678081, 0⟩)
  · have h := mod0_sn 279422028289970510230146507863935616 5
    exact h
  apply stepNat_haltsIn_add (m := 6519847326765978572036751850158497714) (c₂ := ⟨5, 0, 0, 2328516902416420918584554232199463469, 0⟩)
  · have h := mod2_sn 465703380483284183716910846439892693 5
    exact h
  apply stepNat_haltsIn_add (m := 10866412211276630953394586416930829526) (c₂ := ⟨5, 0, 0, 3880861504027368197640923720332439116, 0⟩)
  · have h := mod0_sn 776172300805473639528184744066487823 4
    exact h
  apply stepNat_haltsIn_add (m := 18110687018794384922324310694884715880) (c₂ := ⟨6, 0, 0, 6468102506712280329401539533887398528, 0⟩)
  · have h := mod1_sn 1293620501342456065880307906777479705 4
    exact h
  apply stepNat_haltsIn_add (m := 30184478364657308203873851158141193136) (c₂ := ⟨7, 0, 0, 10780170844520467215669232556478997548, 0⟩)
  · have h := mod1_sn 2156034168904093443133846511295799509 5
    exact h
  apply stepNat_haltsIn_add (m := 50307463941095513673123085263568655228) (c₂ := ⟨7, 0, 0, 17966951407534112026115387594131662581, 0⟩)
  · have h := mod0_sn 3593390281506822405223077518826332516 6
    exact h
  apply stepNat_haltsIn_add (m := 83845773235159189455205142105947758714) (c₂ := ⟨6, 0, 0, 29944919012556853376858979323552770969, 0⟩)
  · have h := mod2_sn 5988983802511370675371795864710554193 6
    exact h
  apply stepNat_haltsIn_add (m := 139742955391931982425341903509912931194) (c₂ := ⟨7, 0, 0, 49908198354261422294764965539254618283, 0⟩)
  · have h := mod1_sn 9981639670852284458952993107850923656 5
    exact h
  apply stepNat_haltsIn_add (m := 232904925653219970708903172516521551990) (c₂ := ⟨6, 0, 0, 83180330590435703824608275898757697139, 0⟩)
  · have h := mod2_sn 16636066118087140764921655179751539427 6
    exact h
  apply stepNat_haltsIn_add (m := 388174876088699951181505287527535919986) (c₂ := ⟨6, 0, 0, 138633884317392839707680459831262828566, 0⟩)
  · have h := mod0_sn 27726776863478567941536091966252565713 5
    exact h
  apply stepNat_haltsIn_add (m := 646958126814499918635842145879226533312) (c₂ := ⟨6, 0, 0, 231056473862321399512800766385438047611, 0⟩)
  · have h := mod0_sn 46211294772464279902560153277087609522 5
    exact h
  apply stepNat_haltsIn_add (m := 1078263544690833197726403576465377555522) (c₂ := ⟨6, 0, 0, 385094123103868999188001277309063412686, 0⟩)
  · have h := mod0_sn 77018824620773799837600255461812682537 5
    exact h
  apply stepNat_haltsIn_add (m := 1797105907818055329544005960775629259204) (c₂ := ⟨5, 0, 0, 641823538506448331980002128848439021144, 0⟩)
  · have h := mod2_sn 128364707701289666396000425769687804228 5
    exact h
  apply stepNat_haltsIn_add (m := 2995176513030092215906676601292715432008) (c₂ := ⟨4, 0, 0, 1069705897510747219966670214747398368574, 0⟩)
  · have h := mod2_sn 213941179502149443993334042949479673714 4
    exact h
  apply stepNat_haltsIn_add (m := 4991960855050153693177794335487859053348) (c₂ := ⟨3, 0, 0, 1782843162517912033277783691245663947624, 0⟩)
  · have h := mod2_sn 356568632503582406655556738249132789524 3
    exact h
  apply stepNat_haltsIn_add (m := 8319934758416922821962990559146431755584) (c₂ := ⟨4, 0, 0, 2971405270863186722129639485409439912708, 0⟩)
  · have h := mod1_sn 594281054172637344425927897081887982541 2
    exact h
  apply stepNat_haltsIn_add (m := 13866557930694871369938317598577386259308) (c₂ := ⟨4, 0, 0, 4952342118105311203549399142349066521181, 0⟩)
  · have h := mod0_sn 990468423621062240709879828469813304236 3
    exact h
  apply stepNat_haltsIn_add (m := 23110929884491452283230529330962310432182) (c₂ := ⟨4, 0, 0, 8253903530175518672582331903915110868636, 0⟩)
  · have h := mod0_sn 1650780706035103734516466380783022173727 3
    exact h
  apply stepNat_haltsIn_add (m := 38518216474152420472050882218270517386972) (c₂ := ⟨4, 0, 0, 13756505883625864454303886506525184781061, 0⟩)
  · have h := mod0_sn 2751301176725172890860777301305036956212 3
    exact h
  apply stepNat_haltsIn_add (m := 64197027456920700786751470363784195644954) (c₂ := ⟨3, 0, 0, 22927509806043107423839810844208641301769, 0⟩)
  · have h := mod2_sn 4585501961208621484767962168841728260353 3
    exact h
  apply stepNat_haltsIn_add (m := 106995045761534501311252450606306992741594) (c₂ := ⟨4, 0, 0, 38212516343405179039733018073681068836283, 0⟩)
  · have h := mod1_sn 7642503268681035807946603614736213767256 2
    exact h
  apply stepNat_haltsIn_add (m := 178325076269224168852087417677178321235990) (c₂ := ⟨3, 0, 0, 63687527239008631732888363456135114727139, 0⟩)
  · have h := mod2_sn 12737505447801726346577672691227022945427 3
    exact h
  apply stepNat_haltsIn_add (m := 297208460448706948086812362795297202059986) (c₂ := ⟨3, 0, 0, 106145878731681052888147272426891857878566, 0⟩)
  · have h := mod0_sn 21229175746336210577629454485378371575713 2
    exact h
  apply stepNat_haltsIn_add (m := 495347434081178246811353937992162003433312) (c₂ := ⟨3, 0, 0, 176909797886135088146912120711486429797611, 0⟩)
  · have h := mod0_sn 35381959577227017629382424142297285959522 2
    exact h
  apply stepNat_haltsIn_add (m := 825579056801963744685589896653603339055522) (c₂ := ⟨3, 0, 0, 294849663143558480244853534519144049662686, 0⟩)
  · have h := mod0_sn 58969932628711696048970706903828809932537 2
    exact h
  apply stepNat_haltsIn_add (m := 1375965094669939574475983161089338898425872) (c₂ := ⟨3, 0, 0, 491416105239264133741422557531906749437811, 0⟩)
  · have h := mod0_sn 98283221047852826748284511506381349887562 2
    exact h
  apply stepNat_haltsIn_add (m := 2293275157783232624126638601815564830709790) (c₂ := ⟨4, 0, 0, 819026842065440222902370929219844582396353, 0⟩)
  · have h := mod1_sn 163805368413088044580474185843968916479270 2
    exact h
  apply stepNat_haltsIn_add (m := 3822125262972054373544397669692608051182986) (c₂ := ⟨5, 0, 0, 1365044736775733704837284882033074303993923, 0⟩)
  · have h := mod1_sn 273008947355146740967456976406614860798784 3
    exact h
  apply stepNat_haltsIn_add (m := 6370208771620090622573996116154346751971646) (c₂ := ⟨6, 0, 0, 2275074561292889508062141470055123839989873, 0⟩)
  · have h := mod1_sn 455014912258577901612428294011024767997974 4
    exact h
  apply stepNat_haltsIn_add (m := 10617014619366817704289993526923911253286078) (c₂ := ⟨6, 0, 0, 3791790935488149180103569116758539733316456, 0⟩)
  · have h := mod0_sn 758358187097629836020713823351707946663291 5
    exact h
  apply stepNat_haltsIn_add (m := 17695024365611362840483322544873185422143464) (c₂ := ⟨5, 0, 0, 6319651559146915300172615194597566222194094, 0⟩)
  · have h := mod2_sn 1263930311829383060034523038919513244438818 5
    exact h
  apply stepNat_haltsIn_add (m := 29491707276018938067472204241455309036905776) (c₂ := ⟨5, 0, 0, 10532752598578192166954358657662610370323491, 0⟩)
  · have h := mod0_sn 2106550519715638433390871731532522074064698 4
    exact h
  apply stepNat_haltsIn_add (m := 49152845460031563445787007069092181728176294) (c₂ := ⟨4, 0, 0, 17554587664296986944923931096104350617205819, 0⟩)
  · have h := mod2_sn 3510917532859397388984786219220870123441163 4
    exact h
  apply stepNat_haltsIn_add (m := 81921409100052605742978345115153636213627158) (c₂ := ⟨3, 0, 0, 29257646107161644908206551826840584362009699, 0⟩)
  · have h := mod2_sn 5851529221432328981641310365368116872401939 3
    exact h
  apply stepNat_haltsIn_add (m := 136535681833421009571630575191922727022711934) (c₂ := ⟨4, 0, 0, 48762743511936074847010919711400973936682833, 0⟩)
  · have h := mod1_sn 9752548702387214969402183942280194787336566 2
    exact h
  apply stepNat_haltsIn_add (m := 227559469722368349286050958653204545037853226) (c₂ := ⟨5, 0, 0, 81271239186560124745018199519001623227804723, 0⟩)
  · have h := mod1_sn 16254247837312024949003639903800324645560944 3
    exact h
  apply stepNat_haltsIn_add (m := 379265782870613915476751597755340908396422046) (c₂ := ⟨6, 0, 0, 135452065310933541241696999198336038713007873, 0⟩)
  · have h := mod1_sn 27090413062186708248339399839667207742601574 4
    exact h
  apply stepNat_haltsIn_add (m := 632109638117689859127919329592234847327370078) (c₂ := ⟨6, 0, 0, 225753442184889235402828331997226731188346456, 0⟩)
  · have h := mod0_sn 45150688436977847080565666399445346237669291 5
    exact h
  apply stepNat_haltsIn_add (m := 1053516063529483098546532215987058078878950132) (c₂ := ⟨6, 0, 0, 376255736974815392338047219995377885313910761, 0⟩)
  · have h := mod0_sn 75251147394963078467609443999075577062782152 5
    exact h
  apply stepNat_haltsIn_add (m := 1755860105882471830910887026645096798131583554) (c₂ := ⟨5, 0, 0, 627092894958025653896745366658963142189851269, 0⟩)
  · have h := mod2_sn 125418578991605130779349073331792628437970253 5
    exact h
  apply stepNat_haltsIn_add (m := 2926433509804119718184811711075161330219305926) (c₂ := ⟨5, 0, 0, 1045154824930042756494575611098271903649752116, 0⟩)
  · have h := mod0_sn 209030964986008551298915122219654380729950423 4
    exact h
  apply stepNat_haltsIn_add (m := 4877389183006866196974686185125268883698843212) (c₂ := ⟨5, 0, 0, 1741924708216737927490959351830453172749586861, 0⟩)
  · have h := mod0_sn 348384941643347585498191870366090634549917372 4
    exact h
  apply stepNat_haltsIn_add (m := 8128981971678110328291143641875448139498072022) (c₂ := ⟨5, 0, 0, 2903207847027896545818265586384088621249311436, 0⟩)
  · have h := mod0_sn 580641569405579309163653117276817724249862287 4
    exact h
  apply stepNat_haltsIn_add (m := 13548303286130183880485239403125746899163453372) (c₂ := ⟨5, 0, 0, 4838679745046494243030442643973481035415519061, 0⟩)
  · have h := mod0_sn 967735949009298848606088528794696207083103812 4
    exact h
  apply stepNat_haltsIn_add (m := 22580505476883639800808732338542911498605755622) (c₂ := ⟨5, 0, 0, 8064466241744157071717404406622468392359198436, 0⟩)
  · have h := mod0_sn 1612893248348831414343480881324493678471839687 4
    exact h
  apply stepNat_haltsIn_add (m := 37634175794806066334681220564238185831009592704) (c₂ := ⟨4, 0, 0, 13440777069573595119529007344370780653931997394, 0⟩)
  · have h := mod2_sn 2688155413914719023905801468874156130786399478 4
    exact h
  apply stepNat_haltsIn_add (m := 62723626324676777224468700940396976385015987844) (c₂ := ⟨5, 0, 0, 22401295115955991865881678907284634423219995658, 0⟩)
  · have h := mod1_sn 4480259023191198373176335781456926884643999131 3
    exact h
  apply stepNat_haltsIn_add (m := 104539377207794628707447834900661627308359979740) (c₂ := ⟨4, 0, 0, 37335491859926653109802798178807724038699992764, 0⟩)
  · have h := mod2_sn 7467098371985330621960559635761544807739998552 4
    exact h
  apply stepNat_haltsIn_add (m := 174232295346324381179079724834436045513933299568) (c₂ := ⟨3, 0, 0, 62225819766544421849671330298012873397833321274, 0⟩)
  · have h := mod2_sn 12445163953308884369934266059602574679566664254 3
    exact h
  apply stepNat_haltsIn_add (m := 290387158910540635298466208057393409189888832616) (c₂ := ⟨3, 0, 0, 103709699610907369749452217163354788996388868791, 0⟩)
  · have h := mod0_sn 20741939922181473949890443432670957799277773758 2
    exact h
  apply stepNat_haltsIn_add (m := 483978598184234392164110346762322348649814721030) (c₂ := ⟨4, 0, 0, 172849499351512282915753695272257981660648114653, 0⟩)
  · have h := mod1_sn 34569899870302456583150739054451596332129622930 2
    exact h
  apply stepNat_haltsIn_add (m := 806630996973723986940183911270537247749691201718) (c₂ := ⟨4, 0, 0, 288082498919187138192922825453763302767746857756, 0⟩)
  · have h := mod0_sn 57616499783837427638584565090752660553549371551 3
    exact h
  apply stepNat_haltsIn_add (m := 1344384994956206644900306518784228746249485336200) (c₂ := ⟨5, 0, 0, 480137498198645230321538042422938837946244762928, 0⟩)
  · have h := mod1_sn 96027499639729046064307608484587767589248952585 3
    exact h
  apply stepNat_haltsIn_add (m := 2240641658260344408167177531307047910415808893668) (c₂ := ⟨5, 0, 0, 800229163664408717202563404038231396577074604881, 0⟩)
  · have h := mod0_sn 160045832732881743440512680807646279315414920976 4
    exact h
  apply stepNat_haltsIn_add (m := 3734402763767240680278629218845079850693014822782) (c₂ := ⟨5, 0, 0, 1333715272774014528670939006730385660961791008136, 0⟩)
  · have h := mod0_sn 266743054554802905734187801346077132192358201627 4
    exact h
  apply stepNat_haltsIn_add (m := 6224004606278734467131048698075133084488358037972) (c₂ := ⟨5, 0, 0, 2222858787956690881118231677883976101602985013561, 0⟩)
  · have h := mod0_sn 444571757591338176223646335576795220320597002712 4
    exact h
  apply stepNat_haltsIn_add (m := 10373341010464557445218414496791888474147263396622) (c₂ := ⟨5, 0, 0, 3704764646594484801863719463139960169338308355936, 0⟩)
  · have h := mod0_sn 740952929318896960372743892627992033867661671187 4
    exact h
  apply stepNat_haltsIn_add (m := 17288901684107595742030690827986480790245438994372) (c₂ := ⟨5, 0, 0, 6174607744324141336439532438566600282230513926561, 0⟩)
  · have h := mod0_sn 1234921548864828267287906487713320056446102785312 4
    exact h
  apply stepNat_haltsIn_add (m := 28814836140179326236717818046644134650409064990622) (c₂ := ⟨5, 0, 0, 10291012907206902227399220730944333803717523210936, 0⟩)
  · have h := mod0_sn 2058202581441380445479844146188866760743504642187 4
    exact h
  apply stepNat_haltsIn_add (m := 48024726900298877061196363411073557750681774984372) (c₂ := ⟨5, 0, 0, 17151688178678170378998701218240556339529205351561, 0⟩)
  · have h := mod0_sn 3430337635735634075799740243648111267905841070312 4
    exact h
  apply stepNat_haltsIn_add (m := 80041211500498128435327272351789262917802958307290) (c₂ := ⟨6, 0, 0, 28586146964463617298331168697067593899215342252603, 0⟩)
  · have h := mod1_sn 5717229392892723459666233739413518779843068450520 4
    exact h
  apply stepNat_haltsIn_add (m := 133402019167496880725545453919648771529671597178818) (c₂ := ⟨6, 0, 0, 47643578274106028830551947828445989832025570421006, 0⟩)
  · have h := mod0_sn 9528715654821205766110389565689197966405114084201 5
    exact h
  apply stepNat_haltsIn_add (m := 222336698612494801209242423199414619216119328631364) (c₂ := ⟨5, 0, 0, 79405963790176714717586579714076649720042617368344, 0⟩)
  · have h := mod2_sn 15881192758035342943517315942815329944008523473668 5
    exact h
  apply stepNat_haltsIn_add (m := 370561164354158002015404038665691032026865547718944) (c₂ := ⟨6, 0, 0, 132343272983627857862644299523461082866737695613908, 0⟩)
  · have h := mod1_sn 26468654596725571572528859904692216573347539122781 4
    exact h
  apply stepNat_haltsIn_add (m := 617601940590263336692340064442818386711442579531576) (c₂ := ⟨7, 0, 0, 220572121639379763104407165872435138111229492689848, 0⟩)
  · have h := mod1_sn 44114424327875952620881433174487027622245898537969 5
    exact h
  apply stepNat_haltsIn_add (m := 1029336567650438894487233440738030644519070965885960) (c₂ := ⟨6, 0, 0, 367620202732299605174011943120725230185382487816414, 0⟩)
  · have h := mod2_sn 73524040546459921034802388624145046037076497563282 6
    exact h
  apply stepNat_haltsIn_add (m := 1715560946084064824145389067896717740865118276476604) (c₂ := ⟨7, 0, 0, 612700337887166008623353238534542050308970813027358, 0⟩)
  · have h := mod1_sn 122540067577433201724670647706908410061794162605471 5
    exact h
  apply stepNat_haltsIn_add (m := 2859268243473441373575648446494529568108530460794340) (c₂ := ⟨6, 0, 0, 1021167229811943347705588730890903417181618021712264, 0⟩)
  · have h := mod2_sn 204233445962388669541117746178180683436323604342452 6
    exact h
  apply stepNat_haltsIn_add (m := 4765447072455735622626080744157549280180884101323904) (c₂ := ⟨7, 0, 0, 1701945383019905579509314551484839028636030036187108, 0⟩)
  · have h := mod1_sn 340389076603981115901862910296967805727206007237421 5
    exact h
  apply stepNat_haltsIn_add (m := 7942411787426226037710134573595915466968140168873176) (c₂ := ⟨8, 0, 0, 2836575638366509299182190919141398381060050060311848, 0⟩)
  · have h := mod1_sn 567315127673301859836438183828279676212010012062369 6
    exact h
  apply stepNat_haltsIn_add (m := 13237352979043710062850224289326525778280233614788628) (c₂ := ⟨8, 0, 0, 4727626063944182165303651531902330635100083433853081, 0⟩)
  · have h := mod0_sn 945525212788836433060730306380466127020016686770616 7
    exact h
  apply stepNat_haltsIn_add (m := 22062254965072850104750373815544209630467056024647714) (c₂ := ⟨7, 0, 0, 7879376773240303608839419219837217725166805723088469, 0⟩)
  · have h := mod2_sn 1575875354648060721767883843967443545033361144617693 7
    exact h
  apply stepNat_haltsIn_add (m := 36770424941788083507917289692573682717445093374412858) (c₂ := ⟨6, 0, 0, 13132294622067172681399032033062029541944676205147449, 0⟩)
  · have h := mod2_sn 2626458924413434536279806406612405908388935241029489 6
    exact h
  apply stepNat_haltsIn_add (m := 61284041569646805846528816154289471195741822290688098) (c₂ := ⟨5, 0, 0, 21887157703445287802331720055103382569907793675245749, 0⟩)
  · have h := mod2_sn 4377431540689057560466344011020676513981558735049149 5
    exact h
  apply stepNat_haltsIn_add (m := 102140069282744676410881360257149118659569703817813498) (c₂ := ⟨4, 0, 0, 36478596172408813003886200091838970949846322792076249, 0⟩)
  · have h := mod2_sn 7295719234481762600777240018367794189969264558415249 4
    exact h
  apply stepNat_haltsIn_add (m := 170233448804574460684802267095248531099282839696355834) (c₂ := ⟨5, 0, 0, 60797660287348021673143666819731618249743871320127083, 0⟩)
  · have h := mod1_sn 12159532057469604334628733363946323649948774264025416 3
    exact h
  apply stepNat_haltsIn_add (m := 283722414674290767808003778492080885165471399493926390) (c₂ := ⟨4, 0, 0, 101329433812246702788572778032886030416239785533545139, 0⟩)
  · have h := mod2_sn 20265886762449340557714555606577206083247957106709027 4
    exact h
  apply stepNat_haltsIn_add (m := 472870691123817946346672964153468141942452332489877318) (c₂ := ⟨3, 0, 0, 168882389687077837980954630054810050693732975889241899, 0⟩)
  · have h := mod2_sn 33776477937415567596190926010962010138746595177848379 3
    exact h
  apply stepNat_haltsIn_add (m := 788117818539696577244454940255780236570753887483128866) (c₂ := ⟨3, 0, 0, 281470649478463063301591050091350084489554959815403166, 0⟩)
  · have h := mod0_sn 56294129895692612660318210018270016897910991963080633 2
    exact h
  apply stepNat_haltsIn_add (m := 1313529697566160962074091567092967060951256479138548112) (c₂ := ⟨3, 0, 0, 469117749130771772169318416818916807482591599692338611, 0⟩)
  · have h := mod0_sn 93823549826154354433863683363783361496518319938467722 2
    exact h
  apply stepNat_haltsIn_add (m := 2189216162610268270123485945154945101585427465230913522) (c₂ := ⟨3, 0, 0, 781862915217952953615530694698194679137652666153897686, 0⟩)
  · have h := mod0_sn 156372583043590590723106138939638935827530533230779537 2
    exact h
  apply stepNat_haltsIn_add (m := 3648693604350447116872476575258241835975712442051522540) (c₂ := ⟨4, 0, 0, 1303104858696588256025884491163657798562754443589829478, 0⟩)
  · have h := mod1_sn 260620971739317651205176898232731559712550888717965895 2
    exact h
  apply stepNat_haltsIn_add (m := 6081156007250745194787460958763736393292854070085870900) (c₂ := ⟨3, 0, 0, 2171841431160980426709807485272762997604590739316382464, 0⟩)
  · have h := mod2_sn 434368286232196085341961497054552599520918147863276492 3
    exact h
  apply stepNat_haltsIn_add (m := 10135260012084575324645768264606227322154756783476451504) (c₂ := ⟨4, 0, 0, 3619735718601634044516345808787938329340984565527304108, 0⟩)
  · have h := mod1_sn 723947143720326808903269161757587665868196913105460821 2
    exact h
  apply stepNat_haltsIn_add (m := 16892100020140958874409613774343712203591261305794085840) (c₂ := ⟨3, 0, 0, 6032892864336056740860576347979897215568307609212173514, 0⟩)
  · have h := mod2_sn 1206578572867211348172115269595979443113661521842434702 3
    exact h
  apply stepNat_haltsIn_add (m := 28153500033568264790682689623906187005985435509656809736) (c₂ := ⟨3, 0, 0, 10054821440560094568100960579966495359280512682020289191, 0⟩)
  · have h := mod0_sn 2010964288112018913620192115993299071856102536404057838 2
    exact h
  apply stepNat_haltsIn_add (m := 46922500055947107984471149373176978343309059182761349562) (c₂ := ⟨3, 0, 0, 16758035734266824280168267633277492265467521136700481986, 0⟩)
  · have h := mod0_sn 3351607146853364856033653526655498453093504227340096397 2
    exact h
  apply stepNat_haltsIn_add (m := 78204166759911846640785248955294963905515098637935582604) (c₂ := ⟨2, 0, 0, 27930059557111373800280446055462487109112535227834136644, 0⟩)
  · have h := mod2_sn 5586011911422274760056089211092497421822507045566827328 2
    exact h
  apply stepNat_haltsIn_add (m := 130340277933186411067975414925491606509191831063225971008) (c₂ := ⟨1, 0, 0, 46550099261852289667134076759104145181854225379723561074, 0⟩)
  · have h := mod2_sn 9310019852370457933426815351820829036370845075944712214 1
    exact h
  apply stepNat_haltsIn_add (m := 217233796555310685113292358209152677515319718438709951684) (c₂ := ⟨2, 0, 0, 77583498769753816111890127931840241969757042299539268458, 0⟩)
  · have h := mod1_sn 15516699753950763222378025586368048393951408459907853691 0
    exact h
  apply stepNat_haltsIn_add (m := 362056327592184475188820597015254462525532864064516586140) (c₂ := ⟨1, 0, 0, 129305831282923026853150213219733736616261737165898780764, 0⟩)
  · have h := mod2_sn 25861166256584605370630042643946747323252347433179756152 1
    exact h
  apply stepNat_haltsIn_add (m := 603427212653640791981367661692090770875888106774194310236) (c₂ := ⟨1, 0, 0, 215509718804871711421917022032889561027102895276497967941, 0⟩)
  · have h := mod0_sn 43101943760974342284383404406577912205420579055299593588 0
    exact h
  apply stepNat_haltsIn_add (m := 1005712021089401319968946102820151284793146844623657183730) (c₂ := ⟨2, 0, 0, 359182864674786185703195036721482601711838158794163279903, 0⟩)
  · have h := mod1_sn 71836572934957237140639007344296520342367631758832655980 0
    exact h
  apply stepNat_haltsIn_add (m := 1676186701815668866614910171366918807988578074372761972886) (c₂ := ⟨3, 0, 0, 598638107791310309505325061202471002853063597990272133173, 0⟩)
  · have h := mod1_sn 119727621558262061901065012240494200570612719598054426634 1
    exact h
  apply stepNat_haltsIn_add (m := 2793644503026114777691516952278198013314296790621269954810) (c₂ := ⟨2, 0, 0, 997730179652183849175541768670785004755105996650453555289, 0⟩)
  · have h := mod2_sn 199546035930436769835108353734157000951021199330090711057 2
    exact h
  apply stepNat_haltsIn_add (m := 4656074171710191296152528253796996688857161317702116591354) (c₂ := ⟨3, 0, 0, 1662883632753639748625902947784641674591843327750755925483, 0⟩)
  · have h := mod1_sn 332576726550727949725180589556928334918368665550151185096 1
    exact h
  apply stepNat_haltsIn_add (m := 7760123619516985493587547089661661148095268862836860985590) (c₂ := ⟨2, 0, 0, 2771472721256066247709838246307736124319738879584593209139, 0⟩)
  · have h := mod2_sn 554294544251213249541967649261547224863947775916918641827 2
    exact h
  apply stepNat_haltsIn_add (m := 12933539365861642489312578482769435246825448104728101642654) (c₂ := ⟨3, 0, 0, 4619121202093443746183063743846226873866231465974322015233, 0⟩)
  · have h := mod1_sn 923824240418688749236612748769245374773246293194864403046 1
    exact h
  apply stepNat_haltsIn_add (m := 21555898943102737482187630804615725411375746841213502737758) (c₂ := ⟨3, 0, 0, 7698535336822406243638439573077044789777052443290536692056, 0⟩)
  · have h := mod0_sn 1539707067364481248727687914615408957955410488658107338411 2
    exact h
  apply stepNat_haltsIn_add (m := 35926498238504562470312718007692875685626244735355837896264) (c₂ := ⟨2, 0, 0, 12830892228037343739397399288461741316295087405484227820094, 0⟩)
  · have h := mod2_sn 2566178445607468747879479857692348263259017481096845564018 2
    exact h
  apply stepNat_haltsIn_add (m := 59877497064174270783854530012821459476043741225593063160444) (c₂ := ⟨3, 0, 0, 21384820380062239565662332147436235527158479009140379700158, 0⟩)
  · have h := mod1_sn 4276964076012447913132466429487247105431695801828075940031 1
    exact h
  apply stepNat_haltsIn_add (m := 99795828440290451306424216688035765793406235375988438600740) (c₂ := ⟨2, 0, 0, 35641367300103732609437220245727059211930798348567299500264, 0⟩)
  · have h := mod2_sn 7128273460020746521887444049145411842386159669713459900052 2
    exact h
  apply stepNat_haltsIn_add (m := 166326380733817418844040361146726276322343725626647397667904) (c₂ := ⟨3, 0, 0, 59402278833506221015728700409545098686551330580945499167108, 0⟩)
  · have h := mod1_sn 11880455766701244203145740081909019737310266116189099833421 1
    exact h
  apply stepNat_haltsIn_add (m := 277210634556362364740067268577877127203906209377745662779840) (c₂ := ⟨2, 0, 0, 99003798055843701692881167349241831144252217634909165278514, 0⟩)
  · have h := mod2_sn 19800759611168740338576233469848366228850443526981833055702 2
    exact h
  apply stepNat_haltsIn_add (m := 462017724260603941233445447629795212006510348962909437966404) (c₂ := ⟨3, 0, 0, 165006330093072836154801945582069718573753696058181942130858, 0⟩)
  · have h := mod1_sn 33001266018614567230960389116413943714750739211636388426171 1
    exact h
  apply stepNat_haltsIn_add (m := 770029540434339902055742412716325353344183914938182396610676) (c₂ := ⟨4, 0, 0, 275010550155121393591336575970116197622922826763636570218098, 0⟩)
  · have h := mod1_sn 55002110031024278718267315194023239524584565352727314043619 2
    exact h
  apply stepNat_haltsIn_add (m := 1283382567390566503426237354527208922240306524896970661017796) (c₂ := ⟨5, 0, 0, 458350916925202322652227626616860329371538044606060950363498, 0⟩)
  · have h := mod1_sn 91670183385040464530445525323372065874307608921212190072699 3
    exact h
  apply stepNat_haltsIn_add (m := 2138970945650944172377062257545348203733844208161617768362996) (c₂ := ⟨6, 0, 0, 763918194875337204420379377694767215619230074343434917272498, 0⟩)
  · have h := mod1_sn 152783638975067440884075875538953443123846014868686983454499 4
    exact h
  apply stepNat_haltsIn_add (m := 3564951576084906953961770429242247006223073680269362947271660) (c₂ := ⟨5, 0, 0, 1273196991458895340700632296157945359365383457239058195454164, 0⟩)
  · have h := mod2_sn 254639398291779068140126459231589071873076691447811639090832 5
    exact h
  apply stepNat_haltsIn_add (m := 5941585960141511589936284048737078343705122800448938245452768) (c₂ := ⟨4, 0, 0, 2121994985764825567834387160263242265608972428731763659090274, 0⟩)
  · have h := mod2_sn 424398997152965113566877432052648453121794485746352731818054 4
    exact h
  apply stepNat_haltsIn_add (m := 9902643266902519316560473414561797239508538000748230409087948) (c₂ := ⟨3, 0, 0, 3536658309608042613057311933772070442681620714552939431817124, 0⟩)
  · have h := mod2_sn 707331661921608522611462386754414088536324142910587886363424 3
    exact h
  apply stepNat_haltsIn_add (m := 16504405444837532194267455690936328732514230001247050681813248) (c₂ := ⟨2, 0, 0, 5894430516013404355095519889620117404469367857588232386361874, 0⟩)
  · have h := mod2_sn 1178886103202680871019103977924023480893873571517646477272374 2
    exact h
  apply stepNat_haltsIn_add (m := 27507342408062553657112426151560547887523716668745084469688748) (c₂ := ⟨1, 0, 0, 9824050860022340591825866482700195674115613095980387310603124, 0⟩)
  · have h := mod2_sn 1964810172004468118365173296540039134823122619196077462120624 1
    exact h
  apply stepNat_haltsIn_add (m := 45845570680104256095187376919267579812539527781241807449481248) (c₂ := ⟨0, 0, 0, 16373418100037234319709777471166992790192688493300645517671874, 0⟩)
  · have h := mod2_sn 3274683620007446863941955494233398558038537698660129103534374 0
    exact h
  exact halt_sn 16373418100037234319709777471166992790192688493300645517671874

end Sz22_halted_692_4