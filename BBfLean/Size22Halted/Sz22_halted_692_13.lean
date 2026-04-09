import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_halted_692 #13: [9/35, 125/21, 4/5, 7/2, 15/7]

Vector representation:
```
 0  2 -1 -1
 0 -1  3 -1
 2  0 -1  0
-1  0  0  1
 0  1  1 -1
```

This Fractran program halts in 83495859887 steps.

Author: Claude
-/

namespace Sz22_halted_692_13

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b+1, c, d+1⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c+1, d⟩
  | _ => none

private theorem r4_gen : ∀ k a d, (⟨a + k, 0, 0, d⟩ : Q) [fm]⊢^{k} ⟨a, 0, 0, d + k⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · simp; rfl
  rw [show a + (k + 1) = (a + k) + 1 from by ring, show k + 1 = 1 + k from by ring]
  apply stepNat_trans 1 k
  · show fm ⟨(a + k) + 1, 0, 0, d⟩ = some ⟨a + k, 0, 0, d + 1⟩; simp [fm]
  rw [show d + (1 + k) = (d + 1) + k from by ring]; exact ih a (d + 1)

private theorem r4_sn : ∀ k d, (⟨k, 0, 0, d⟩ : Q) [fm]⊢^{k} ⟨0, 0, 0, d + k⟩ := by
  intro k d; have h := r4_gen k 0 d; simp at h; exact h

private theorem r5r1_open_sn : ∀ d, (⟨0, 0, 0, d + 2⟩ : Q) [fm]⊢^{2} ⟨0, 3, 0, d⟩ := by
  intro d; show stepNat fm 2 ⟨0, 0, 0, d + 2⟩ = some ⟨0, 3, 0, d⟩; rfl

private theorem r2r1_chain_gen : ∀ k b d, (⟨0, b + 1, 0, d + 4 * k⟩ : Q) [fm]⊢^{4 * k} ⟨0, b + 1 + 5 * k, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · simp; rfl
  rw [show d + 4 * (k + 1) = (d + 4 * k) + 4 from by ring,
      show 4 * (k + 1) = 4 + 4 * k from by ring]
  apply stepNat_trans 4 (4 * k)
  · rw [show (d + 4 * k) + 4 = (d + 4 * k + 3) + 1 from by ring]
    show stepNat fm 4 ⟨0, b + 1, 0, (d + 4 * k + 3) + 1⟩ = some ⟨0, b + 6, 0, d + 4 * k⟩; rfl
  rw [show b + 6 = (b + 5) + 1 from by ring]
  have h := ih (b + 5) d
  rw [show b + 5 + 1 + 5 * k = b + 1 + 5 * (k + 1) from by ring] at h; exact h

private theorem r2r1_chain_sn : ∀ k d, (⟨0, 3, 0, d + 4 * k⟩ : Q) [fm]⊢^{4 * k} ⟨0, 3 + 5 * k, 0, d⟩ := by
  intro k d; have h := r2r1_chain_gen k 2 d; simp at h
  rw [show 2 + 1 + 5 * k = 3 + 5 * k from by ring] at h; exact h

private theorem partial_d3_sn : ∀ b, (⟨0, b + 1, 0, 3⟩ : Q) [fm]⊢^{4} ⟨2, b + 4, 0, 0⟩ := by
  intro b; show stepNat fm 4 ⟨0, b + 1, 0, 3⟩ = some ⟨2, b + 4, 0, 0⟩; rfl

private theorem partial_d2_sn : ∀ b, (⟨0, b + 1, 0, 2⟩ : Q) [fm]⊢^{4} ⟨4, b + 2, 0, 0⟩ := by
  intro b; show stepNat fm 4 ⟨0, b + 1, 0, 2⟩ = some ⟨4, b + 2, 0, 0⟩; rfl

private theorem partial_d1_sn : ∀ b, (⟨0, b + 1, 0, 1⟩ : Q) [fm]⊢^{4} ⟨6, b, 0, 0⟩ := by
  intro b; show stepNat fm 4 ⟨0, b + 1, 0, 1⟩ = some ⟨6, b, 0, 0⟩; rfl

private theorem drain_ab_gen : ∀ k a b, (⟨a + 1, b + k, 0, 0⟩ : Q) [fm]⊢^{5 * k} ⟨a + 1 + 5 * k, b, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · simp; rfl
  rw [show b + (k + 1) = (b + k) + 1 from by ring, show 5 * (k + 1) = 5 + 5 * k from by ring]
  apply stepNat_trans 5 (5 * k)
  · show stepNat fm 5 ⟨a + 1, (b + k) + 1, 0, 0⟩ = some ⟨a + 6, b + k, 0, 0⟩; rfl
  rw [show a + 6 = (a + 5) + 1 from by ring]
  have h := ih (a + 5) b
  rw [show a + 5 + 1 + 5 * k = a + 1 + (5 + 5 * k) from by ring] at h; exact h

private theorem drain_ab_sn : ∀ k a, (⟨a + 1, k, 0, 0⟩ : Q) [fm]⊢^{5 * k} ⟨a + 1 + 5 * k, 0, 0, 0⟩ := by
  intro k a; have h := drain_ab_gen k a 0; simp at h; exact h

private theorem macro_r3_sn : ∀ q, (⟨0, 0, 0, 4 * q + 3⟩ : Q) [fm]⊢^{54 * q + 32} ⟨0, 0, 0, 25 * q + 16⟩ := by
  intro q
  rw [show (54 * q + 32 : ℕ) = 2 + (4 * q + (4 + (5 * (5 * q + 2) + (25 * q + 16)))) from by ring]
  apply stepNat_trans 2 _
  · rw [show (4 * q + 3 : ℕ) = (4 * q + 1) + 2 from by ring]; exact r5r1_open_sn (4 * q + 1)
  rw [show (4 * q + 1 : ℕ) = 1 + 4 * q from by ring]
  apply stepNat_trans (4 * q) _
  · exact r2r1_chain_sn q 1
  rw [show 3 + 5 * q = (5 * q + 2) + 1 from by ring]
  apply stepNat_trans 4 _ (partial_d1_sn (5 * q + 2))
  rw [show (6 : ℕ) = 5 + 1 from by ring]
  apply stepNat_trans (5 * (5 * q + 2)) _
  · exact drain_ab_sn (5 * q + 2) 5
  rw [show 5 + 1 + 5 * (5 * q + 2) = 25 * q + 16 from by ring]
  have h := r4_sn (25 * q + 16) 0
  rw [show 0 + (25 * q + 16) = 25 * q + 16 from by ring] at h; exact h

private theorem macro_r1_sn : ∀ q, (⟨0, 0, 0, 4 * q + 5⟩ : Q) [fm]⊢^{54 * q + 68} ⟨0, 0, 0, 25 * q + 32⟩ := by
  intro q
  rw [show (54 * q + 68 : ℕ) = 2 + (4 * q + (4 + (5 * (5 * q + 6) + (25 * q + 32)))) from by ring]
  apply stepNat_trans 2 _
  · rw [show (4 * q + 5 : ℕ) = (4 * q + 3) + 2 from by ring]; exact r5r1_open_sn (4 * q + 3)
  rw [show (4 * q + 3 : ℕ) = 3 + 4 * q from by ring]
  apply stepNat_trans (4 * q) _
  · exact r2r1_chain_sn q 3
  rw [show 3 + 5 * q = (5 * q + 2) + 1 from by ring]
  apply stepNat_trans 4 _ (partial_d3_sn (5 * q + 2))
  rw [show (5 * q + 2 + 4 : ℕ) = 5 * q + 6 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  apply stepNat_trans (5 * (5 * q + 6)) _
  · exact drain_ab_sn (5 * q + 6) 1
  rw [show 1 + 1 + 5 * (5 * q + 6) = 25 * q + 32 from by ring]
  have h := r4_sn (25 * q + 32) 0
  rw [show 0 + (25 * q + 32) = 25 * q + 32 from by ring] at h; exact h

private theorem macro_r0_sn : ∀ q, (⟨0, 0, 0, 4 * q + 4⟩ : Q) [fm]⊢^{54 * q + 50} ⟨0, 0, 0, 25 * q + 24⟩ := by
  intro q
  rw [show (54 * q + 50 : ℕ) = 2 + (4 * q + (4 + (5 * (5 * q + 4) + (25 * q + 24)))) from by ring]
  apply stepNat_trans 2 _
  · rw [show (4 * q + 4 : ℕ) = (4 * q + 2) + 2 from by ring]; exact r5r1_open_sn (4 * q + 2)
  rw [show (4 * q + 2 : ℕ) = 2 + 4 * q from by ring]
  apply stepNat_trans (4 * q) _
  · exact r2r1_chain_sn q 2
  rw [show 3 + 5 * q = (5 * q + 2) + 1 from by ring]
  apply stepNat_trans 4 _ (partial_d2_sn (5 * q + 2))
  rw [show (5 * q + 2 + 2 : ℕ) = 5 * q + 4 from by ring, show (4 : ℕ) = 3 + 1 from by ring]
  apply stepNat_trans (5 * (5 * q + 4)) _
  · exact drain_ab_sn (5 * q + 4) 3
  rw [show 3 + 1 + 5 * (5 * q + 4) = 25 * q + 24 from by ring]
  have h := r4_sn (25 * q + 24) 0
  rw [show 0 + (25 * q + 24) = 25 * q + 24 from by ring] at h; exact h

private theorem macro_halt_sn : ∀ q, (⟨0, 0, 0, 4 * q + 2⟩ : Q) [fm]⊢^{4 * q + 2} ⟨0, 5 * q + 3, 0, 0⟩ := by
  intro q
  rw [show (4 * q + 2 : ℕ) = 2 + 4 * q from by ring]
  apply stepNat_trans 2 (4 * q)
  · rw [show (2 + 4 * q : ℕ) = (4 * q) + 2 from by ring]; exact r5r1_open_sn (4 * q)
  have h := r2r1_chain_gen q 2 0
  simp at h
  rw [show 2 + 1 + 5 * q = 5 * q + 3 from by ring] at h; exact h

theorem fm_haltsIn : haltsIn fm c₀ 83495859887 := by
  apply stepNat_haltsIn_add (m := 1) (c₂ := ⟨0, 0, 0, 1⟩)
  · show fm c₀ = some ⟨0, 0, 0, 1⟩; rfl
  apply stepNat_haltsIn_add (m := 14) (c₂ := ⟨0, 0, 0, 7⟩)
  · show stepNat fm 14 ⟨0, 0, 0, 1⟩ = some ⟨0, 0, 0, 7⟩; rfl
  apply stepNat_haltsIn_add (m := 86) (c₂ := ⟨0, 0, 0, 41⟩)
  · rw [show (7 : ℕ) = 4 * 1 + 3 from by ring, show (41 : ℕ) = 25 * 1 + 16 from by ring,
      show (86 : ℕ) = 54 * 1 + 32 from by ring]; exact macro_r3_sn 1
  apply stepNat_haltsIn_add (m := 554) (c₂ := ⟨0, 0, 0, 257⟩)
  · rw [show (41 : ℕ) = 4 * 9 + 5 from by ring, show (257 : ℕ) = 25 * 9 + 32 from by ring,
      show (554 : ℕ) = 54 * 9 + 68 from by ring]; exact macro_r1_sn 9
  apply stepNat_haltsIn_add (m := 3470) (c₂ := ⟨0, 0, 0, 1607⟩)
  · rw [show (257 : ℕ) = 4 * 63 + 5 from by ring, show (1607 : ℕ) = 25 * 63 + 32 from by ring,
      show (3470 : ℕ) = 54 * 63 + 68 from by ring]; exact macro_r1_sn 63
  apply stepNat_haltsIn_add (m := 21686) (c₂ := ⟨0, 0, 0, 10041⟩)
  · rw [show (1607 : ℕ) = 4 * 401 + 3 from by ring, show (10041 : ℕ) = 25 * 401 + 16 from by ring,
      show (21686 : ℕ) = 54 * 401 + 32 from by ring]; exact macro_r3_sn 401
  apply stepNat_haltsIn_add (m := 135554) (c₂ := ⟨0, 0, 0, 62757⟩)
  · rw [show (10041 : ℕ) = 4 * 2509 + 5 from by ring, show (62757 : ℕ) = 25 * 2509 + 32 from by ring,
      show (135554 : ℕ) = 54 * 2509 + 68 from by ring]; exact macro_r1_sn 2509
  apply stepNat_haltsIn_add (m := 847220) (c₂ := ⟨0, 0, 0, 392232⟩)
  · rw [show (62757 : ℕ) = 4 * 15688 + 5 from by ring, show (392232 : ℕ) = 25 * 15688 + 32 from by ring,
      show (847220 : ℕ) = 54 * 15688 + 68 from by ring]; exact macro_r1_sn 15688
  apply stepNat_haltsIn_add (m := 5295128) (c₂ := ⟨0, 0, 0, 2451449⟩)
  · rw [show (392232 : ℕ) = 4 * 98057 + 4 from by ring, show (2451449 : ℕ) = 25 * 98057 + 24 from by ring,
      show (5295128 : ℕ) = 54 * 98057 + 50 from by ring]; exact macro_r0_sn 98057
  apply stepNat_haltsIn_add (m := 33094562) (c₂ := ⟨0, 0, 0, 15321557⟩)
  · rw [show (2451449 : ℕ) = 4 * 612861 + 5 from by ring, show (15321557 : ℕ) = 25 * 612861 + 32 from by ring,
      show (33094562 : ℕ) = 54 * 612861 + 68 from by ring]; exact macro_r1_sn 612861
  apply stepNat_haltsIn_add (m := 206841020) (c₂ := ⟨0, 0, 0, 95759732⟩)
  · rw [show (15321557 : ℕ) = 4 * 3830388 + 5 from by ring, show (95759732 : ℕ) = 25 * 3830388 + 32 from by ring,
      show (206841020 : ℕ) = 54 * 3830388 + 68 from by ring]; exact macro_r1_sn 3830388
  apply stepNat_haltsIn_add (m := 1292756378) (c₂ := ⟨0, 0, 0, 598498324⟩)
  · rw [show (95759732 : ℕ) = 4 * 23939932 + 4 from by ring, show (598498324 : ℕ) = 25 * 23939932 + 24 from by ring,
      show (1292756378 : ℕ) = 54 * 23939932 + 50 from by ring]; exact macro_r0_sn 23939932
  apply stepNat_haltsIn_add (m := 8079727370) (c₂ := ⟨0, 0, 0, 3740614524⟩)
  · rw [show (598498324 : ℕ) = 4 * 149624580 + 4 from by ring, show (3740614524 : ℕ) = 25 * 149624580 + 24 from by ring,
      show (8079727370 : ℕ) = 54 * 149624580 + 50 from by ring]; exact macro_r0_sn 149624580
  apply stepNat_haltsIn_add (m := 50498296070) (c₂ := ⟨0, 0, 0, 23378840774⟩)
  · rw [show (3740614524 : ℕ) = 4 * 935153630 + 4 from by ring, show (23378840774 : ℕ) = 25 * 935153630 + 24 from by ring,
      show (50498296070 : ℕ) = 54 * 935153630 + 50 from by ring]; exact macro_r0_sn 935153630
  refine ⟨⟨0, 29223550968, 0, 0⟩, ?_, rfl⟩
  rw [show (23378840774 : ℕ) = 4 * 5844710193 + 2 from by ring,
    show (29223550968 : ℕ) = 5 * 5844710193 + 3 from by ring]
  exact macro_halt_sn 5844710193

end Sz22_halted_692_13
