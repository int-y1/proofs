import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1885: [9/35, 5/33, 98/3, 11/49, 15/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  2  0
 0  0  0 -2  1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1885

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ⟨a, 0, 0, 2 * k, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 1))
    ring_nf; finish

theorem r4_chain_odd : ∀ k, ⟨a, 0, 0, 2 * k + 1, e⟩ [fm]⊢* ⟨a, 0, 0, 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 1))
    ring_nf; finish

theorem r5r2_drain : ∀ k, ⟨a + k, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c := c + 2))
    ring_nf; finish

theorem r2_drain : ∀ j, ⟨a, b + j, c, 0, e + j⟩ [fm]⊢* ⟨a, b, c + j, 0, e⟩ := by
  intro j; induction' j with j ih generalizing a b c e
  · exists 0
  · rw [show b + (j + 1) = (b + j) + 1 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem r3_chain : ∀ j, ⟨a, j, 0, d, 0⟩ [fm]⊢* ⟨a + j, 0, 0, d + 2 * j, 0⟩ := by
  intro j; induction' j with j ih generalizing a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1) (d := d + 2))
    ring_nf; finish

theorem r1r1r3_chain : ∀ j, ⟨A, B, c + 2 * j, 2, 0⟩ [fm]⊢* ⟨A + j, B + 3 * j, c, 2, 0⟩ := by
  intro j; induction' j with j ih generalizing A B c
  · exists 0
  · rw [show c + 2 * (j + 1) = (c + 2) + 2 * j from by ring]
    apply stepStar_trans (ih (c := c + 2) (A := A) (B := B))
    step fm; step fm; step fm
    ring_nf; finish

theorem odd_tail : ⟨A, B, 1, 2, 0⟩ [fm]⊢⁺ ⟨A + 1, B + 1, 0, 3, 0⟩ := by
  step fm; step fm; finish

theorem even_tail : ⟨A, B, 2, 2, 0⟩ [fm]⊢⁺ ⟨A + 1, B + 3, 0, 2, 0⟩ := by
  step fm; step fm; step fm; finish

theorem spiral_odd : ∀ m, ⟨A, 0, 2 * m + 1, 2, 0⟩ [fm]⊢* ⟨A + 4 * m + 2, 0, 0, 6 * m + 5, 0⟩ := by
  intro m
  rw [show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (r1r1r3_chain m (c := 1) (A := A) (B := 0))
  show ⟨A + m, 0 + 3 * m, 1, 2, 0⟩ [fm]⊢* _
  rw [show 0 + 3 * m = 3 * m from by ring]
  apply stepStar_trans (stepPlus_stepStar (odd_tail (A := A + m) (B := 3 * m)))
  apply stepStar_trans (r3_chain (3 * m + 1) (a := A + m + 1) (d := 3))
  ring_nf; finish

theorem spiral_even : ∀ m, ⟨A, 0, 2 * (m + 1), 2, 0⟩ [fm]⊢* ⟨A + 4 * (m + 1), 0, 0, 6 * (m + 1) + 2, 0⟩ := by
  intro m
  rw [show 2 * (m + 1) = 2 + 2 * m from by ring]
  apply stepStar_trans (r1r1r3_chain m (c := 2) (A := A) (B := 0))
  show ⟨A + m, 0 + 3 * m, 2, 2, 0⟩ [fm]⊢* _
  rw [show 0 + 3 * m = 3 * m from by ring]
  apply stepStar_trans (stepPlus_stepStar (even_tail (A := A + m) (B := 3 * m)))
  apply stepStar_trans (r3_chain (3 * m + 3) (a := A + m + 1) (d := 2))
  ring_nf; finish

theorem r5_r3 : ⟨a + 1, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨a + 1, 0, c + 1, 2, 0⟩ := by
  step fm; step fm; finish

theorem trans_even : ∀ k, ⟨a + k + 1, 0, 0, 2 * k, 0⟩ [fm]⊢⁺ ⟨a + 4 * k + 3, 0, 0, 6 * k + 5, 0⟩ := by
  intro k
  apply stepStar_stepPlus_stepPlus
  · exact r4_chain k (a := a + k + 1) (e := 0)
  show ⟨a + k + 1, 0, 0, 0, 0 + k⟩ [fm]⊢⁺ _
  rw [show (0 : ℕ) + k = k from by ring]
  apply stepStar_stepPlus_stepPlus
  · rw [show a + k + 1 = (a + 1) + k from by ring]
    exact r5r2_drain k (a := a + 1) (c := 0)
  show ⟨a + 1, 0, 0 + 2 * k, 0, 0⟩ [fm]⊢⁺ _
  rw [show (0 : ℕ) + 2 * k = 2 * k from by ring]
  apply stepPlus_stepStar_stepPlus
  · exact r5_r3 (a := a) (c := 2 * k)
  apply stepStar_trans (spiral_odd k (A := a + 1))
  ring_nf; finish

theorem trans_odd_k2 : ⟨a + 3, 0, 0, 5, 0⟩ [fm]⊢⁺ ⟨a + 7, 0, 0, 8, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm
  show ⟨a + 3, 0, 2 * (0 + 1), 2, 0⟩ [fm]⊢* ⟨a + 7, 0, 0, 8, 0⟩
  apply stepStar_trans (spiral_even 0 (A := a + 3))
  ring_nf; finish

theorem trans_odd_ge3 : ∀ k, ⟨a + k + 4, 0, 0, 2 * k + 7, 0⟩ [fm]⊢⁺ ⟨a + 4 * k + 11, 0, 0, 6 * k + 14, 0⟩ := by
  intro k
  rw [show 2 * k + 7 = 2 * (k + 3) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact r4_chain_odd (k + 3) (a := a + k + 4) (e := 0)
  show ⟨a + k + 4, 0, 0, 1, 0 + (k + 3)⟩ [fm]⊢⁺ _
  rw [show (0 : ℕ) + (k + 3) = k + 3 from by ring]
  -- R5+R1: 2 steps to (a+k+3, 3, 0, 0, k+3)
  step fm; step fm
  rw [show k + 2 + 1 = k + 3 from by ring]
  -- R2x3: (a+k+3, 0, 3, 0, k)
  apply stepStar_trans
  · rw [show (3 : ℕ) = 0 + 3 from by ring, show k + 3 = k + 3 from rfl]
    exact r2_drain 3 (a := a + k + 3) (b := 0) (c := 0) (e := k)
  show ⟨a + k + 3, 0, 0 + 3, 0, k⟩ [fm]⊢* _
  rw [show (0 : ℕ) + 3 = 3 from by ring]
  -- R5+R2 drain k rounds: (a+3, 0, 2k+3, 0, 0)
  apply stepStar_trans
  · rw [show a + k + 3 = (a + 3) + k from by ring]
    exact r5r2_drain k (a := a + 3) (c := 3)
  show ⟨a + 3, 0, 3 + 2 * k, 0, 0⟩ [fm]⊢* _
  rw [show 3 + 2 * k = 2 * k + 3 from by ring]
  -- R5+R3: (a+3, 0, 2k+4, 2, 0)
  apply stepStar_trans (stepPlus_stepStar (r5_r3 (a := a + 2) (c := 2 * k + 3)))
  -- C = 2k+4 = 2*((k+1)+1)
  rw [show 2 * k + 3 + 1 = 2 * ((k + 1) + 1) from by ring]
  apply stepStar_trans (spiral_even (k + 1) (A := a + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 5, 0⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 5 ∧ 2 * a ≥ d + 1)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d even: d = K + K = 2K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨F, rfl⟩ : ∃ F, a = F + K + 1 := ⟨a - K - 1, by omega⟩
      refine ⟨⟨F + 4 * K + 3, 0, 0, 6 * K + 5, 0⟩,
        ⟨F + 4 * K + 3, 6 * K + 5, rfl, by omega, by omega⟩, ?_⟩
      exact trans_even K
    · -- d odd: d = 2K + 1
      subst hK
      rcases (show K = 2 ∨ K ≥ 3 from by omega) with rfl | hK3
      · -- K = 2, d = 5
        obtain ⟨F, rfl⟩ : ∃ F, a = F + 3 := ⟨a - 3, by omega⟩
        refine ⟨⟨F + 7, 0, 0, 8, 0⟩,
          ⟨F + 7, 8, rfl, by omega, by omega⟩, ?_⟩
        exact trans_odd_k2
      · -- K >= 3: K = k+3, d = 2(k+3)+1 = 2k+7
        obtain ⟨k, rfl⟩ : ∃ k, K = k + 3 := ⟨K - 3, by omega⟩
        obtain ⟨F, rfl⟩ : ∃ F, a = F + k + 4 := ⟨a - k - 4, by omega⟩
        refine ⟨⟨F + 4 * k + 11, 0, 0, 6 * k + 14, 0⟩,
          ⟨F + 4 * k + 11, 6 * k + 14, rfl, by omega, by omega⟩, ?_⟩
        rw [show 2 * (k + 3) + 1 = 2 * k + 7 from by ring]
        exact trans_odd_ge3 k
  · exact ⟨3, 5, rfl, by omega, by omega⟩
