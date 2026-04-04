import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1845: [9/35, 1/33, 50/3, 11/25, 21/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  0  0 -1
 1 -1  2  0  0
 0  0 -2  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1845

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a b c, ⟨a, b + k, c, 0, 0⟩ [fm]⊢* ⟨a + k, b, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b (c + 2))
    ring_nf; finish

theorem r4_drain : ∀ k, ∀ a e, ⟨a, 0, 2 * k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

theorem r4_drain_odd : ∀ k, ∀ a e, ⟨a, 0, 2 * k + 1, 0, e⟩ [fm]⊢* ⟨a, 0, 1, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

theorem e_drain : ∀ k, ∀ a d, ⟨a + k, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

theorem r1r1r3_chain : ∀ k, ∀ a b D, ⟨a, b, 2, D + 2 * k, 0⟩ [fm]⊢* ⟨a + k, b + 3 * k, 2, D, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b D
  · exists 0
  · rw [show D + 2 * (k + 1) = (D + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 3) D)
    ring_nf; finish

theorem opening : ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 1, 0, 2, d + 1, 0⟩ := by
  step fm; step fm; finish

theorem main_trans_odd : ⟨a + 1, 0, 0, 2 * k + 1, 0⟩ [fm]⊢⁺ ⟨a + k + 1, 0, 0, 3 * k + 4, 0⟩ := by
  apply stepPlus_stepStar_stepPlus opening
  rw [show 2 * k + 1 + 1 = 0 + 2 * (k + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (k + 1) (a + 1) 0 0)
  show ⟨a + 1 + (k + 1), 0 + 3 * (k + 1), 2, 0, 0⟩ [fm]⊢* _
  apply stepStar_trans (r3_chain (3 * (k + 1)) (a + 1 + (k + 1)) 0 2)
  show ⟨a + 1 + (k + 1) + 3 * (k + 1), 0, 2 + 2 * (3 * (k + 1)), 0, 0⟩ [fm]⊢* _
  rw [show a + 1 + (k + 1) + 3 * (k + 1) = a + 4 * k + 5 from by ring,
      show 2 + 2 * (3 * (k + 1)) = 2 * (3 * k + 4) from by ring]
  apply stepStar_trans (r4_drain (3 * k + 4) (a + 4 * k + 5) 0)
  rw [show a + 4 * k + 5 = (a + k + 1) + (3 * k + 4) from by ring,
      show 0 + (3 * k + 4) = 3 * k + 4 from by ring]
  apply stepStar_trans (e_drain (3 * k + 4) (a + k + 1) 0)
  ring_nf; finish

theorem odd_fixup : ⟨a + 1, 0, 1, 0, e + 3⟩ [fm]⊢* ⟨a, 0, 0, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem main_trans_even : ⟨a + 1, 0, 0, 2 * (k + 1), 0⟩ [fm]⊢⁺ ⟨a + k + 4, 0, 0, 3 * k + 2, 0⟩ := by
  apply stepPlus_stepStar_stepPlus opening
  rw [show 2 * (k + 1) + 1 = 1 + 2 * (k + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (k + 1) (a + 1) 0 1)
  show ⟨a + 1 + (k + 1), 0 + 3 * (k + 1), 2, 1, 0⟩ [fm]⊢* _
  step fm; step fm
  show ⟨a + 1 + (k + 1) + 1, 0 + 3 * (k + 1) + 2 - 1, 3, 0, 0⟩ [fm]⊢* _
  rw [show 0 + 3 * (k + 1) + 2 - 1 = 0 + (3 * k + 4) from by omega]
  apply stepStar_trans (r3_chain (3 * k + 4) (a + 1 + (k + 1) + 1) 0 3)
  rw [show a + 1 + (k + 1) + 1 + (3 * k + 4) = a + 4 * k + 7 from by ring,
      show 3 + 2 * (3 * k + 4) = 2 * (3 * k + 5) + 1 from by ring]
  apply stepStar_trans (r4_drain_odd (3 * k + 5) (a + 4 * k + 7) 0)
  rw [show 0 + (3 * k + 5) = 3 * k + 5 from by ring,
      show a + 4 * k + 7 = (a + 4 * k + 6) + 1 from by ring,
      show 3 * k + 5 = (3 * k + 2) + 3 from by ring]
  apply stepStar_trans (odd_fixup (a := a + 4 * k + 6) (e := 3 * k + 2))
  rw [show a + 4 * k + 6 = (a + k + 4) + (3 * k + 2) from by ring]
  apply stepStar_trans (e_drain (3 * k + 2) (a + k + 4) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 15)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a + 1, 0, 0, d + 1, 0⟩)
  · intro c ⟨a, d, hq⟩; subst hq
    rcases Nat.even_or_odd (d + 1) with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      refine ⟨⟨a + k + 4, 0, 0, 3 * k + 2, 0⟩, ⟨a + k + 3, 3 * k + 1, by ring_nf⟩, ?_⟩
      rw [show d + 1 = 2 * (k + 1) from by omega]
      exact main_trans_even
    · refine ⟨⟨a + K + 1, 0, 0, 3 * K + 4, 0⟩, ⟨a + K, 3 * K + 3, by ring_nf⟩, ?_⟩
      rw [show d + 1 = 2 * K + 1 from by omega]
      exact main_trans_odd
  · exact ⟨1, 0, by ring_nf⟩
