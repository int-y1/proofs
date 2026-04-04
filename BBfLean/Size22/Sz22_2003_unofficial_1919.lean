import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1919: [9/70, 11/5, 50/21, 7/11, 15/2]

Vector representation:
```
-1  2 -1 -1  0
 0  0 -1  0  1
 1 -1  2 -1  0
 0  0  0  1 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1919

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem opening : ⟨a + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a, 3, 0, d, 0⟩ := by
  step fm; step fm; finish

theorem drain_chain : ∀ k, ⟨a + k, b + 1, 0, d + 3 * k, 0⟩ [fm]⊢*
    ⟨a, b + 1 + 3 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring]
    apply stepStar_trans (ih (a := a + 1) (d := d + 3))
    rw [show b + 1 + 3 * k = (b + 3 * k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show b + 1 + 3 * (k + 1) = b + 3 * k + 3 + 1 from by ring]
    finish

theorem r0_setup : ⟨a + 1, b, 0, 0, 0⟩ [fm]⊢⁺ ⟨a, b + 1, 0, 1, 0⟩ := by
  step fm; step fm; step fm; finish

theorem b_to_ae : ∀ k, ⟨a, k + 1, 0, 1, e⟩ [fm]⊢*
    ⟨a + k + 1, 0, 0, 0, e + k + 2⟩ := by
  intro k; induction' k with k ih generalizing a e
  · step fm; step fm; step fm; finish
  · rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

theorem trans_A_to_B :
    ⟨n + m + 3, 0, 0, 3 * m + 2, 0⟩ [fm]⊢⁺
    ⟨n + 3 * m + 4, 0, 0, 3 * m + 4, 0⟩ := by
  rw [show n + m + 3 = (n + m + 1) + 2 from by ring,
      show 3 * m + 2 = (3 * m + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus opening
  rw [show n + m + 1 = (n + 1) + m from by ring,
      show 3 * m + 1 = 1 + 3 * m from by ring]
  apply stepStar_trans (drain_chain m (a := n + 1) (b := 2) (d := 1))
  rw [show 2 + 1 + 3 * m = (3 * m + 2) + 1 from by ring]
  apply stepStar_trans (b_to_ae (3 * m + 2) (a := n + 1) (e := 0))
  rw [show n + 1 + (3 * m + 2) + 1 = n + 3 * m + 4 from by ring,
      show 0 + (3 * m + 2) + 2 = 3 * m + 4 from by ring]
  apply stepStar_trans (e_to_d (3 * m + 4) (a := n + 3 * m + 4) (d := 0))
  ring_nf; finish

theorem trans_B_to_A :
    ⟨n + m + 4, 0, 0, 3 * m + 4, 0⟩ [fm]⊢⁺
    ⟨n + 3 * m + 7, 0, 0, 3 * m + 8, 0⟩ := by
  rw [show n + m + 4 = (n + m + 2) + 2 from by ring,
      show 3 * m + 4 = (3 * m + 3) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus opening
  rw [show n + m + 2 = (n + 1) + (m + 1) from by ring,
      show 3 * m + 3 = 0 + 3 * (m + 1) from by ring]
  apply stepStar_trans (drain_chain (m + 1) (a := n + 1) (b := 2) (d := 0))
  rw [show 2 + 1 + 3 * (m + 1) = 3 * m + 6 from by ring,
      show n + 1 = (n + 1) from rfl]
  apply stepStar_trans (stepPlus_stepStar (r0_setup (a := n) (b := 3 * m + 6)))
  rw [show 3 * m + 6 + 1 = (3 * m + 6) + 1 from by ring]
  apply stepStar_trans (b_to_ae (3 * m + 6) (a := n) (e := 0))
  rw [show n + (3 * m + 6) + 1 = n + 3 * m + 7 from by ring,
      show 0 + (3 * m + 6) + 2 = 3 * m + 8 from by ring]
  apply stepStar_trans (e_to_d (3 * m + 8) (a := n + 3 * m + 7) (d := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨8, 0, 0, 8, 0⟩) (by execute fm 95)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ (∃ n m, q = ⟨n + m + 3, 0, 0, 3 * m + 2, 0⟩) ∨
                   (∃ n m, q = ⟨n + m + 4, 0, 0, 3 * m + 4, 0⟩))
  · intro c hc
    rcases hc with ⟨n, m, rfl⟩ | ⟨n, m, rfl⟩
    · exact ⟨⟨n + 3 * m + 4, 0, 0, 3 * m + 4, 0⟩,
        Or.inr ⟨n + 2 * m, m, by ring_nf⟩, trans_A_to_B⟩
    · exact ⟨⟨n + 3 * m + 7, 0, 0, 3 * m + 8, 0⟩,
        Or.inl ⟨n + 2 * m + 2, m + 2, by ring_nf⟩, trans_B_to_A⟩
  · exact Or.inl ⟨3, 2, by ring_nf⟩
