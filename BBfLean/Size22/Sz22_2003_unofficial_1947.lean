import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1947: [9/70, 50/21, 11/5, 7/11, 21/2]

Vector representation:
```
-1  2 -1 -1  0
 1 -1  2 -1  0
 0  0 -1  0  1
 0  0  0  1 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1947

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem opening : ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 1, 0, 2, d, 0⟩ := by
  step fm; step fm; finish

theorem drain_three_round : ⟨a + 2, b, 2, d + 3, 0⟩ [fm]⊢* ⟨a + 1, b + 3, 2, d, 0⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem drain_three_loop : ∀ k, ⟨a + k + 1, b, 2, d + 3 * k, 0⟩ [fm]⊢* ⟨a + 1, b + 3 * k, 2, d, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show a + (k + 1) + 1 = (a + 1) + k + 1 from by ring,
        show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring]
    apply stepStar_trans (ih (a := a + 1) (d := d + 3))
    rw [show a + 1 + 1 = a + 2 from by ring,
        show b + 3 * k = b + 3 * k from rfl]
    apply stepStar_trans (drain_three_round (a := a) (b := b + 3 * k) (d := d))
    ring_nf; finish

theorem end_mod2 : ⟨a + 3, b, 2, 2, 0⟩ [fm]⊢* ⟨a + 1, b + 4, 2, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

theorem spiral_loop : ∀ k, ⟨a, b + k, 2, 0, e⟩ [fm]⊢* ⟨a + k, b, 2, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show a + 1 = a + 1 from rfl]
    apply stepStar_trans (ih (a := a + 1) (b := b) (e := e + 1))
    ring_nf; finish

theorem close : ⟨a, 0, 2, 0, e⟩ [fm]⊢* ⟨a, 0, 0, e + 2, 0⟩ := by
  step fm; step fm
  show ⟨a, 0, 0, 0, e + 1 + 1⟩ [fm]⊢* ⟨a, 0, 0, e + 2, 0⟩
  rw [show e + 1 + 1 = 0 + (e + 2) from by ring]
  apply stepStar_trans (e_to_d (e + 2) (a := a) (d := 0) (e := 0))
  ring_nf; finish

theorem trans_mod0 : ⟨m + k + 2, 0, 0, 3 * (k + 1), 0⟩ [fm]⊢⁺ ⟨m + 3 * k + 4, 0, 0, 3 * k + 5, 0⟩ := by
  apply stepPlus_stepStar_stepPlus
    (opening (a := m + k + 1) (d := 3 * (k + 1)))
  show ⟨m + k + 1 + 1, 0, 2, 3 * (k + 1), 0⟩ [fm]⊢* _
  rw [show m + k + 1 + 1 = m + (k + 1) + 1 from by ring,
      show (3 : ℕ) * (k + 1) = 0 + 3 * (k + 1) from by ring]
  apply stepStar_trans
    (drain_three_loop (k + 1) (a := m) (b := 0) (d := 0))
  apply stepStar_trans
    (spiral_loop (3 * (k + 1)) (a := m + 1) (b := 0) (e := 0))
  rw [show m + 1 + 3 * (k + 1) = m + 3 * k + 4 from by ring,
      show 0 + 3 * (k + 1) = 3 * k + 3 from by ring]
  apply stepStar_trans
    (close (a := m + 3 * k + 4) (e := 3 * k + 3))
  ring_nf; finish

theorem trans_mod2 : ⟨m + k + 3, 0, 0, 3 * k + 2, 0⟩ [fm]⊢⁺ ⟨m + 3 * k + 5, 0, 0, 3 * k + 6, 0⟩ := by
  apply stepPlus_stepStar_stepPlus
    (opening (a := m + k + 2) (d := 3 * k + 2))
  show ⟨m + k + 2 + 1, 0, 2, 3 * k + 2, 0⟩ [fm]⊢* _
  rw [show m + k + 2 + 1 = m + 2 + k + 1 from by ring,
      show (3 : ℕ) * k + 2 = 2 + 3 * k from by ring]
  apply stepStar_trans
    (drain_three_loop k (a := m + 2) (b := 0) (d := 2))
  rw [show m + 2 + 1 = m + 3 from by ring,
      show 0 + 3 * k = 3 * k from by ring]
  apply stepStar_trans
    (end_mod2 (a := m) (b := 3 * k))
  rw [show (3 : ℕ) * k + 4 = 0 + (3 * k + 4) from by ring]
  apply stepStar_trans
    (spiral_loop (3 * k + 4) (a := m + 1) (b := 0) (e := 0))
  rw [show m + 1 + (3 * k + 4) = m + 3 * k + 5 from by ring,
      show 0 + (3 * k + 4) = 3 * k + 4 from by ring]
  apply stepStar_trans
    (close (a := m + 3 * k + 5) (e := 3 * k + 4))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨9, 0, 0, 8, 0⟩)
  · execute fm 96
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m k, q = ⟨m + k + 3, 0, 0, 3 * k + 2, 0⟩ ∨
                          q = ⟨m + k + 2, 0, 0, 3 * (k + 1), 0⟩)
  · intro c ⟨m, k, hq⟩
    rcases hq with rfl | rfl
    · exact ⟨_, ⟨m + 2 * k + 2, k + 1, Or.inr (by ring_nf)⟩, trans_mod2⟩
    · exact ⟨_, ⟨m + 2 * k, k + 1, Or.inl (by ring_nf)⟩, trans_mod0⟩
  · exact ⟨4, 2, Or.inl rfl⟩
