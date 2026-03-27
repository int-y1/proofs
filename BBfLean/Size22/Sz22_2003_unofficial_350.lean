import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #350: [2/15, 1/3, 1617/2, 25/7, 1/55, 3/5]

Vector representation:
```
 1 -1 -1  0  0
 0 -1  0  0  0
-1  1  0  2  1
 0  0  2 -1  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_350

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

private theorem cast_step {a b : Q} (h : a = b) (hs : a [fm]⊢* c) : b [fm]⊢* c := h ▸ hs
private theorem cast_plus {a b : Q} (h : b = a) (hs : a [fm]⊢⁺ c) : b [fm]⊢⁺ c := h ▸ hs
private theorem cast_plus' {a b : Q} (h : b = a) (hs : c [fm]⊢⁺ a) : c [fm]⊢⁺ b := h ▸ hs

theorem r1r3_chain : ⟨0, 1, c+k, d, e⟩ [fm]⊢* ⟨0, 1, c, d+2*k, e+k⟩ := by
  have many_step : ∀ k c d e, ⟨0, 1, c+k, d, e⟩ [fm]⊢* ⟨0, 1, c, d+2*k, e+k⟩ := by
    intro k; induction' k with k ih <;> intro c d e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih c _ _)
    ring_nf; finish
  exact many_step k c d e

theorem r4_chain : ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c+2*k, d, e⟩ := by
  have many_step : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c+2*k, d, e⟩ := by
    intro k; induction' k with k ih <;> intro c d e
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish
  exact many_step k c d e

theorem r5_chain : ⟨0, 0, c+k, 0, e+k⟩ [fm]⊢* ⟨0, 0, c, 0, e⟩ := by
  have many_step : ∀ k c e, ⟨0, 0, c+k, 0, e+k⟩ [fm]⊢* ⟨0, 0, c, 0, e⟩ := by
    intro k; induction' k with k ih <;> intro c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    exact ih c e
  exact many_step k c e

theorem r6_r1 (c : ℕ) : ⟨0, 0, c+2, 0, 0⟩ [fm]⊢⁺ ⟨1, 0, c, 0, 0⟩ := by
  step fm; step fm; finish

theorem main_cycle (c : ℕ) : ⟨1, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨1, 0, 3*c+1, 0, 0⟩ := by
  -- Rule3: (1, 0, c, 0, 0) → (0, 1, c, 2, 1)
  step fm
  -- r1r3_chain: (0, 1, c, 2, 1) →* (0, 1, 0, 2+2c, 1+c)
  apply stepStar_trans (cast_step (by ring_nf) (r1r3_chain (c := 0) (k := c) (d := 2) (e := 1)))
  -- Rule2: (0, 1, 0, 2+2c, 1+c) → (0, 0, 0, 2+2c, 1+c)
  step fm
  -- r4_chain: (0, 0, 0, 2+2c, 1+c) →* (0, 0, 4+4c, 0, 1+c)
  apply stepStar_trans (cast_step (by ring_nf) (r4_chain (c := 0) (k := 2 + 2 * c) (d := 0) (e := 1 + c)))
  -- r5_chain: (0, 0, 4+4c, 0, 1+c) →* (0, 0, 3+3c, 0, 0)
  apply stepStar_trans (cast_step (by ring_nf) (r5_chain (c := 3 + 3 * c) (k := 1 + c) (e := 0)))
  -- r6_r1: (0, 0, 3+3c, 0, 0) →⁺ (1, 0, 1+3c, 0, 0)
  apply stepPlus_stepStar
  exact cast_plus' (by ring_nf) (cast_plus (by ring_nf) (r6_r1 (1 + 3 * c)))

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (C := fun n ↦ ⟨1, 0, n, 0, 0⟩) (i₀ := 0)
  intro n
  exact ⟨3 * n + 1, main_cycle n⟩

end Sz22_2003_unofficial_350
