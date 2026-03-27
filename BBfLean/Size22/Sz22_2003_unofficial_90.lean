import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #90: [1/30, 196/3, 6/77, 5/7, 33/2]

Vector representation:
```
-1 -1 -1  0  0
 2 -1  0  2  0
 1  1  0 -1 -1
 0  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_90

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: transfer d to c
theorem d_to_c : ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  have h : ∀ k c, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
    intro k; induction' k with k ih <;> intro c
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih _); ring_nf; finish
  exact h k c

-- R5+R1 chain: drain a and c into e
theorem ac_drain : ⟨a + 2 * k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  have h : ∀ k a e, ⟨a + 2 * k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
    intro k; induction' k with k ih <;> intro a e
    · exists 0
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish
  exact h k a e

-- R5+R2 pivot: one step of R5 then R2
theorem pivot : ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 2, e + 1⟩ := by
  step fm; step fm; finish

-- R3+R2 chain: build a and d while consuming e
theorem r3r2_chain : ⟨a, 0, 0, d + 1, e + k⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, d + 1 + k, e⟩ := by
  have h : ∀ k a d, ⟨a, 0, 0, d + 1, e + k⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, d + 1 + k, e⟩ := by
    intro k; induction' k with k ih <;> intro a d
    · exists 0
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish
  exact h k a d

-- Main transition: (a + 2d + 1, 0, 0, d, 0) ->⁺ (a + 3d + 5, 0, 0, d + 3, 0)
theorem main_trans : ⟨a + 2 * d + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 3 * d + 5, 0, 0, d + 3, 0⟩ := by
  -- Phase 1: d_to_c
  rw [show d = (0 : ℕ) + d from by ring]
  apply stepStar_stepPlus_stepPlus d_to_c
  simp only [Nat.zero_add]
  -- Phase 2: ac_drain
  rw [show a + 2 * d + 1 = (a + 1) + 2 * d from by ring]
  apply stepStar_stepPlus_stepPlus ac_drain
  simp only [Nat.zero_add]
  -- Phase 3: pivot
  apply stepPlus_stepStar_stepPlus pivot
  -- Phase 4: r3r2_chain
  rw [show d + 1 = (0 : ℕ) + (d + 1) from by ring]
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (k := d + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨8, 0, 0, 3, 0⟩)
  · execute fm 19
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ a ≥ 2 * d + 1 ∧ d ≥ 3)
  · intro c ⟨a, d, hq, ha, hd⟩; subst hq
    obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 * d + 1 := ⟨a - (2 * d + 1), by omega⟩
    refine ⟨⟨m + 3 * d + 5, 0, 0, d + 3, 0⟩, ⟨m + 3 * d + 5, d + 3, rfl, ?_, ?_⟩, main_trans⟩
    · omega
    · omega
  · exact ⟨8, 3, rfl, by omega, by omega⟩
