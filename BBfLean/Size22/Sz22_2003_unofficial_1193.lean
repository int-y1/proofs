import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1193: [5/6, 49/2, 484/35, 3/11, 55/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  2
 0  1  0  0 -1
 0  0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1193

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 repeated: move e to b
theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · rw [Nat.add_succ e k]; step fm
    apply stepStar_trans (ih (b := b + 1)); ring_nf; finish

-- Spiral: R1, R1, R3 repeated j times
theorem spiral : ∀ j, ∀ b c d e, ⟨2, b + 2 * j, c, d + j, e⟩ [fm]⊢* ⟨2, b, c + j, d, e + 2 * j⟩ := by
  intro j; induction' j with j ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (j + 1) = (b + 2 * j) + 1 + 1 from by ring,
        show d + (j + 1) = (d + j) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) d (e + 2))
    ring_nf; finish

-- Drain: R3, R2, R2 repeated k times
theorem drain : ∀ k, ∀ d e, ⟨0, 0, k, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + 1 + 3 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm; step fm; step fm
    apply stepStar_trans (ih (d + 3) (e + 2))
    ring_nf; finish

-- Odd transition: (0,0,0,d+h+2, 2h+1) ⊢⁺ (0,0,0,d+3h+5, 4h+5)
theorem main_odd : ∀ d h, ⟨0, 0, 0, d + h + 2, 2 * h + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 3 * h + 5, 4 * h + 5⟩ := by
  intro d h
  apply stepStar_stepPlus_stepPlus
  · rw [show (2 * h + 1 : ℕ) = 0 + (2 * h + 1) from by ring]
    exact e_to_b (2 * h + 1) (b := 0) (d := d + h + 2) (e := 0)
  rw [show (0 + (2 * h + 1) : ℕ) = 2 * h + 1 from by ring]
  apply step_stepStar_stepPlus
  · show ⟨0, 2 * h + 1, 0, d + h + 2, 0⟩ [fm]⊢ ⟨0, 2 * h + 1, 1, d + h + 1, 1⟩
    rw [show d + h + 2 = (d + h + 1) + 1 from by ring]; unfold fm; rfl
  apply stepStar_trans
  · show ⟨0, 2 * h + 1, 1, d + h + 1, 1⟩ [fm]⊢* ⟨2, 2 * h + 1, 0, d + h, 3⟩
    rw [show d + h + 1 = (d + h) + 1 from by ring]; step fm; finish
  apply stepStar_trans
  · rw [show (2 * h + 1 : ℕ) = 1 + 2 * h from by ring]
    exact spiral h 1 0 d 3
  rw [show 0 + h = h from by ring, show 3 + 2 * h = 2 * h + 3 from by ring]
  step fm; step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]
  apply stepStar_trans (drain (h + 1) (d + 1) (2 * h + 3))
  ring_nf; finish

-- Even transition: (0,0,0,d+h+2, 2h) ⊢⁺ (0,0,0,d+3h+4, 4h+3)
theorem main_even : ∀ d h, ⟨0, 0, 0, d + h + 2, 2 * h⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 3 * h + 4, 4 * h + 3⟩ := by
  intro d h
  apply stepStar_stepPlus_stepPlus
  · rw [show (2 * h : ℕ) = 0 + 2 * h from by ring]
    exact e_to_b (2 * h) (b := 0) (d := d + h + 2) (e := 0)
  rw [show (0 + 2 * h : ℕ) = 2 * h from by ring]
  apply step_stepStar_stepPlus
  · show ⟨0, 2 * h, 0, d + h + 2, 0⟩ [fm]⊢ ⟨0, 2 * h, 1, d + h + 1, 1⟩
    rw [show d + h + 2 = (d + h + 1) + 1 from by ring]; unfold fm; rfl
  apply stepStar_trans
  · show ⟨0, 2 * h, 1, d + h + 1, 1⟩ [fm]⊢* ⟨2, 2 * h, 0, d + h, 3⟩
    rw [show d + h + 1 = (d + h) + 1 from by ring]; step fm; finish
  apply stepStar_trans
  · rw [show (2 * h : ℕ) = 0 + 2 * h from by ring]
    exact spiral h 0 0 d 3
  rw [show 0 + h = h from by ring, show 3 + 2 * h = 2 * h + 3 from by ring]
  step fm; step fm
  rw [show d + 4 = (d + 3) + 1 from by ring]
  apply stepStar_trans (drain h (d + 3) (2 * h + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D + 2, E⟩ ∧ 2 * D ≥ E)
  · intro c ⟨D, E, hq, hDE⟩; subst hq
    rcases Nat.even_or_odd E with ⟨h, he⟩ | ⟨h, he⟩
    · -- E = 2h
      rw [show h + h = 2 * h from by ring] at he; subst he
      obtain ⟨d, rfl⟩ : ∃ d, D = d + h := ⟨D - h, by omega⟩
      refine ⟨⟨0, 0, 0, d + 3 * h + 4, 4 * h + 3⟩,
        ⟨d + 3 * h + 2, 4 * h + 3, by simp [Q], by omega⟩, ?_⟩
      exact main_even d h
    · -- E = 2h + 1
      subst he
      obtain ⟨d, rfl⟩ : ∃ d, D = d + h := ⟨D - h, by omega⟩
      refine ⟨⟨0, 0, 0, d + 3 * h + 5, 4 * h + 5⟩,
        ⟨d + 3 * h + 3, 4 * h + 5, by simp [Q], by omega⟩, ?_⟩
      exact main_odd d h
  · exact ⟨0, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1193
