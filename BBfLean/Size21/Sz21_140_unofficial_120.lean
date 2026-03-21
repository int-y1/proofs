import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #120: [77/15, 9/14, 4/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 2 -1  0  0  0
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_120

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: e → c
theorem e_to_c : ⟨a, 0, c, 0, e+k⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
  have many_step : ∀ k c, ⟨a, 0, c, 0, e+k⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
    intro k; induction' k with k h <;> intro c
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k c

-- R2 repeated: d → b
theorem r2_chain : ⟨a+k, b, 0, d+k, e⟩ [fm]⊢* ⟨a, b+2*k, 0, d, e⟩ := by
  have many_step : ∀ k a b, ⟨a+k, b, 0, d+k, e⟩ [fm]⊢* ⟨a, b+2*k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro a b
    · exists 0
    rw [← Nat.add_assoc, show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a b

-- R3 repeated: b → a
theorem r3_chain : ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+2*k, b, 0, 0, e⟩ := by
  have many_step : ∀ k a, ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+2*k, b, 0, 0, e⟩ := by
    intro k; induction' k with k h <;> intro a
    · exists 0
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k a

-- Generalized processing lemma
theorem processing_gen : ∀ C, ∀ a B D E,
    B + D ≥ 1 ∨ C = 0 →
    ⟨a+C+D, B, C, D, E⟩ [fm]⊢* ⟨a + 2*C + 4*D + 2*B, 0, 0, 0, C + E⟩ := by
  intro C; induction' C with C ih <;> intro a B D E _
  · simp only [Nat.zero_add]
    have h1 : ⟨a+D, B, 0, 0+D, E⟩ [fm]⊢* ⟨a, B+2*D, 0, 0, E⟩ := r2_chain
    rw [Nat.zero_add] at h1
    apply stepStar_trans h1
    have h2 : ⟨a, 0+(B+2*D), 0, 0, E⟩ [fm]⊢* ⟨a+2*(B+2*D), 0, 0, 0, E⟩ := r3_chain
    rw [Nat.zero_add] at h2
    apply stepStar_trans h2
    ring_nf; finish
  · rcases (show B ≥ 1 ∨ (B = 0 ∧ D ≥ 1) from by omega) with hB | ⟨rfl, hD⟩
    · -- Sub-case B >= 1: R1 step
      obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
      rw [show a + (C + 1) + D = a + C + D + 1 from by ring]
      step fm
      apply stepStar_trans (ih a B' (D+1) (E+1) (by omega))
      ring_nf; finish
    · -- Sub-case B = 0, D >= 1: R2 step then R1 step
      obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
      rw [show a + (C + 1) + (D' + 1) = (a + C + D') + 1 + 1 from by ring]
      step fm
      step fm
      apply stepStar_trans (ih a 1 (D'+1) (E+1) (by omega))
      ring_nf; finish

-- Main phase 2 transition
theorem main_trans : ⟨a+c+1, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨a+2*c+2, 0, 0, 0, c+1⟩ := by
  rw [show a + c + 1 = (a + c) + 1 from by ring]
  step fm
  have h := processing_gen c a 1 0 1 (by omega)
  rw [show a + c + 0 = a + c from by ring] at h
  apply stepStar_trans h
  ring_nf; finish

-- Full transition combining e_to_c and main_trans
theorem full_trans : ⟨a+e+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a+2*e+2, 0, 0, 0, e+1⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := @e_to_c (a+e+1) 0 0 e
    rw [Nat.zero_add] at h
    exact h
  · exact main_trans

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (C := fun p ↦ ⟨p.1 + p.2 + 1, 0, 0, 0, p.2⟩) ⟨0, 0⟩
  intro ⟨a, e⟩
  refine ⟨⟨a+e, e+1⟩, ?_⟩
  show ⟨a+e+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a+e+(e+1)+1, 0, 0, 0, e+1⟩
  have h := @full_trans a e
  convert h using 2; ring_nf
