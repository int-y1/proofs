import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #867: [4/105, 45/2, 11/5, 91/33, 5/13]

Vector representation:
```
 2 -1 -1 -1  0  0
-1  2  1  0  0  0
 0  0 -1  0  1  0
 0 -1  0  1 -1  1
 0  0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_867

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+2, c+1, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R1R2 chain: each pair consumes 1 from d, adds 1 to a and b.
theorem r1r2_chain : ∀ k, ∀ a b, ⟨a, b + 1, 1, d + k, 0, f⟩ [fm]⊢* ⟨a + k, b + 1 + k, 1, d, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [show d + (k + 1) = d + k + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 1))
    ring_nf; finish

-- R2 chain: drain a, adding 2 to b and 1 to c per step.
theorem r2_chain : ∀ k, ∀ b c, ⟨a + k, b, c, 0, 0, f⟩ [fm]⊢* ⟨a, b + 2 * k, c + k, 0, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) (c + 1))
    ring_nf; finish

-- R3 chain: drain c to e.
theorem r3_chain : ∀ k, ∀ c e, ⟨0, b, c + k, 0, e, f⟩ [fm]⊢* ⟨0, b, c, 0, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (e + 1))
    ring_nf; finish

-- R4 chain: drain b and e, adding to d and f.
theorem r4_chain : ∀ k, ∀ b d f, ⟨0, b + k, 0, d, e + k, f⟩ [fm]⊢* ⟨0, b, 0, d + k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b d f
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (d + 1) (f + 1))
    ring_nf; finish

-- Phases 2+3 combined for cleaner composition.
theorem phase23 (B D F : ℕ) :
    ⟨0, B + 1, 1, D + 1, 0, F⟩ [fm]⊢* ⟨(0 : ℕ), B + 3 * D + 4, D + 2, 0, 0, F⟩ := by
  rw [show D + 1 = 0 + (D + 1) from by ring]
  apply stepStar_trans (r1r2_chain (D + 1) 0 B)
  apply stepStar_trans (r2_chain (f := F) (a := 0) (D + 1) (B + 1 + (D + 1)) 1)
  ring_nf; finish

-- Phases 4+5 combined.
theorem phase45 (B D F : ℕ) :
    ⟨0, B + 3 * D + 4, D + 2, 0, 0, F⟩ [fm]⊢* ⟨(0 : ℕ), B + 2 * D + 2, 0, D + 2, 0, F + D + 2⟩ := by
  rw [show D + 2 = 0 + (D + 2) from by ring,
      show B + 3 * D + 4 = B + 3 * D + 4 from by ring]
  apply stepStar_trans (r3_chain (b := B + 3 * D + 4) (f := F) (D + 2) 0 0)
  rw [show B + 3 * D + 4 = (B + 2 * D + 2) + (D + 2) from by ring]
  apply stepStar_trans (r4_chain (e := 0) (D + 2) (B + 2 * D + 2) 0 F)
  ring_nf; finish

-- Main transition.
theorem main_trans (B D F : ℕ) :
    ⟨0, B + 1, 0, D + 1, 0, F + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), B + 2 * D + 2, 0, D + 2, 0, F + D + 2⟩ := by
  step fm
  apply stepStar_trans (phase23 B D F)
  exact phase45 B D F

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 1, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨B, D, F⟩ ↦ ⟨0, B + 1, 0, D + 1, 0, F + 1⟩) ⟨0, 0, 0⟩
  intro ⟨B, D, F⟩
  exact ⟨⟨B + 2 * D + 1, D + 1, F + D + 1⟩, main_trans B D F⟩

end Sz22_2003_unofficial_867
