import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1633: [77/15, 26/3, 9/91, 5/11, 363/2]

Vector representation:
```
 0 -1 -1  1  1  0
 1 -1  0  0  0  1
 0  2  0 -1  0 -1
 0  0  1  0 -1  0
-1  1  0  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1633

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+2, f⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ a c f,
    ⟨a, 0, c, 0, k, f⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a c f
  · exists 0
  rw [show (k + 1) = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih a (c + 1) f)
  ring_nf; finish

theorem r1r1r3_chain : ∀ k, ∀ α c d e f,
    ⟨α, 2, c + 2 * k, d, e, f + k⟩ [fm]⊢*
    ⟨α, 2, c, d + k, e + 2 * k, f⟩ := by
  intro k; induction' k with k ih <;> intro α c d e f
  · simp; exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
      show f + (k + 1) = (f + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih α c (d + 1) (e + 2) f)
  ring_nf; finish

theorem drain_chain : ∀ k, ∀ a d e f,
    ⟨a, 0, 0, d + k, e, f + 1⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e, f + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · simp; exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show a + 1 + 1 = a + 2 from by ring,
      show f + 1 + 1 = (f + 1) + 1 from by ring]
  apply stepStar_trans (ih (a + 2) d e (f + 1))
  ring_nf; finish

theorem main_trans (A F : ℕ) :
    ⟨A + 1, 0, 0, 0, 2 * (F + 1), F + 1⟩ [fm]⊢⁺
    ⟨A + 2 * F + 3, 0, 0, 0, 2 * (F + 2), F + 2⟩ := by
  -- Phase 1: R4 drain e to c
  have p1 : ⟨A + 1, 0, 0, 0, 2 * (F + 1), F + 1⟩ [fm]⊢*
      ⟨A + 1, 0, 2 * (F + 1), 0, 0, F + 1⟩ := by
    have := e_to_c (2 * (F + 1)) (A + 1) 0 (F + 1)
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R5, R1, R3
  have p2 : ⟨A + 1, 0, 2 * (F + 1), 0, 0, F + 1⟩ [fm]⊢⁺
      ⟨A, 2, 2 * F + 1, 0, 3, F⟩ := by
    rw [show 2 * (F + 1) = (2 * F + 1) + 1 from by ring,
        show F + 1 = F + 1 from rfl]
    step fm; step fm; step fm; ring_nf; finish
  -- Phase 3: R1R1R3 chain
  have p3 : ⟨A, 2, 2 * F + 1, 0, 3, F⟩ [fm]⊢*
      ⟨A, 2, 1, F, 2 * F + 3, 0⟩ := by
    have h := r1r1r3_chain F A 1 0 3 0
    rw [show 1 + 2 * F = 2 * F + 1 from by ring] at h
    convert h using 2; ring_nf
  -- Phase 4: R1, R2
  have p4 : ⟨A, 2, 1, F, 2 * F + 3, 0⟩ [fm]⊢*
      ⟨A + 1, 0, 0, F + 1, 2 * F + 4, 1⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    rw [show 2 * F + 3 + 1 = 2 * F + 4 from by ring]
    step fm
    ring_nf; finish
  -- Phase 5: drain
  have p5 : ⟨A + 1, 0, 0, F + 1, 2 * F + 4, 1⟩ [fm]⊢*
      ⟨A + 2 * F + 3, 0, 0, 0, 2 * F + 4, F + 2⟩ := by
    have h := drain_chain (F + 1) (A + 1) 0 (2 * F + 4) 0
    convert h using 2; ring_nf
  have : 2 * (F + 2) = 2 * F + 4 := by ring
  rw [this]
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus p2
      (stepStar_trans p3 (stepStar_trans p4 p5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 4, 2⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, F⟩ ↦ ⟨A + 1, 0, 0, 0, 2 * (F + 1), F + 1⟩) ⟨2, 1⟩
  intro ⟨A, F⟩; exact ⟨⟨A + 2 * F + 2, F + 1⟩, main_trans A F⟩

end Sz22_2003_unofficial_1633
