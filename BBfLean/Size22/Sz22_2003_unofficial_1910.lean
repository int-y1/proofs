import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1910: [9/385, 1/15, 196/3, 5/7, 33/2]

Vector representation:
```
 0  2 -1 -1 -1
 0 -1 -1  0  0
 2 -1  0  2  0
 0  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1910

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- One round of the main loop: R4, R1, R3, R3
theorem round : ⟨A, 0, 0, D+2, E+1⟩ [fm]⊢* ⟨A+4, 0, 0, D+4, E⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Main loop: e+1 iterations of R4,R1,R3,R3
theorem main_loop : ∀ k, ∀ A D, ⟨A, 0, 0, D+2, k⟩ [fm]⊢* ⟨A+4*k, 0, 0, D+2*k+2, 0⟩ := by
  intro k; induction' k with k ih <;> intro A D
  · exists 0
  · rw [show D + 2 = D + 2 from rfl]
    apply stepStar_trans (round (A := A) (D := D) (E := k))
    rw [show D + 4 = (D + 2) + 2 from by ring]
    apply stepStar_trans (ih (A + 4) (D + 2))
    ring_nf; finish

-- Transfer d to c: (A, 0, c, d+k, 0) ->* (A, 0, c+k, d, 0)
theorem d_to_c : ∀ k, ∀ c d, ⟨A, 0, c, d+k, 0⟩ [fm]⊢* ⟨A, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- Drain via R5+R2 alternation: (A+k, 0, k, 0, E) ->* (A, 0, 0, 0, E+k)
theorem r5r2_drain : ∀ k, ∀ A E, ⟨A+k, 0, k, 0, E⟩ [fm]⊢* ⟨A, 0, 0, 0, E+k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm; step fm
    rw [show k + 1 = k + 1 from rfl]
    apply stepStar_trans (ih A (E + 1))
    ring_nf; finish

-- Main transition: (a+1, 0, 0, 0, e) ->⁺ (2*e+a+2, 0, 0, 0, 2*e+4)
theorem main_trans : ⟨a+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨2*e+a+2, 0, 0, 0, 2*e+4⟩ := by
  -- Opening: R5, R3 -> (a+2, 0, 0, 2, e+1)
  step fm; step fm
  -- Main loop: (a+2, 0, 0, 0+2, e+1) ->* (a+2+4*(e+1), 0, 0, 0+2*(e+1)+2, 0)
  apply stepStar_trans (main_loop (e+1) (a+2) 0)
  -- = (4*e+a+6, 0, 0, 2*e+4, 0)
  -- d_to_c: (4*e+a+6, 0, 0, 2*e+4, 0) ->* (4*e+a+6, 0, 2*e+4, 0, 0)
  rw [show a + 2 + 4 * (e + 1) = 4 * e + a + 6 from by ring,
      show 0 + 2 * (e + 1) + 2 = 0 + (2 * e + 4) from by ring]
  apply stepStar_trans (d_to_c (2*e+4) (A := 4*e+a+6) 0 0)
  simp only [Nat.zero_add]
  rw [show 4 * e + a + 6 = (2 * e + a + 2) + (2 * e + 4) from by ring]
  apply stepStar_trans (r5r2_drain (2*e+4) (2*e+a+2) 0)
  simp only [Nat.zero_add]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 4⟩) (by execute fm 18)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a+1, 0, 0, 0, e⟩) ⟨1, 4⟩
  intro ⟨a, e⟩; exact ⟨⟨2*e+a+1, 2*e+4⟩, main_trans⟩
