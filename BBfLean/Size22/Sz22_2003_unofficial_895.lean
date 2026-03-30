import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #895: [4/15, 147/22, 25/2, 11/7, 33/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  2 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_895

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: drain d to e
theorem d_to_e : ∀ k, ∀ e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · finish
  · step fm
    apply stepStar_trans (ih (e + 1))
    rw [show e + 1 + k = e + (k + 1) from by ring]; finish

-- R3 chain: drain a, doubling into c
theorem r3_chain : ∀ k, ∀ c, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · finish
  · step fm
    apply stepStar_trans (ih (c + 2))
    rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring]; finish

-- R2+R1 interleaved chain
theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + k + 1, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c (d + 2) e)
    rw [show a + 1 + k + 1 = a + (k + 1) + 1 from by ring,
        show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]; finish

-- Main transition: (0, 0, d+3+g, d, 0) ⊢⁺ (0, 0, 2d+6+g, 2d+2, 0)
theorem main_trans (d g : ℕ) :
    ⟨0, 0, d + 3 + g, d, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * d + 6 + g, 2 * d + 2, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_e d 0 (c := d + 3 + g))
  rw [show (0 : ℕ) + d = d from by ring]
  rw [show d + 3 + g = (d + 2 + g) + 1 from by ring]
  step fm
  rw [show d + 2 + g = (d + 1 + g) + 1 from by ring]
  step fm
  apply stepStar_trans
  · show ⟨2, 0, d + 1 + g, 0, d + 1⟩ [fm]⊢* ⟨d + 3, 0, g, 2 * d + 2, 0⟩
    have h := r2r1_chain (d + 1) 1 g 0 0
    simp only [Nat.zero_add] at h
    rw [show 1 + 1 = 2 from by ring,
        show g + (d + 1) = d + 1 + g from by ring,
        show 1 + (d + 1) + 1 = d + 3 from by ring,
        show 2 * (d + 1) = 2 * d + 2 from by ring] at h
    exact h
  apply stepStar_trans (r3_chain (d + 3) g (d := 2 * d + 2))
  rw [show g + 2 * (d + 3) = 2 * d + 6 + g from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 2, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, g⟩ ↦ ⟨0, 0, d + 3 + g, d, 0⟩) ⟨2, 0⟩
  intro ⟨d, g⟩
  exact ⟨⟨2 * d + 2, g + 1⟩, by
    show ⟨0, 0, d + 3 + g, d, 0⟩ [fm]⊢⁺ ⟨0, 0, (2 * d + 2) + 3 + (g + 1), 2 * d + 2, 0⟩
    rw [show (2 * d + 2) + 3 + (g + 1) = 2 * d + 6 + g from by ring]
    exact main_trans d g⟩
