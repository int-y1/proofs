import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1829: [9/10, 55/21, 88/3, 7/11, 3/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 3 -1  0  0  1
 0  0  0  1 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1829

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+3, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R2+R1 interleaving: each round does a -= 1, b += 1, d -= 1, e += 1
theorem r2r1_chain : ∀ d, ∀ a b e, ⟨a + d, b + 1, 0, d, e⟩ [fm]⊢* ⟨a, b + d + 1, 0, 0, e + d⟩ := by
  intro d; induction' d with d ih <;> intro a b e
  · exists 0
  · rw [show a + (d + 1) = (a + d) + 1 from by ring]
    step fm
    step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih a (b + 1) (e + 1))
    ring_nf; finish

-- R3 chain: b+1 rounds of R3
theorem r3_chain : ∀ b, ∀ a e, ⟨a, b + 1, 0, 0, e⟩ [fm]⊢* ⟨a + 3 * (b + 1), 0, 0, 0, e + b + 1⟩ := by
  intro b; induction' b with b ih <;> intro a e
  · step fm; ring_nf; finish
  · step fm
    rw [show a + 3 = (a + 3) from rfl]
    apply stepStar_trans (ih (a + 3) (e + 1))
    ring_nf; finish

-- R4 chain: move e to d
theorem e_to_d : ∀ k, ∀ a d e, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show d + 1 = (d + 1) from rfl]
    apply stepStar_trans (ih a (d + 1) e)
    ring_nf; finish

-- Main transition: C(d) -> C(2d+1) where C(d) = (2d+1, 0, 0, d, 0)
theorem main_trans : ∀ d, ⟨2 * (d + 1) + 1, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨4 * (d + 1) + 3, 0, 0, 2 * (d + 1) + 1, 0⟩ := by
  intro d
  rw [show 2 * (d + 1) + 1 = (2 * d + 2) + 1 from by ring]
  step fm
  rw [show 2 * d + 2 = (d + 1) + (d + 1) from by ring]
  apply stepStar_trans (r2r1_chain (d + 1) (d + 1) 0 0)
  rw [show 0 + (d + 1) + 1 = (d + 1) + 1 from by ring,
      show 0 + (d + 1) = d + 1 from by ring]
  apply stepStar_trans (r3_chain (d + 1) (d + 1) (d + 1))
  rw [show d + 1 + 3 * (d + 1 + 1) = 4 * (d + 1) + 3 from by ring,
      show d + 1 + (d + 1) + 1 = 2 * (d + 1) + 1 from by ring]
  rw [show (2 * (d + 1) + 1 : ℕ) = 0 + (2 * (d + 1) + 1) from by ring]
  apply stepStar_trans (e_to_d (2 * (d + 1) + 1) (4 * (d + 1) + 3) 0 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨2 * (d + 1) + 1, 0, 0, d + 1, 0⟩) 0
  intro d
  exact ⟨2 * (d + 1), by
    show ⟨2 * (d + 1) + 1, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨2 * (2 * (d + 1) + 1) + 1, 0, 0, 2 * (d + 1) + 1, 0⟩
    rw [show 2 * (2 * (d + 1) + 1) + 1 = 4 * (d + 1) + 3 from by ring,
        show 2 * (d + 1) + 1 = 2 * (d + 1) + 1 from rfl]
    exact main_trans d⟩

end Sz22_2003_unofficial_1829
