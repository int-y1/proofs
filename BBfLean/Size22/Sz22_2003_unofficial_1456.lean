import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1456: [7/15, 3/154, 275/7, 4/5, 21/2]

Vector representation:
```
 0 -1 -1  1  0
-1  1  0 -1 -1
 0  0  2 -1  1
 2  0 -1  0  0
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1456

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

variable {a b c d e : ℕ}

-- R5/R2 alternation: drain a and e
theorem r5r2_drain : ∀ k, ⟨2 * k + 2, b, 0, 0, k⟩ [fm]⊢* ⟨2, b + 2 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b := b + 2))
    ring_nf; finish

-- R3/R1/R1 chain: drain b pairwise
theorem r3r1r1_chain : ∀ k, ∀ d e, ⟨0, 2 * k, 0, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (d + 1) (e + 1))
    ring_nf; finish

-- R3 chain: drain d to c and e
theorem r3_chain : ∀ d, ⟨0, 0, c, d, e⟩ [fm]⊢* ⟨0, 0, c + 2 * d, 0, e + d⟩ := by
  intro d; induction' d with d ih generalizing c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 2) (e := e + 1))
    ring_nf; finish

-- R4 chain: drain c to a
theorem r4_chain : ∀ c, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨a + 2 * c, 0, 0, 0, e⟩ := by
  intro c; induction' c with c ih generalizing a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

-- Main transition: (2*e+4, 0, 0, 0, e+1) →⁺ (4*e+8, 0, 0, 0, 2*e+3)
theorem main_trans (e : ℕ) :
    ⟨2 * e + 4, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨4 * e + 8, 0, 0, 0, 2 * e + 3⟩ := by
  rw [show 2 * e + 4 = (2 * e + 2 + 1) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (r5r2_drain e (b := 2))
  rw [show 2 + 2 * e = 2 * e + 2 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm
  rw [show 2 * e + 2 = 2 * (e + 1) from by ring]
  apply stepStar_trans (r3r1r1_chain (e + 1) 0 0)
  rw [show 0 + (e + 1) + 1 = e + 2 from by ring,
      show 0 + (e + 1) = e + 1 from by ring]
  apply stepStar_trans (r3_chain (e + 2) (c := 0) (e := e + 1))
  rw [show 0 + 2 * (e + 2) = 2 * e + 4 from by ring,
      show e + 1 + (e + 2) = 2 * e + 3 from by ring]
  apply stepStar_trans (r4_chain (2 * e + 4) (a := 0) (e := 2 * e + 3))
  rw [show 0 + 2 * (2 * e + 4) = 4 * e + 8 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨6, 0, 0, 0, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * (n + 2) + 2, 0, 0, 0, n + 2⟩) 0
  intro n
  exists 2 * n + 3
  show ⟨2 * (n + 2) + 2, 0, 0, 0, n + 2⟩ [fm]⊢⁺ ⟨2 * (2 * n + 3 + 2) + 2, 0, 0, 0, 2 * n + 3 + 2⟩
  rw [show 2 * (n + 2) + 2 = 2 * (n + 1) + 4 from by ring,
      show n + 2 = (n + 1) + 1 from by ring,
      show 2 * (2 * n + 3 + 2) + 2 = 4 * (n + 1) + 8 from by ring,
      show 2 * n + 3 + 2 = 2 * (n + 1) + 3 from by ring]
  exact main_trans (n + 1)

end Sz22_2003_unofficial_1456
