import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1411: [7/15, 11/3, 54/77, 5/121, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 0 -1  0  0  1
 1  3  0 -1 -1
 0  0  1  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1411

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+3, c, d, e⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3+R2×3 chain: each round does R3 then R2 three times.
theorem r3r2r2_chain : ∀ k a d e, ⟨a, 0, 0, d + k, e + 1⟩ [fm]⊢* ⟨a + k, 0, 0, d, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) d (e + 2)); ring_nf; finish

-- R4 drain: pairs of e go to c.
theorem r4_drain : ∀ k a c e, ⟨a, 0, c, 0, e + 2 * k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e); ring_nf; finish

-- R5+R1 drain c to d.
theorem r5r1_drain : ∀ k a c d, ⟨a + k, 0, c + k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a c (d + 2)); ring_nf; finish

-- R1 drain b (with c available).
theorem r1_drain : ∀ k a c d e, ⟨a, k, c + k, d, e⟩ [fm]⊢* ⟨a, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a c (d + 1) e); ring_nf; finish

-- Main transition: (a+1, 0, 0, d+3, 0) ⊢⁺ (a+4, 0, 0, 2d+4, 0)
theorem main_trans (a d : ℕ) :
    ⟨a + 1, 0, 0, d + 3, 0⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 2 * d + 4, 0⟩ := by
  -- Phase 1: R5+R2
  step fm; step fm
  -- Phase 2: R3+R2×3 chain: (a, 0, 0, d+4, 1) → (a+d+4, 0, 0, 0, 2d+9)
  rw [show d + 3 + 1 = 0 + (d + 4) from by ring]
  apply stepStar_trans (r3r2r2_chain (d + 4) a 0 0)
  rw [show 0 + 2 * (d + 4) + 1 = 2 * d + 9 from by ring]
  -- Phase 3: R4 drain: (a+d+4, 0, 0, 0, 2d+9) → (a+d+4, 0, d+4, 0, 1)
  rw [show 2 * d + 9 = 1 + 2 * (d + 4) from by ring]
  apply stepStar_trans (r4_drain (d + 4) (a + (d + 4)) 0 1)
  rw [show 0 + (d + 4) = d + 4 from by ring]
  -- Phase 4: R5+R1: (a+d+4, 0, d+4, 0, 1) → (a+d+3, 0, d+3, 2, 1)
  rw [show a + (d + 4) = (a + d + 3) + 1 from by ring,
      show d + 4 = (d + 3) + 1 from by ring]
  apply stepStar_trans (by step fm; step fm; finish :
    ⟨(a + d + 3) + 1, 0, (d + 3) + 1, 0, 1⟩ [fm]⊢* ⟨a + d + 3, 0, d + 3, 2, 1⟩)
  -- Phase 5: R3 + R1×3: (a+d+3, 0, d+3, 2, 1) → (a+d+4, 0, d, 4, 0)
  apply stepStar_trans (by
    rw [show (2 : ℕ) = 1 + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show a + d + 3 + 1 = a + d + 4 from by ring]
    exact r1_drain 3 (a + d + 4) d 1 0 :
    ⟨a + d + 3, 0, d + 3, 2, 1⟩ [fm]⊢* ⟨a + d + 4, 0, d, 4, 0⟩)
  -- Phase 6: R5+R1 drain c: (a+d+4, 0, d, 4, 0) → (a+4, 0, 0, 2d+4, 0)
  have h6 : ⟨a + d + 4, 0, d, 4, 0⟩ [fm]⊢* ⟨a + 4, 0, 0, 4 + 2 * d, 0⟩ := by
    convert r5r1_drain d (a + 4) 0 4 using 2; ring_nf
  apply stepStar_trans h6; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 6, 0⟩) (by execute fm 42)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + 1, 0, 0, d + 3, 0⟩) ⟨0, 3⟩
  intro ⟨a, d⟩; exact ⟨⟨a + 3, 2 * d + 1⟩, main_trans a d⟩

end Sz22_2003_unofficial_1411
