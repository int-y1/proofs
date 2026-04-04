import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1903: [9/35, 65/33, 14/3, 11/13, 455/2]

Vector representation:
```
 0  2 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  1  0  0
 0  0  0  0  1 -1
-1  0  1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1903

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f+1⟩
  | _ => none

-- R2+R1 interleaved chain: (a, b+2, 0, d+k, k, f) →* (a, b+k+2, 0, d, 0, f+k)
theorem r2r1_chain : ∀ k, ∀ b d f, ⟨a, b + 2, 0, d + k, k, f⟩ [fm]⊢* ⟨a, b + k + 2, 0, d, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b d f
  · exists 0
  · rw [show b + 2 = (b + 1) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b + 1) d (f + 1))
    ring_nf; finish

-- R3 chain: (a, b+k, 0, d, 0, f) →* (a+k, b, 0, d+k, 0, f)
theorem r3_chain : ∀ k, ∀ a b d f, ⟨a, b + k, 0, d, 0, f⟩ [fm]⊢* ⟨a + k, b, 0, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a b d f
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b (d + 1) f)
    ring_nf; finish

-- R4 chain: (a, 0, 0, d, e, f+k) →* (a, 0, 0, d, e+k, f)
theorem r4_chain : ∀ k, ∀ a d e f, ⟨a, 0, 0, d, e, f + k⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) f)
    ring_nf; finish

-- Main transition: (a+1, 0, 0, 2*e+2, e+1, 0) →⁺ (a+e+3, 0, 0, 2*e+4, e+2, 0)
theorem main_trans : ⟨a + 1, 0, 0, 2 * e + 2, e + 1, 0⟩ [fm]⊢⁺ ⟨a + e + 3, 0, 0, 2 * e + 4, e + 2, 0⟩ := by
  -- R5 step
  step fm
  -- R1 step
  rw [show 2 * e + 2 + 1 = (2 * e + 2) + 1 from by ring]
  step fm
  -- R2+R1 chain: e+1 rounds
  rw [show (2 * e + 2 : ℕ) = (e + 1) + (e + 1) from by ring]
  apply stepStar_trans (r2r1_chain (a := a) (e + 1) 0 (e + 1) 1)
  -- R3 chain
  rw [show 0 + (e + 1) + 2 = 0 + (e + 3) from by ring]
  apply stepStar_trans (r3_chain (e + 3) a 0 (e + 1) (1 + (e + 1)))
  -- R4 chain
  rw [show 1 + (e + 1) = 0 + (e + 2) from by ring]
  apply stepStar_trans (r4_chain (e + 2) (a + (e + 3)) (e + 1 + (e + 3)) 0 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 1, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + 1, 0, 0, 2 * e + 2, e + 1, 0⟩) ⟨1, 0⟩
  intro ⟨a, e⟩; exact ⟨⟨a + e + 2, e + 1⟩, main_trans⟩
