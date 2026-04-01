import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1523: [7/30, 11/3, 45/77, 4/11, 21/2]

Vector representation:
```
-1 -1 -1  1  0
 0 -1  0  0  1
 0  2  1 -1 -1
 2  0  0  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1523

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3/R2/R2 chain: (0,0,c,d+k,e+1) ⊢* (0,0,c+k,d,e+k+1)
theorem r3r2r2_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e + 1⟩ [fm]⊢* ⟨0, 0, c + k, d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) d (e + 1)); ring_nf; finish

-- R4 chain: (a,0,c,0,e+k) ⊢* (a+2*k,0,c,0,e)
theorem r4_chain : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c e); ring_nf; finish

-- R5/R1 drain: (a+2*k,0,c+k,d,0) ⊢* (a,0,c,d+2*k,0)
theorem r5r1_drain : ∀ k, ∀ a c d, ⟨a + 2 * k, 0, c + k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a c (d + 2)); ring_nf; finish

-- Main transition: (2, 0, 0, d, 0) ⊢⁺ (2, 0, 0, 2*d+2, 0)
theorem main_trans (d : ℕ) :
    ⟨2, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2, 0, 0, 2 * d + 2, 0⟩ := by
  -- Phase 1: 5 opening steps to (0, 0, 0, d+1, 1)
  step fm; step fm; step fm; step fm; step fm
  -- Phase 2: R3/R2/R2 chain
  rw [show d + 1 = 0 + (d + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (d + 1) 0 0 0)
  -- Phase 3: R4 chain
  rw [show 0 + (d + 1) + 1 = 0 + (d + 2) from by ring,
      show 0 + (d + 1) = d + 1 from by ring]
  apply stepStar_trans (r4_chain (d + 2) 0 (d + 1) 0)
  -- Phase 4: R5/R1 drain
  apply stepStar_trans (show ⟨0 + 2 * (d + 2), 0, d + 1, 0, 0⟩ [fm]⊢* ⟨2, 0, 0, 2 * (d + 1), 0⟩ from by
    rw [show 0 + 2 * (d + 2) = 2 + 2 * (d + 1) from by ring]
    have h := r5r1_drain (d + 1) 2 0 0
    rw [show (0 : ℕ) + (d + 1) = d + 1 from by ring,
        show (0 : ℕ) + 2 * (d + 1) = 2 * (d + 1) from by ring] at h
    exact h)
  rw [show 2 * (d + 1) = 2 * d + 2 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨2, 0, 0, d, 0⟩) 2
  intro d; exact ⟨2 * d + 2, main_trans d⟩

end Sz22_2003_unofficial_1523
