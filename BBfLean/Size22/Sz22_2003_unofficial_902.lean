import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #902: [4/15, 3/14, 275/2, 7/11, 154/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0  0  0  1 -1
 1  0 -1  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_902

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e+1⟩
  | _ => none

-- R4 repeated: drain e to d.
theorem e_to_d : ∀ k, ⟨(0 : ℕ), 0, c, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

-- R2/R1 interleaved: (a+1, 0, c+k+1, k+1, 1) →* (a+k+2, 0, c, 0, 1)
theorem r2r1_chain : ∀ k, ⟨a + 1, 0, c + k + 1, k + 1, 1⟩ [fm]⊢* ⟨a + k + 2, 0, c, 0, 1⟩ := by
  intro k; induction' k with k ih generalizing a c
  · step fm; step fm; finish
  · rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring,
        show (k + 1) + 1 = (k + 1) + 1 from by ring]
    step fm
    step fm
    rw [show a + 1 + 1 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

-- R3 chain: (a+k, 0, c, 0, e) →* (a, 0, c+2*k, 0, e+k)
theorem r3_chain : ∀ k, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 2) (e := e + 1))
    ring_nf; finish

-- Compose phases 1-2: (0,0,C+1,0,E) →⁺ (1,0,C,E+1,1)
theorem phases_12 : ⟨(0 : ℕ), 0, C + 1, 0, E⟩ [fm]⊢⁺ ⟨(1 : ℕ), 0, C, E + 1, 1⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show (E : ℕ) = 0 + E from by ring]
    exact e_to_d E (c := C + 1) (d := 0) (e := 0)
  · rw [show (0 : ℕ) + E = E from by ring]
    step fm; finish

-- Main: (0, 0, r+e+3, 0, e+1) →⁺ (0, 0, r+2*e+6, 0, e+4)
theorem main_trans : ⟨(0 : ℕ), 0, r + e + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, r + 2 * e + 6, 0, e + 4⟩ := by
  -- Phases 1-2: (0,0,r+e+3,0,e+1) →⁺ (1,0,r+e+2,e+2,1)
  rw [show r + e + 3 = (r + e + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phases_12 (C := r + e + 2) (E := e + 1))
  -- Phase 3: r2r1_chain
  rw [show (e + 1) + 1 = (e + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show r + e + 2 = r + (e + 1) + 1 from by ring]
  apply stepStar_trans (r2r1_chain (e + 1) (a := 0) (c := r))
  -- Phase 4: r3_chain
  rw [show 0 + (e + 1) + 2 = 0 + (e + 3) from by ring]
  apply stepStar_trans (r3_chain (e + 3) (a := 0) (c := r) (e := 1))
  rw [show r + 2 * (e + 3) = r + 2 * e + 6 from by ring,
      show 1 + (e + 3) = e + 4 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 11, 0, 7⟩)
  · execute fm 31
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨r, e⟩ ↦ ⟨0, 0, r + e + 3, 0, e + 1⟩) ⟨2, 6⟩
  intro ⟨r, e⟩
  refine ⟨⟨r + e, e + 3⟩, ?_⟩
  show ⟨(0 : ℕ), 0, r + e + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, (r + e) + (e + 3) + 3, 0, (e + 3) + 1⟩
  rw [show (r + e) + (e + 3) + 3 = r + 2 * e + 6 from by ring,
      show (e + 3) + 1 = e + 4 from by ring]
  exact main_trans

end Sz22_2003_unofficial_902
