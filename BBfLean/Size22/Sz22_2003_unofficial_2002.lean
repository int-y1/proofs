import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #2002: [99/35, 88/5, 5/6, 7/11, 5/2]

Vector representation:
```
 0  2 -1 -1  1
 3  0 -1  0  1
-1 -1  1  0  0
 0  0  0  1 -1
-1  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_2002

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+3, b, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move e to d. (a, 0, 0, d, e+k) →* (a, 0, 0, d+k, e).
theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

-- R1/R3 interleaved: (a+k, b, 1, d+k, e) →* (a, b+k, 1, d, e+k)
theorem r1r3_chain : ∀ k a b e, ⟨a + k, b, 1, d + k, e⟩ [fm]⊢* ⟨a, b + k, 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih a (b + 1) (e + 1))
    ring_nf; finish

-- R1/R3 chain + final R1/R3: (a+d+2, 0, 1, d+1, e) →* (a+1, d+1, 1, 0, d+1+e)
theorem partA_general : ⟨a + d + 2, 0, 1, d + 1, e⟩ [fm]⊢* ⟨a + 1, d + 1, 1, 0, d + 1 + e⟩ := by
  rw [show a + d + 2 = (a + 2) + d from by ring,
      show d + 1 = 1 + d from by ring]
  apply stepStar_trans (r1r3_chain d (a + 2) 0 e (d := 1))
  rw [show (0 : ℕ) + d = d from by ring]
  step fm
  step fm
  ring_nf; finish

-- Specialized for e=0: (a+d+2, 0, 1, d+1, 0) →* (a+1, d+1, 1, 0, d+1)
theorem partA : ⟨a + d + 2, 0, 1, d + 1, 0⟩ [fm]⊢* ⟨a + 1, d + 1, 1, 0, d + 1⟩ := by
  have h := partA_general (a := a) (d := d) (e := 0)
  simp only [Nat.add_zero] at h
  exact h

-- R2/R3 interleaved draining b: (a, k, 1, 0, e) →* (a+2*k, 0, 1, 0, e+k)
theorem r2r3_drain : ∀ k a e, ⟨a, k, 1, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 1, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (a + 2) (e + 1))
    ring_nf; finish

-- Main transition: (F+e+3, 0, 0, 0, e+1) ⊢⁺ (F+2e+6, 0, 0, 0, 2e+3)
theorem main_trans (F e : ℕ) : ⟨F + e + 3, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨F + 2 * e + 6, 0, 0, 0, 2 * e + 3⟩ := by
  -- Phase 1: R4 chain: (F+e+3, 0, 0, 0, e+1) →* (F+e+3, 0, 0, e+1, 0)
  apply stepStar_stepPlus_stepPlus (e_to_d (e + 1) 0 (a := F + e + 3))
  -- Phase 2: R5: (F+e+3, 0, 0, e+1, 0). a = F+e+3 >= 1, b=0: R5 fires.
  rw [show (0 : ℕ) + (e + 1) = e + 1 from by ring]
  step fm
  -- Phase 3: Part A: (F+e+2, 0, 1, e+1, 0). Use partA with a=F, d=e.
  apply stepStar_trans (partA (a := F) (d := e))
  -- Now at (F+1, e+1, 1, 0, e+1). Apply Part B: r2r3_drain.
  apply stepStar_trans (r2r3_drain (e + 1) (F + 1) (e + 1))
  -- Now at (F+1+2*(e+1), 0, 1, 0, e+1+(e+1)). Final R2.
  rw [show F + 1 + 2 * (e + 1) = F + 2 * e + 3 from by ring,
      show e + 1 + (e + 1) = 2 * e + 2 from by ring]
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, e⟩ ↦ ⟨F + e + 3, 0, 0, 0, e + 1⟩) ⟨0, 0⟩
  intro ⟨F, e⟩
  refine ⟨⟨F + 1, 2 * e + 2⟩, ?_⟩
  show ⟨F + e + 3, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨F + 1 + (2 * e + 2) + 3, 0, 0, 0, 2 * e + 2 + 1⟩
  rw [show F + 1 + (2 * e + 2) + 3 = F + 2 * e + 6 from by ring,
      show 2 * e + 2 + 1 = 2 * e + 3 from by ring]
  exact main_trans F e

end Sz22_2003_unofficial_2002
