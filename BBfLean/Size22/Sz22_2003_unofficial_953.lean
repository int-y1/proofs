import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #953: [4/15, 33/14, 275/2, 7/11, 9/7]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 0  2  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_953

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) (e + 1)); ring_nf; finish

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c e,
    ⟨a + 1, 0, c + k, k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1)); ring_nf; finish

theorem main_trans (p e : ℕ) :
    ⟨0, 0, p + e + 2, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, p + 2 * e + 8, 0, 2 * e + 4⟩ := by
  -- Phase 1: R4 drain (e+1 steps): (0,0,p+e+2,0,e+1) ⊢* (0,0,p+e+2,e+1,0)
  have h1 := r4_drain (e + 1) (p + e + 2) 0
  rw [show 0 + (e + 1) = e + 1 from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2: R5 step + R1 + R1 (3 steps): (0,0,p+e+2,e+1,0) -> (4,0,p+e,e,0)
  rw [show p + e + 2 = (p + e) + 1 + 1 from by ring]
  step fm; step fm
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  -- Phase 3: R2/R1 chain (e rounds): (4,0,p+e,e,0) ⊢* (e+4,0,p,0,e)
  rw [show (4 : ℕ) = 3 + 1 from rfl]
  apply stepStar_trans (r2r1_chain e 3 p 0)
  rw [show 3 + e + 1 = e + 4 from by ring,
      show 0 + e = e from by ring]
  -- Phase 4: R3 drain (e+4 steps): (e+4,0,p,0,e) ⊢* (0,0,p+2e+8,0,2e+4)
  have h4 := r3_drain (e + 4) p e
  rw [show p + 2 * (e + 4) = p + 2 * e + 8 from by ring,
      show e + (e + 4) = 2 * e + 4 from by ring] at h4
  exact h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨p, e⟩ ↦ ⟨0, 0, p + e + 2, 0, e + 1⟩) ⟨0, 0⟩
  intro ⟨p, e⟩
  refine ⟨⟨p + 3, 2 * e + 3⟩, ?_⟩
  show ⟨0, 0, p + e + 2, 0, e + 1⟩ [fm]⊢⁺
    ⟨0, 0, (p + 3) + (2 * e + 3) + 2, 0, (2 * e + 3) + 1⟩
  rw [show (p + 3) + (2 * e + 3) + 2 = p + 2 * e + 8 from by ring,
      show (2 * e + 3) + 1 = 2 * e + 4 from by ring]
  exact main_trans p e
