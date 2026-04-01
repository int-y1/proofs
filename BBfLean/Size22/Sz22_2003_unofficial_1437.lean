import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1437: [7/15, 242/3, 3/77, 25/121, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  2
 0  1  0 -1 -1
 0  0  2  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1437

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3-R2 chain: k rounds. Each round: R3 then R2, net a+=1, d-=1, e+=1.
theorem r3r2_chain : ∀ k a d e, ⟨a + 1, 0, 0, d + k, e + 1⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d, e + k + 1⟩ := by
  intro k; induction' k with k ih
  · intro a d e; exists 0
  · intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + 1 = (e + 1 : ℕ) from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) d (e + 1)); ring_nf; finish

-- R4 chain: k rounds converting 2k of e into 2k of c. Needs b=0, d=0.
theorem r4_chain : ∀ k c e, ⟨a, 0, c, 0, e + 2 * k⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c e; exists 0
  · intro c e
    rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (c + 2) e); ring_nf; finish

-- R5-R1 chain: k rounds. Each round: R5 then R1, net a-=1, c-=1, d+=2.
theorem r5r1_chain : ∀ k a c d, ⟨a + k, 0, c + k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih
  · intro a c d; exists 0
  · intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a c (d + 2)); ring_nf; finish

-- Main transition: (1, 0, 0, 2*(m+1), 0) ⊢⁺ (1, 0, 0, 4*m+6, 0)
theorem main_trans (m : ℕ) :
    ⟨1, 0, 0, 2 * m + 2, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 4 * m + 6, 0⟩ := by
  -- Phase A: R5, R2 → (1, 0, 0, 2*m+3, 2)
  step fm; step fm
  -- Phase B: R3-R2 chain, 2*m+3 rounds
  -- State: (1, 0, 0, 2*m+3, 2) = (0+1, 0, 0, 0+(2*m+3), 1+1)
  rw [show (2 : ℕ) * m + 1 + 1 + 1 = 0 + (2 * m + 3) from by ring,
      show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (r3r2_chain (2 * m + 3) 0 0 1)
  -- State: (2*m+4, 0, 0, 0, 2*m+5)
  rw [show 0 + (2 * m + 3) + 1 = 2 * m + 4 from by ring,
      show 1 + (2 * m + 3) + 1 = 2 * m + 5 from by ring]
  -- Phase C: R4 chain, m+2 rounds
  -- State: (2*m+4, 0, 0, 0, 2*m+5) = (2*m+4, 0, 0, 0, 1 + 2*(m+2))
  rw [show (2 * m + 5 : ℕ) = 1 + 2 * (m + 2) from by ring]
  apply stepStar_trans (r4_chain (m + 2) 0 1 (a := 2 * m + 4))
  -- State: (2*m+4, 0, 2*m+4, 0, 1)
  rw [show 0 + 2 * (m + 2) = 2 * m + 4 from by ring]
  -- Phase D: R5, R1, R3, R1
  rw [show (2 * m + 4 : ℕ) = (2 * m + 3) + 1 from by ring]
  step fm
  rw [show (2 * m + 3 : ℕ) + 1 = (2 * m + 3) + 1 from rfl]
  step fm; step fm; step fm
  -- State: (2*m+3, 0, 2*m+2, 2, 0)
  -- Phase E: R5-R1 chain, 2*m+2 rounds
  -- State is (2*m+3, 0, 2*m+2, 2, 0). Need form (1+(2*m+2), 0, 0+(2*m+2), 2, 0).
  have h5 : (2 * m + 3, 0, 2 * m + 2, 2, 0) = (1 + (2 * m + 2), 0, 0 + (2 * m + 2), (2 : ℕ), 0) :=
    by ring_nf
  rw [h5]
  apply stepStar_trans (r5r1_chain (2 * m + 2) 1 0 2)
  rw [show 2 + 2 * (2 * m + 2) = 4 * m + 6 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 0⟩)
  · execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨1, 0, 0, 2 * m + 2, 0⟩) 0
  intro m; refine ⟨2 * m + 2, ?_⟩
  rw [show 2 * (2 * m + 2) + 2 = 4 * m + 6 from by ring]
  exact main_trans m

end Sz22_2003_unofficial_1437
