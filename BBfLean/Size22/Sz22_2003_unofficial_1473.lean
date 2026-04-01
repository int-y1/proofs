import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1473: [7/15, 4/3, 1089/14, 5/11, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 2 -1  0  0  0
-1  2  0 -1  2
 0  0  1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1473

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer e to c (b=0, d=0)
theorem e_to_c : ∀ k c, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c; exists 0
  · intro c
    have h1 : (⟨a, 0, c, 0, e + (k + 1)⟩ : Q) [fm]⊢ ⟨a, 0, c + 1, 0, e + k⟩ := by
      rcases a with _ | a <;> simp [fm]
    apply stepStar_trans (step_stepStar h1)
    rw [show c + (k + 1) = c + 1 + k from by ring]
    exact ih (c + 1)

-- R3+R2+R2 chain
theorem r3r2r2_chain : ∀ k, ∀ a d e, ⟨a + 1, 0, 0, d + k, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro a d e; exists 0
  · intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) d (e + 2)); ring_nf; finish

-- R3+R1+R1 inner drain
theorem r3r1r1_chain : ∀ k, ∀ a c d e, ⟨a + k + 1, 0, 2 * k + 1 + c, d + 1, e⟩ [fm]⊢* ⟨a + 1, 0, 1 + c, d + k + 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro a c d e; exists 0
  · intro a c d e
    rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
        show 2 * (k + 1) + 1 + c = (2 * k + 1 + c) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 1) (e + 2)); ring_nf; finish

-- Final c=1 step: R3+R1+R2
theorem final_c1 (a d e : ℕ) : ⟨a + 1, 0, 1, d + 1, e⟩ [fm]⊢* ⟨a + 2, 0, 0, d + 1, e + 2⟩ := by
  step fm; step fm; step fm; finish

-- Phase 1: R5, R1, r3r1r1_chain, final_c1
theorem phase1 (J F : ℕ) : ⟨2 * J + 2 * F + 3, 0, 2 * J + 2, 0, 0⟩ [fm]⊢*
    ⟨J + 2 * F + 3, 0, 0, J + 2, 2 * J + 2⟩ := by
  rw [show 2 * J + 2 * F + 3 = (2 * J + 2 * F + 2) + 1 from by ring,
      show 2 * J + 2 = (2 * J + 1) + 1 from by ring]
  step fm; step fm
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring,
      show 2 * J + 1 = 2 * J + 1 + 0 from by ring,
      show 2 * J + 2 * F + 2 = (J + 2 * F + 1) + J + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain J (J + 2 * F + 1) 0 (0 + 1) 0)
  rw [show J + 2 * F + 1 + 1 = (J + 2 * F + 1) + 1 from by ring,
      show (1 + 0 : ℕ) = 1 from by ring,
      show 0 + 1 + J + 1 = (J + 1) + 1 from by ring,
      show 0 + 2 * J = 2 * J from by ring]
  apply stepStar_trans (final_c1 (J + 2 * F + 1) (J + 1) (2 * J))
  ring_nf; finish

-- Main transition J=0: (2F+1, 0, 0, 0, 0) ⊢⁺ (2F+5, 0, 2, 0, 0)
theorem main_trans_j0 (F : ℕ) :
    ⟨2 * F + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨2 * F + 5, 0, 2, 0, 0⟩ := by
  rw [show 2 * F + 1 = F + F + 1 from by ring]
  step fm; step fm
  rw [show F + F + 2 = (F + F + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain 1 (F + F + 1) 0 0)
  rw [show F + F + 1 + 3 * 1 + 1 = 2 * F + 5 from by ring,
      show (0 + 2 * 1 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (e_to_c 2 0 (a := 2 * F + 5) (e := 0))
  ring_nf; finish

-- Main transition J>=1: phase1, R3, R2, R2, r3r2r2_chain, e_to_c
theorem main_trans_jpos (F J : ℕ) :
    ⟨2 * J + 2 * F + 3, 0, 2 * J + 2, 0, 0⟩ [fm]⊢⁺ ⟨4 * J + 2 * F + 9, 0, 4 * J + 6, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (phase1 J F)
  rw [show J + 2 * F + 3 = (J + 2 * F + 2) + 1 from by ring,
      show J + 2 = 0 + (J + 2) from by ring]
  apply step_stepStar_stepPlus
    (show (⟨(J + 2 * F + 2) + 1, 0, 0, 0 + (J + 2), 2 * J + 2⟩ : Q) [fm]⊢
          ⟨J + 2 * F + 2, 2, 0, 0 + (J + 2) - 1, 2 * J + 2 + 2⟩ from by
      rw [show 0 + (J + 2) = (J + 1) + 1 from by ring]; unfold fm; rfl)
  rw [show 0 + (J + 2) - 1 = J + 1 from by omega,
      show 2 * J + 2 + 2 = 2 * J + 4 from by ring]
  step fm; step fm
  rw [show J + 2 * F + 2 + 2 + 2 = (J + 2 * F + 5) + 1 from by ring,
      show J + 1 = 0 + (J + 1) from by ring]
  apply stepStar_trans (r3r2r2_chain (J + 1) (J + 2 * F + 5) 0 (2 * J + 4))
  rw [show J + 2 * F + 5 + 3 * (J + 1) + 1 = 4 * J + 2 * F + 9 from by ring,
      show 2 * J + 4 + 2 * (J + 1) = 0 + (4 * J + 6) from by ring]
  apply stepStar_trans (e_to_c (4 * J + 6) 0 (a := 4 * J + 2 * F + 9) (e := 0))
  ring_nf; finish

-- Combined
theorem main_trans (F J : ℕ) :
    ⟨2 * J + 2 * F + 1, 0, 2 * J, 0, 0⟩ [fm]⊢⁺ ⟨2 * (2 * J + 1) + 2 * (F + 1) + 1, 0, 2 * (2 * J + 1), 0, 0⟩ := by
  rcases J with _ | J
  · rw [show 2 * 0 + 2 * F + 1 = 2 * F + 1 from by ring,
        show 2 * 0 = 0 from by ring,
        show 2 * (2 * 0 + 1) + 2 * (F + 1) + 1 = 2 * F + 5 from by ring,
        show 2 * (2 * 0 + 1) = 2 from by ring]
    exact main_trans_j0 F
  · rw [show 2 * (2 * (J + 1) + 1) + 2 * (F + 1) + 1 = 4 * J + 2 * F + 9 from by ring,
        show 2 * (2 * (J + 1) + 1) = 4 * J + 6 from by ring,
        show 2 * (J + 1) + 2 * F + 1 = 2 * J + 2 * F + 3 from by ring,
        show 2 * (J + 1) = 2 * J + 2 from by ring]
    exact main_trans_jpos F J

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, J⟩ ↦ ⟨2 * J + 2 * F + 1, 0, 2 * J, 0, 0⟩) ⟨0, 0⟩
  intro ⟨F, J⟩; exact ⟨⟨F + 1, 2 * J + 1⟩, main_trans F J⟩

end Sz22_2003_unofficial_1473
