import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1320: [63/10, 1573/2, 2/33, 5/7, 10/13]

Vector representation:
```
-1  2 -1  1  0  0
-1  0  0  0  2  1
 1 -1  0  0 -1  0
 0  0  1 -1  0  0
 1  0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1320

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c+1, d, e, f⟩
  | _ => none

-- R4 repeated: (0,0,c,D,e,f) →* (0,0,c+D,0,e,f)
theorem d_to_c : ∀ D, ∀ c e f,
    ⟨(0 : ℕ), (0 : ℕ), c, D, e, f⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + D, 0, e, f⟩ := by
  intro D; induction' D with D ih <;> intro c e f
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e f)
    ring_nf; finish

-- R3+R1 chain of k rounds.
-- (0, b+2, k, d, e+k, f) →* (0, b+k+2, 0, d+k, e, f)
theorem r3r1_chain : ∀ k, ∀ b d e f,
    ⟨(0 : ℕ), b + 2, k, d, e + k, f⟩ [fm]⊢* ⟨(0 : ℕ), b + k + 2, 0, d + k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    rw [show b + 3 = (b + 1) + 2 from by ring]
    apply stepStar_trans (ih (b + 1) (d + 1) e f)
    ring_nf; finish

-- R3+R2 chain of k rounds. Each round: R3 then R2 (c=0).
-- (0, k, 0, d, k+e, f) →* (0, 0, 0, d, 2*k+e, f+k)
theorem r3r2_chain : ∀ k, ∀ d e f,
    ⟨(0 : ℕ), k, (0 : ℕ), d, k + e, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, (0 : ℕ), d, 2 * k + e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · rw [show k + 1 + e = (k + e) + 1 from by ring]
    step fm  -- R3: (1, k, 0, d, k+e, f)
    step fm  -- R2: (0, k, 0, d, k+e+2, f+1)
    rw [show k + e + 2 = k + (e + 2) from by ring]
    apply stepStar_trans (ih d (e + 2) (f + 1))
    ring_nf; finish

-- Main transition: (0,0,0,D,2D+2,F+1) ⊢⁺ (0,0,0,D+1,2D+4,F+D+2)
theorem main_trans (D F : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D, 2 * D + 2, F + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D + 1, 2 * D + 4, F + D + 2⟩ := by
  -- Phase 1: R4 x D
  apply stepStar_stepPlus_stepPlus (d_to_c D 0 (2 * D + 2) (F + 1))
  rw [show 0 + D = D from by ring]
  -- Phase 2: R5
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 0, D, 0, 2 * D + 2, F + 1⟩ : Q) [fm]⊢
      ⟨1, 0, D + 1, 0, 2 * D + 2, F⟩)
  -- Phase 3: R1
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0 + 1, 0, D + 1, 0, 2 * D + 2, F⟩ : Q) [fm]⊢
      ⟨0, 2, D, 1, 2 * D + 2, F⟩))
  -- Phase 4: R3+R1 x D: (0,2,D,1,2D+2,F) →* (0,D+2,0,D+1,D+2,F)
  rw [show (2 : ℕ) = 0 + 2 from by ring,
      show 2 * D + 2 = (D + 2) + D from by ring]
  apply stepStar_trans (r3r1_chain D 0 1 (D + 2) F)
  rw [show 0 + D + 2 = D + 2 from by ring,
      show 1 + D = D + 1 from by ring]
  -- Phase 5: R3+R2 x (D+2): (0,D+2,0,D+1,D+2,F) →* (0,0,0,D+1,2D+4,F+D+2)
  -- r3r2_chain needs (0, k, 0, d, k+e, f). With k=D+2, e=0: k+e = D+2. OK.
  rw [show D + 2 = D + 2 + 0 from by ring]
  apply stepStar_trans (r3r2_chain (D + 2) (D + 1) 0 F)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨D, F⟩ ↦ ⟨0, 0, 0, D, 2 * D + 2, F + 1⟩) ⟨0, 0⟩
  intro ⟨D, F⟩
  refine ⟨⟨D + 1, F + D + 1⟩, ?_⟩
  show ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D, 2 * D + 2, F + 1⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D + 1, 2 * (D + 1) + 2, (F + D + 1) + 1⟩
  rw [show 2 * (D + 1) + 2 = 2 * D + 4 from by ring,
      show (F + D + 1) + 1 = F + D + 2 from by ring]
  exact main_trans D F

end Sz22_2003_unofficial_1320
