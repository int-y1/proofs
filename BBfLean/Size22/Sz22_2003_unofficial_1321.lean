import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1321: [63/10, 1573/2, 2/33, 5/7, 14/13]

Vector representation:
```
-1  2 -1  1  0  0
-1  0  0  0  2  1
 1 -1  0  0 -1  0
 0  0  1 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1321

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

-- R4 chain: transfer d to c (a=0, b=0 so R1,R2,R3 don't fire)
theorem d_to_c : ∀ k, ∀ c d e f,
    ⟨(0 : ℕ), (0 : ℕ), c, d + k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + k, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e f)
    ring_nf; finish

-- R1+R3 interleaved chain: each round R1(a>=1,c>=1) then R3(b>=1,e>=1)
-- Net per round: b+1, c-1, d+1, e-1
-- Needs a=1 maintained: R1 sets a=0, R3 sets a=1
theorem r1r3_chain : ∀ k, ∀ b c d e f,
    ⟨(1 : ℕ), b, c + k, d, e + k, f⟩ [fm]⊢* ⟨(1 : ℕ), b + k, c, d + k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b + 1) c (d + 1) e f)
    ring_nf; finish

-- R3+R2 interleaved drain: each round R3(b>=1,e>=1,a=0) then R2(a=1,c=0)
-- Net per round: b-1, e+1, f+1
theorem r3r2_drain : ∀ k, ∀ b d e f,
    ⟨(0 : ℕ), b + k, (0 : ℕ), d, e + k, f⟩ [fm]⊢*
    ⟨(0 : ℕ), b, (0 : ℕ), d, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R3: (1, b+k, 0, d, e+k, f)
    step fm  -- R2: (0, b+k, 0, d, e+k+2, f+1)
    rw [show e + k + 2 = (e + 2) + k from by ring]
    apply stepStar_trans (ih b d (e + 2) (f + 1))
    ring_nf; finish

-- Main transition: canonical (0,0,0,D+2,2*(D+3),F+1) ->+ (0,0,0,D+3,2*(D+4),F+D+3)
theorem main_trans (D F : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D + 2, 2 * (D + 3), F + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D + 3, 2 * (D + 4), F + D + 3⟩ := by
  -- Phase 1: R4 x (D+2): move d to c
  rw [show D + 2 = 0 + (D + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (D + 2) 0 0 (2 * (D + 3)) (F + 1))
  rw [show 0 + (D + 2) = D + 2 from by ring]
  -- State: (0, 0, D+2, 0, 2*(D+3), F+1)
  -- Phase 2: R5
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 0, D + 2, 0, 2 * (D + 3), F + 1⟩ : Q) [fm]⊢
      ⟨1, 0, D + 2, 1, 2 * (D + 3), F⟩)
  -- State: (1, 0, D+2, 1, 2*(D+3), F)
  -- Phase 3: R1+R3 x (D+2) rounds
  rw [show D + 2 = 0 + (D + 2) from by ring,
      show 2 * (D + 3) = (D + 4) + (D + 2) from by ring]
  apply stepStar_trans (r1r3_chain (D + 2) 0 0 1 (D + 4) F)
  rw [show 0 + (D + 2) = D + 2 from by ring,
      show 1 + (D + 2) = D + 3 from by ring]
  -- State: (1, D+2, 0, D+3, D+4, F)
  -- Phase 4: R2 (a=1, c=0)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, D + 2, 0, D + 3, D + 4, F⟩ : Q) [fm]⊢
      ⟨0, D + 2, 0, D + 3, D + 6, F + 1⟩))
  -- State: (0, D+2, 0, D+3, D+6, F+1)
  -- Phase 5: R3+R2 x (D+2): interleaved drain
  rw [show D + 2 = 0 + (D + 2) from by ring,
      show D + 6 = 4 + (D + 2) from by ring]
  apply stepStar_trans (r3r2_drain (D + 2) 0 (D + 3) 4 (F + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 6, 2⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, f⟩ ↦ ⟨0, 0, 0, d + 2, 2 * (d + 3), f + 1⟩) ⟨0, 1⟩
  intro ⟨d, f⟩
  refine ⟨⟨d + 1, f + d + 2⟩, ?_⟩
  show ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 2, 2 * (d + 3), f + 1⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (d + 1) + 2, 2 * ((d + 1) + 3), (f + d + 2) + 1⟩
  rw [show (d + 1) + 2 = d + 3 from by ring,
      show 2 * ((d + 1) + 3) = 2 * (d + 4) from by ring,
      show (f + d + 2) + 1 = f + d + 3 from by ring]
  exact main_trans d f

end Sz22_2003_unofficial_1321
