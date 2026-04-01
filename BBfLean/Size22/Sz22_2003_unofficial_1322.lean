import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1322: [63/10, 1573/2, 2/33, 5/7, 15/13]

Vector representation:
```
-1  2 -1  1  0  0
-1  0  0  0  2  1
 1 -1  0  0 -1  0
 0  0  1 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1322

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R4 chain: transfer d to c
theorem d_to_c : ∀ k, ∀ c d e f,
    ⟨(0 : ℕ), (0 : ℕ), c, d + k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + k, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e f)
    ring_nf; finish

-- R3+R1 interleaved chain: each round consumes 1 from c and 1 from e, adds 1 to b and 1 to d
theorem r3r1_chain : ∀ k, ∀ b c d e f,
    ⟨(0 : ℕ), b + 1, c + k, d, e + k, f⟩ [fm]⊢* ⟨(0 : ℕ), b + 1 + k, c, d + k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b + 1) c (d + 1) e f)
    ring_nf; finish

-- R3+R2 interleaved chain: each round consumes 1 from b, adds 1 to e and 1 to f
theorem r3r2_chain : ∀ k, ∀ d e f,
    ⟨(0 : ℕ), k, (0 : ℕ), d, e + 1, f⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d, e + k + 1, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    step fm
    apply stepStar_trans (ih d (e + 1) (f + 1))
    ring_nf; finish

-- Main transition: canonical (0,0,0,d+1,d+3,f+2) ->+ (0,0,0,d+2,d+4,f+d+4)
theorem main_trans (d f : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 1, d + 3, f + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 2, d + 4, f + d + 4⟩ := by
  -- Phase 1: R4 x (d+1): move d to c
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (d + 1) 0 0 (d + 3) (f + 2))
  rw [show 0 + (d + 1) = d + 1 from by ring]
  -- State: (0, 0, d+1, 0, d+3, f+2)
  -- Phase 2: R5
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 0, d + 1, 0, d + 3, f + 2⟩ : Q) [fm]⊢
      ⟨0, 1, d + 2, 0, d + 3, f + 1⟩)
  -- State: (0, 1, d+2, 0, d+3, f+1)
  -- Phase 3: R3+R1 x (d+2) rounds
  rw [show d + 2 = 0 + (d + 2) from by ring,
      show d + 3 = 1 + (d + 2) from by ring]
  apply stepStar_trans (r3r1_chain (d + 2) 0 0 0 1 (f + 1))
  rw [show 0 + 1 + (d + 2) = d + 3 from by ring,
      show 0 + (d + 2) = d + 2 from by ring]
  -- State: (0, d+3, 0, d+2, 1, f+1)
  -- Phase 4: R3 (consume last e)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, d + 3, 0, d + 2, 1, f + 1⟩ : Q) [fm]⊢
      ⟨1, d + 2, 0, d + 2, 0, f + 1⟩))
  -- State: (1, d+2, 0, d+2, 0, f+1)
  -- Phase 5: R2 (a=1, c=0)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, d + 2, 0, d + 2, 0, f + 1⟩ : Q) [fm]⊢
      ⟨0, d + 2, 0, d + 2, 2, f + 2⟩))
  -- State: (0, d+2, 0, d+2, 2, f+2)
  -- Phase 6: R3+R2 x (d+2) rounds: drain b
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (d + 2) (d + 2) 1 (f + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, f⟩ ↦ ⟨0, 0, 0, d + 1, d + 3, f + 2⟩) ⟨0, 0⟩
  intro ⟨d, f⟩
  refine ⟨⟨d + 1, f + d + 2⟩, ?_⟩
  show ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 1, d + 3, f + 2⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (d + 1) + 1, (d + 1) + 3, (f + d + 2) + 2⟩
  rw [show (d + 1) + 1 = d + 2 from by ring,
      show (d + 1) + 3 = d + 4 from by ring,
      show (f + d + 2) + 2 = f + d + 4 from by ring]
  exact main_trans d f

end Sz22_2003_unofficial_1322
