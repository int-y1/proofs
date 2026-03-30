import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #760: [35/6, 4/55, 847/2, 3/7, 5/33]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 0 -1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_760

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: (0, b, 0, k, e) ⊢* (0, b+k, 0, 0, e)
theorem r4_chain : ∀ k b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- (R1,R1,R2) chain: (2, 2*k+1, c, d, e+k) ⊢* (2, 1, c+k, d+2*k, e)
theorem r1r1r2_chain : ∀ k c d e,
    ⟨2, 2 * k + 1, c, d, e + k⟩ [fm]⊢* ⟨2, 1, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

-- R2 drain: (a, 0, k, d, f+k) ⊢* (a+2*k, 0, 0, d, f)
theorem r2_drain : ∀ k a d f,
    ⟨a, 0, k, d, f + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, f⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d f)
    ring_nf; finish

-- R3 chain: (k, 0, 0, d, e) ⊢* (0, 0, 0, d+k, e+2*k)
theorem r3_chain : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1) (e + 2))
    ring_nf; finish

-- Middle phase: (0, 2*d+2, 0, 0, e+2*d+3) ⊢* (2*d+3, 0, 0, 2*d+1, e)
theorem middle_phase (d e : ℕ) :
    ⟨0, 2 * d + 2, 0, 0, e + 2 * d + 3⟩ [fm]⊢* ⟨2 * d + 3, 0, 0, 2 * d + 1, e⟩ := by
  -- R5: need b+1 and e+1 patterns
  rw [show 2 * d + 2 = (2 * d + 1) + 1 from by ring,
      show e + 2 * d + 3 = (e + 2 * d + 2) + 1 from by ring]
  step fm
  -- After R5: (0, 2*d+1, 1, 0, e+2*d+2)
  -- R2: need c+1 and e+1 patterns. State has c=0+1=1 and e=e+2*d+2
  rw [show e + 2 * d + 2 = (e + 2 * d + 1) + 1 from by ring]
  step fm
  -- After R2: (2, 2*d+1, 0, 0, e+2*d+1)
  -- (R1,R1,R2)^d chain
  rw [show e + 2 * d + 1 = (e + d + 1) + d from by ring]
  apply stepStar_trans (r1r1r2_chain d 0 0 (e + d + 1))
  -- After chain: (2, 1, d, 2*d, e+d+1)
  rw [show (0 + d : ℕ) = d from by ring,
      show (0 + 2 * d : ℕ) = 2 * d from by ring]
  -- R1: need a+1 and b+1
  step fm
  -- After R1: (1, 0, d+1, 2*d+1, e+d+1)
  -- R2 drain: need (1, 0, d+1, 2*d+1, e+(d+1))
  rw [show e + d + 1 = e + (d + 1) from by ring]
  apply stepStar_trans (r2_drain (d + 1) 1 (2 * d + 1) e)
  ring_nf; finish

-- Main transition
theorem main_trans (d f : ℕ) :
    ⟨0, 0, 0, 2 * d + 2, f + 2 * d + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * d + 4, f + 4 * d + 6⟩ := by
  -- Phase 1: R4 chain (at least one R4 step to start the plus)
  rw [show 2 * d + 2 = (2 * d + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, (2 * d + 1) + 1, f + 2 * d + 3⟩ = some ⟨0, 0 + 1, 0, 2 * d + 1, f + 2 * d + 3⟩
    simp [fm]
  rw [show (0 + 1 : ℕ) = 1 from rfl]
  apply stepStar_trans (r4_chain (2 * d + 1) 1 (f + 2 * d + 3))
  -- (0, 2*d+2, 0, 0, f+2*d+3)
  rw [show 1 + (2 * d + 1) = 2 * d + 2 from by ring]
  -- Middle phase
  apply stepStar_trans (middle_phase d f)
  -- (2*d+3, 0, 0, 2*d+1, f)
  -- R3 chain
  apply stepStar_trans (r3_chain (2 * d + 3) (2 * d + 1) f)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 4⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, f⟩ ↦ ⟨0, 0, 0, 2 * d + 2, f + 2 * d + 3⟩) ⟨0, 1⟩
  intro ⟨d, f⟩
  refine ⟨⟨2 * d + 1, f + 1⟩, ?_⟩
  show ⟨0, 0, 0, 2 * d + 2, f + 2 * d + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * (2 * d + 1) + 2, (f + 1) + 2 * (2 * d + 1) + 3⟩
  have h := main_trans d f
  convert h using 2
  ring_nf

end Sz22_2003_unofficial_760
