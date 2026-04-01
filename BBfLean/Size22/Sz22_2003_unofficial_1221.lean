import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1221: [5/6, 539/2, 52/35, 9/13, 5/11]

Vector representation:
```
-1 -1  1  0  0  0
-1  0  0  2  1  0
 2  0 -1 -1  0  1
 0  2  0  0  0 -1
 0  0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1221

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+2, e+1, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R4 chain: drain f into b
theorem f_to_b : ∀ k b d e, ⟨0, b, 0, d, e, k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

-- R1R1R3 chain: (2, b+2k, c, d+k, e, f) →* (2, b, c+k, d, e, f+k)
theorem r1r1r3_chain : ∀ k b c d e f, ⟨2, b + 2 * k, c, d + k, e, f⟩ [fm]⊢* ⟨2, b, c + k, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · simp; exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e f)
    rw [show b + 2 = (b + 1) + 1 from by ring]
    step fm
    step fm
    rw [show c + k + 1 = c + (k + 1) from by ring]
    step fm
    ring_nf; finish

-- R2R2R3 chain: (2, 0, c+k, d, e, f) →* (2, 0, c, d+3*k, e+2*k, f+k)
theorem r2r2r3_chain : ∀ k c d e f, ⟨2, 0, c + k, d, e, f⟩ [fm]⊢* ⟨2, 0, c, d + 3 * k, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 3) (e + 2) (f + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, d+f+1, e+1, f) →⁺ (0, 0, 0, (d+f+2)+(2*f+1)+1, (e+2*f+1)+1, 2*f+1)
theorem main_trans (d e f : ℕ) :
    ⟨(0 : ℕ), 0, 0, d + f + 1, e + 1, f⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, d + 3 * f + 4, e + 2 * f + 2, 2 * f + 1⟩ := by
  -- Phase 1: first R4 step for ⊢⁺ (need f ≥ 1 case; handle f=0 separately)
  rcases f with _ | f
  · -- f = 0: (0, 0, 0, d+1, e+1, 0)
    -- R5: e+1 ≥ 1
    step fm
    -- (0, 0, 1, d+1, e, 0)
    -- R3: c=1, d+1 ≥ 1
    step fm
    -- (2, 0, 0, d, e, 1)
    -- R2, R2
    step fm
    step fm
    ring_nf; finish
  · -- f = f + 1 ≥ 1
    -- Phase 1: first R4 step for ⊢⁺
    step fm
    -- After first R4 step: (0, 2, 0, d+(f+1)+1, e+1, f). Goal is ⊢*
    rw [show d + (f + 1) + 1 = d + f + 2 from by ring]
    -- Remaining R4 steps
    apply stepStar_trans (f_to_b f 2 (d + f + 2) (e + 1))
    rw [show 2 + 2 * f = 2 * f + 2 from by ring]
    -- State: (0, 2f+2, 0, d+f+2, e+1, 0)
    -- Phase 2: R5
    step fm
    -- State: (0, 2f+2, 1, d+f+2, e, 0)
    -- Phase 3: R3
    rw [show d + f + 2 = (d + f + 1) + 1 from by ring]
    step fm
    -- State: (2, 2f+2, 0, d+f+1, e, 1)
    -- Phase 4: R1R1R3 chain (f+1 rounds)
    rw [show 2 * f + 2 = 0 + 2 * (f + 1) from by ring,
        show d + f + 1 = d + (f + 1) from by ring]
    apply stepStar_trans (r1r1r3_chain (f + 1) 0 0 d e 1)
    rw [show 0 + (f + 1) = f + 1 from by ring,
        show 1 + (f + 1) = f + 2 from by ring]
    -- State: (2, 0, f+1, d, e, f+2)
    -- Phase 5: R2R2R3 chain (f+1 rounds)
    rw [show (f + 1 : ℕ) = 0 + (f + 1) from by ring]
    apply stepStar_trans (r2r2r3_chain (f + 1) 0 d e (f + 2))
    -- State: (2, 0, 0, d+3(f+1), e+2(f+1), f+2+(f+1))
    -- Phase 6: R2, R2
    step fm
    step fm
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 10, 5, 3⟩)
  · execute fm 16
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨d, e, f⟩ ↦ ⟨0, 0, 0, d + f + 1, e + 1, f⟩) ⟨6, 4, 3⟩
  intro ⟨d, e, f⟩
  refine ⟨⟨d + f + 2, e + 2 * f + 1, 2 * f + 1⟩, ?_⟩
  show ⟨(0 : ℕ), 0, 0, d + f + 1, e + 1, f⟩ [fm]⊢⁺
    ⟨0, 0, 0, (d + f + 2) + (2 * f + 1) + 1, (e + 2 * f + 1) + 1, 2 * f + 1⟩
  rw [show (d + f + 2) + (2 * f + 1) + 1 = d + 3 * f + 4 from by ring,
      show (e + 2 * f + 1) + 1 = e + 2 * f + 2 from by ring]
  exact main_trans d e f

end Sz22_2003_unofficial_1221
