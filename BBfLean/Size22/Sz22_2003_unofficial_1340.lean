import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1340: [63/10, 2/33, 9317/2, 5/7, 2/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  1  3
 0  0  1 -1  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1340

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R3 drain: repeated R3 with b=0, c=0.
theorem r3_drain : ∀ j, ∀ d e, ⟨j, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + j, e + 3 * j⟩ := by
  intro j; induction' j with j ih <;> intro d e
  · exists 0
  · rw [show d + (j + 1) = (d + 1) + j from by ring,
        show e + 3 * (j + 1) = (e + 3) + 3 * j from by ring]
    step fm
    exact ih (d + 1) (e + 3)

-- R1/R2 interleaved chain.
theorem r1r2_chain : ∀ k, ∀ b d e, ⟨1, b, k + 1, d, e + k⟩ [fm]⊢* ⟨0, b + k + 2, 0, d + k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · step fm; ring_nf; finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm
    rw [show e + k + 1 = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) (d + 1) e)
    ring_nf; finish

-- Master drain: drain a+1 and b via R3/R2 interleaving with c=0.
theorem master_drain : ∀ b, ∀ a d e, ⟨a + 1, b, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + a + b + 1, e + 3 * a + 2 * b + 3⟩ := by
  intro b; induction' b with b ih <;> intro a d e
  · -- b = 0: pure R3 drain
    rw [show d + a + 0 + 1 = d + (a + 1) from by ring,
        show e + 3 * a + 2 * 0 + 3 = e + 3 * (a + 1) from by ring]
    exact r3_drain (a + 1) d e
  · -- b + 1: case split on e
    rcases e with _ | e
    · -- e = 0: R3 then R2, then IH
      step fm
      rw [show (3 : ℕ) = 2 + 1 from rfl]
      step fm
      rw [show d + a + (b + 1) + 1 = (d + 1) + (a + 0) + b + 1 from by ring,
          show 0 + 3 * a + 2 * (b + 1) + 3 = 2 + 3 * (a + 0) + 2 * b + 3 from by ring,
          show a + 0 = a from by ring]
      exact ih a (d + 1) 2
    · -- e = e + 1: R2 then IH
      rw [show a + 1 = (a + 1 + 1) - 1 from by omega]
      step fm
      rw [show d + a + (b + 1) + 1 = d + (a + 1) + b + 1 from by ring,
          show e + 1 + 3 * a + 2 * (b + 1) + 3 = e + 3 * (a + 1) + 2 * b + 3 from by ring]
      exact ih (a + 1) d e

-- R4 drain: transfer d to c.
theorem d_to_c : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- Phases 2-5 combined as a star transition.
theorem phases_2_to_5 (c g : ℕ) :
    ⟨1, 0, c + 1, 0, g + 2 + c⟩ [fm]⊢* ⟨0, 0, 2 * c + 3, 0, 2 * c + g + 6⟩ := by
  -- Phase 2: R1/R2 chain
  rw [show g + 2 + c = (g + 2) + c from by ring]
  apply stepStar_trans (r1r2_chain c 0 0 (g + 2))
  -- Now at (0, c + 2, 0, c + 1, g + 2)
  -- After r1r2_chain: (0, 0+c+2, 0, 0+c+1, g+2)
  -- Normalize and do R2 step
  rw [show (0 : ℕ) + c + 2 = (c + 1) + 1 from by ring,
      show (0 : ℕ) + c + 1 = c + 1 from by ring,
      show (g + 2 : ℕ) = (g + 1) + 1 from by ring]
  step fm
  -- After R2: (0+1, c+1, 0, c+1, g+1) = (1, c+1, 0, c+1, g+1)
  -- Phase 4: master drain with a=0, b=c+1, d=c+1, e=g+1
  apply stepStar_trans (master_drain (c + 1) 0 (c + 1) (g + 1))
  -- Result: (0, 0, 0, c+1+0+(c+1)+1, g+1+3*0+2*(c+1)+3)
  -- Phase 5: R4 drain
  rw [show c + 1 + 0 + (c + 1) + 1 = 0 + (2 * c + 3) from by ring,
      show g + 1 + 3 * 0 + 2 * (c + 1) + 3 = 2 * c + g + 6 from by ring]
  apply stepStar_trans (d_to_c (2 * c + 3) 0 0 (2 * c + g + 6))
  ring_nf; finish

-- Main transition.
theorem main_trans (c g : ℕ) :
    ⟨0, 0, c + 1, 0, c + g + 3⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 3, 0, 2 * c + g + 6⟩ := by
  -- Phase 1: R5
  rw [show c + g + 3 = (g + 2 + c) + 1 from by ring]
  step fm
  exact phases_2_to_5 c g

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 3⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, g⟩ ↦ ⟨0, 0, c + 1, 0, c + g + 3⟩) ⟨0, 0⟩
  intro ⟨c, g⟩
  refine ⟨⟨2 * c + 2, g + 1⟩, ?_⟩
  show ⟨0, 0, c + 1, 0, c + g + 3⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 2 + 1, 0, 2 * c + 2 + (g + 1) + 3⟩
  rw [show 2 * c + 2 + 1 = 2 * c + 3 from by ring,
      show 2 * c + 2 + (g + 1) + 3 = 2 * c + g + 6 from by ring]
  exact main_trans c g

end Sz22_2003_unofficial_1340
