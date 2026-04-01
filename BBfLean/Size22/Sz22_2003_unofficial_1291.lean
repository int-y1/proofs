import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1291: [63/10, 11/2, 4/33, 5/7, 28/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  1
 2 -1  0  0 -1
 0  0  1 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1291

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer d to c
theorem d_to_c : ∀ k, ∀ c d e, ⟨(0 : ℕ), (0 : ℕ), c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih c (d + 1) e)
    step fm
    rw [show c + k + 1 = c + (k + 1) from by ring]
    finish

-- R3,R2,R2 drain chain
theorem drain : ∀ k, ∀ d e, ⟨(0 : ℕ), k, (0 : ℕ), d, e + 1⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    step fm
    step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- Combined chain and drain by strong induction on c
-- From (2, b, c, d, e+c) to (0, 0, 0, d+c, e+b+2c+2)
theorem chain_drain : ∀ c, ∀ b d e, ⟨(2 : ℕ), b, c, d, e + c⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), 0, d + c, e + b + 2 * c + 2⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih
  rcases c with _ | _ | c
  · -- c = 0: (2, b, 0, d, e) R2 R2 -> (0, b, 0, d, e+2), then drain b
    intro b d e; simp
    step fm; step fm
    -- State: (0, b, 0, d, e+2)
    -- Need to show: (0, b, 0, d, e+2) ->* (0, 0, 0, d, e+b+2)
    rw [show e + 2 = (e + 1) + 1 from by ring,
        show e + b + 2 = (e + 1) + b + 1 from by ring]
    exact drain b d (e + 1)
  · -- c = 1: (2, b, 1, d, e+1) R1 R2 -> (0, b+2, 0, d+1, e+2), then drain b+2
    intro b d e; simp
    step fm; step fm
    -- State: (0, b+2, 0, d+1, e+2)
    rw [show e + 1 + 1 = (e + 1) + 1 from by ring,
        show e + b + 4 = (e + 1) + (b + 2) + 1 from by ring]
    exact drain (b + 2) (d + 1) (e + 1)
  · -- c + 2: R1 R1 R3 then apply ih c
    intro b d e
    rw [show e + (c + 2) = (e + 1) + c + 1 from by ring,
        show c + 2 = c + 1 + 1 from by ring]
    step fm
    step fm
    step fm
    -- State after R1 R1 R3: (2, b+3, c, d+2, (e+1)+c)
    -- Need to rewrite to match ih
    apply stepStar_trans (ih c (by omega) (b + 3) (d + 2) (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, d+1, e+d+2) ->+ (0, 0, 0, d+2, e+2*d+4)
theorem main_transition (d e : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, d + 1, e + d + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, d + 2, e + 2 * d + 4⟩ := by
  -- Phase 1: R4 chain to move d+1 to c
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (d + 1) 0 0 (e + d + 2))
  rw [show 0 + (d + 1) = d + 1 from by ring]
  -- State: (0, 0, d+1, 0, e+d+2)
  -- Phase 2: R5 step
  rw [show e + d + 2 = (e + d + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 0, d + 1, 0, (e + d + 1) + 1⟩ : Q) [fm]⊢ ⟨2, 0, d + 1, 1, e + d + 1⟩)
  -- State: (2, 0, d+1, 1, e+d+1)
  -- Phase 3: chain + drain
  rw [show e + d + 1 = e + (d + 1) from by ring]
  apply stepStar_trans (chain_drain (d + 1) 0 1 e)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d + 1, e + d + 2⟩) ⟨0, 0⟩
  intro ⟨d, e⟩
  exists ⟨d + 1, e + d + 1⟩
  show ⟨(0 : ℕ), (0 : ℕ), 0, d + 1, e + d + 2⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), 0, (d + 1) + 1, (e + d + 1) + (d + 1) + 2⟩
  rw [show (d + 1) + 1 = d + 2 from by ring,
      show (e + d + 1) + (d + 1) + 2 = e + 2 * d + 4 from by ring]
  exact main_transition d e

end Sz22_2003_unofficial_1291
