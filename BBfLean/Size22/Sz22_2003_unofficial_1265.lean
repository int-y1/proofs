import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1265: [5/6, 9/385, 28/5, 121/2, 5/11]

Vector representation:
```
-1 -1  1  0  0
 0  2 -1 -1 -1
 2  0 -1  1  0
-1  0  0  0  2
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1265

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 drain: (a+k, 0, 0, d, e) ->* (a, 0, 0, d, e+2*k)
theorem r4_drain : ∀ k a d e, ⟨a + k, (0 : ℕ), (0 : ℕ), d, e⟩ [fm]⊢* ⟨a, (0 : ℕ), (0 : ℕ), d, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro a d e; simp; exists 0
  · intro a d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

-- R5+R2 round: (0, b, 0, D+1, E+2) ->* (0, b+2, 0, D, E)
theorem r5r2_round (b D E : ℕ) :
    ⟨(0 : ℕ), b, (0 : ℕ), D + 1, E + 2⟩ [fm]⊢* ⟨(0 : ℕ), b + 2, (0 : ℕ), D, E⟩ := by
  execute fm 2

-- R5+R2 chain: k rounds
theorem r5r2_chain : ∀ k, ∀ b D E, ⟨(0 : ℕ), b, (0 : ℕ), D + k, E + 2 * k⟩ [fm]⊢* ⟨(0 : ℕ), b + 2 * k, (0 : ℕ), D, E⟩ := by
  intro k; induction' k with k ih
  · intro b D E; simp; exists 0
  · intro b D E
    rw [show D + (k + 1) = (D + 1) + k from by ring,
        show E + 2 * (k + 1) = (E + 2) + 2 * k from by ring]
    apply stepStar_trans (ih b (D + 1) (E + 2))
    exact r5r2_round (b + 2 * k) D E

-- Middle 8 steps: (0, b+2, 0, 0, 2) ->* (0, b, 2, 1, 0)
theorem middle_steps (b : ℕ) :
    ⟨(0 : ℕ), b + 2, (0 : ℕ), (0 : ℕ), 2⟩ [fm]⊢* ⟨(0 : ℕ), b, 2, 1, (0 : ℕ)⟩ := by
  execute fm 8

-- R3+R1+R1 round: (0, b+2, c+1, D+1, 0) ->* (0, b, c+2, D+2, 0)
theorem r3r1r1_round (b c D : ℕ) :
    ⟨(0 : ℕ), b + 2, c + 1, D + 1, (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 2, D + 2, (0 : ℕ)⟩ := by
  execute fm 3

-- R3+R1+R1 chain: k rounds
theorem r3r1r1_chain : ∀ k, ∀ b c D, ⟨(0 : ℕ), b + 2 * k, c + 1, D + 1, (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k + 1, D + k + 1, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih
  · intro b c D; simp; exists 0
  · intro b c D
    rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (b + 2) c D)
    rw [show c + k + 1 = (c + k) + 1 from by ring,
        show D + k + 1 = (D + k) + 1 from by ring]
    apply stepStar_trans (r3r1r1_round b (c + k) (D + k))
    ring_nf; finish

-- R3 drain: (a, 0, k+1, D, 0) ->* (a+2*(k+1), 0, 0, D+k+1, 0)
theorem r3_drain : ∀ k, ∀ a D, ⟨a, (0 : ℕ), k + 1, D, (0 : ℕ)⟩ [fm]⊢* ⟨a + 2 * (k + 1), (0 : ℕ), (0 : ℕ), D + k + 1, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih
  · intro a D; step fm; ring_nf; finish
  · intro a D
    step fm
    apply stepStar_trans (ih (a + 2) (D + 1))
    ring_nf; finish

-- Combined R4+R5+R2: (2*d+2, 0, 0, 2*d+1, 0) ->* (0, 4*d+2, 0, 0, 2)
theorem phase12 (d : ℕ) :
    ⟨2 * d + 2, (0 : ℕ), (0 : ℕ), 2 * d + 1, (0 : ℕ)⟩ [fm]⊢*
    ⟨(0 : ℕ), 4 * d + 2, (0 : ℕ), (0 : ℕ), 2⟩ := by
  -- R4 drain: (2*d+2, 0, 0, 2*d+1, 0) ->* (0, 0, 0, 2*d+1, 4*d+4)
  apply stepStar_trans
  · rw [show 2 * d + 2 = 0 + (2 * d + 2) from by ring,
        show (0 : ℕ) = 0 + 2 * 0 from by ring]
    exact r4_drain (2 * d + 2) 0 (2 * d + 1) 0
  rw [show 0 + 2 * (2 * d + 2) = 4 * d + 4 from by ring]
  -- R5+R2 chain: 2*d+1 rounds
  -- (0, 0, 0, 2*d+1, 4*d+4) = (0, 0, 0, 0+(2*d+1), 2+2*(2*d+1))
  apply stepStar_trans
  · rw [show 2 * d + 1 = 0 + (2 * d + 1) from by ring,
        show 4 * d + 4 = 2 + 2 * (2 * d + 1) from by ring]
    exact r5r2_chain (2 * d + 1) 0 0 2
  rw [show 0 + 2 * (2 * d + 1) = 4 * d + 2 from by ring]
  finish

-- Main transition
theorem main_transition (d : ℕ) :
    ⟨2 * d + 2, (0 : ℕ), (0 : ℕ), 2 * d + 1, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨4 * d + 4, (0 : ℕ), (0 : ℕ), 4 * d + 3, (0 : ℕ)⟩ := by
  -- Phase 1-2 via ⊢*
  apply stepStar_stepPlus_stepPlus (phase12 d)
  -- State: (0, 4*d+2, 0, 0, 2)
  -- Middle steps: 8 steps (⊢*), but we need ⊢⁺ so take first step explicitly
  -- (0, 4*d+2, 0, 0, 2) = (0, 4*d+2, 0, 0, 1+1) -> R5 -> (0, 4*d+2, 1, 0, 1)
  rw [show 4 * d + 2 = (4 * d + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (show (⟨(0 : ℕ), (4 * d + 1) + 1, (0 : ℕ), (0 : ℕ), 2⟩ : Q) [fm]⊢
         ⟨(0 : ℕ), (4 * d + 1) + 1, 1, (0 : ℕ), 1⟩ from by simp [fm])
  -- (0, 4*d+2, 1, 0, 1) -> R3 -> (2, 4*d+2, 0, 1, 1) -> R1 -> (1, 4*d+1, 1, 1, 1) -> R1 -> (0, 4*d, 2, 1, 1)
  -- -> R2 -> (0, 4*d+2, 1, 0, 0) -> R3 -> (2, 4*d+2, 0, 1, 0) -> R1 -> (1, 4*d+1, 1, 1, 0) -> R1 -> (0, 4*d, 2, 1, 0)
  -- That's 7 more steps from middle_steps (originally 8). Let me just execute.
  apply stepStar_trans
  · show (⟨(0 : ℕ), (4 * d + 1) + 1, 1, (0 : ℕ), 1⟩ : Q) [fm]⊢*
         ⟨(0 : ℕ), 4 * d, 2, 1, (0 : ℕ)⟩
    execute fm 7
  -- State: (0, 4*d, 2, 1, 0)
  -- Phase 4: R3+R1+R1 chain: 2*d rounds
  rw [show 4 * d = 0 + 2 * (2 * d) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain (2 * d) 0 1 0)
  rw [show 1 + 2 * d + 1 = 2 * d + 2 from by ring,
      show 0 + 2 * d + 1 = 2 * d + 1 from by ring]
  -- State: (0, 0, 2*d+2, 2*d+1, 0)
  -- Phase 5: R3 drain
  rw [show 2 * d + 2 = (2 * d + 1) + 1 from by ring]
  apply stepStar_trans (r3_drain (2 * d + 1) 0 (2 * d + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 3, 0⟩) (by execute fm 21)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨2 * (d + 1) + 2, 0, 0, 2 * (d + 1) + 1, 0⟩) 0
  intro d
  exists 2 * d + 2
  show ⟨2 * (d + 1) + 2, (0 : ℕ), (0 : ℕ), 2 * (d + 1) + 1, (0 : ℕ)⟩ [fm]⊢⁺
       ⟨2 * (2 * d + 2 + 1) + 2, (0 : ℕ), (0 : ℕ), 2 * (2 * d + 2 + 1) + 1, (0 : ℕ)⟩
  have h := main_transition (d + 1)
  rw [show 4 * (d + 1) + 4 = 2 * (2 * d + 2 + 1) + 2 from by ring,
      show 4 * (d + 1) + 3 = 2 * (2 * d + 2 + 1) + 1 from by ring] at h
  exact h

end Sz22_2003_unofficial_1265
