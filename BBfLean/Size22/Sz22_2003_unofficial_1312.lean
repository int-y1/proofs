import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1312: [63/10, 1331/2, 2/33, 5/7, 14/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  3
 1 -1  0  0 -1
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1312

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 chain: move d to c
theorem d_to_c : ∀ k c d e, ⟨(0 : ℕ), (0 : ℕ), c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih c (d + 1) e)
    step fm
    rw [show c + k + 1 = c + (k + 1) from by ring]
    finish

-- R1R3 chain: k rounds of (R1, R3)
-- (1, b, c+k, d, e+k) →* (1, b+k, c, d+k, e)
theorem r1r3_chain : ∀ k b c d e, ⟨(1 : ℕ), b, c + k, d, e + k⟩ [fm]⊢* ⟨(1 : ℕ), b + k, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R1
    step fm  -- R3
    apply stepStar_trans (ih (b + 1) c (d + 1) e)
    rw [show b + 1 + k = b + (k + 1) from by ring,
        show d + 1 + k = d + (k + 1) from by ring]
    finish

-- R3R2 chain: k rounds, each does R3 then R2
-- (0, k, 0, d, e+1) →* (0, 0, 0, d, e+2k+1)
theorem r3r2_chain : ∀ k d e, ⟨(0 : ℕ), k, (0 : ℕ), d, e + 1⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm  -- R3
    step fm  -- R2
    rw [show e + 3 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih d (e + 2))
    rw [show e + 2 + 2 * k + 1 = e + 2 * (k + 1) + 1 from by ring]
    finish

-- Combined phase: (0, 0, c, 0, c+1+s) →⁺ (0, 0, 0, c+1, 2*c+s+3)
-- Uses R5, then c R1R3 rounds, then R2, then c R3R2 rounds
-- Special case c=0: R5 + R2
theorem combined_phase : ∀ c s, ⟨(0 : ℕ), (0 : ℕ), c, 0, c + 1 + s⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 0, c + 1, 2 * c + s + 3⟩ := by
  intro c; induction' c with c ih <;> intro s
  · -- c = 0: R5 + R2
    rw [show (0 : ℕ) + 1 + s = s + 1 from by ring]
    step fm  -- R5: (1, 0, 0, 1, s)
    step fm  -- R2: (0, 0, 0, 1, s+3)
    rw [show s + 3 = 2 * 0 + s + 3 from by ring]
    finish
  · -- c+1: R5 + R1 + ih-style chain
    rw [show c + 1 + 1 + s = (c + 1 + s) + 1 from by ring]
    -- R5
    step fm
    -- State: (1, 0, c+1, 1, c+1+s)
    -- R1
    rw [show c + 1 = c + 1 from rfl]
    step fm
    -- State: (0, 2, c, 2, c+1+s) in Lean normal form
    -- R3
    rw [show c + 1 + s = (c + s) + 1 from by ring]
    step fm
    -- Goal state has form: (1, 1, 0+c, 2, 0+c+s)
    -- Need c (R1, R3) pairs: (1, 1, c, 2, c+s) → (1, c+1, 0, c+2, s)
    -- Goal: (1, 1, c, 2, c+s) ⊢* (0, 0, 0, c+1+1, 2*(c+1)+s+3)
    -- r1r3_chain c 1 0 2 s : (1, 1, 0+c, 2, s+c) ⊢* (1, 1+c, 0, 2+c, s)
    have h_r1r3 := r1r3_chain c 1 0 2 s
    rw [show (0 : ℕ) + c = c from by ring, show s + c = c + s from by ring] at h_r1r3
    apply stepStar_trans h_r1r3
    rw [show 1 + c = c + 1 from by ring,
        show 2 + c = c + 2 from by ring]
    -- State: (1, c+1, 0, c+2, s)
    -- R2 (a=1, c_reg=0)
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨1, c + 1, 0, c + 2, s⟩ : Q) [fm]⊢ ⟨0, c + 1, 0, c + 2, s + 3⟩))
    -- State: (0, c+1, 0, c+2, s+3)
    -- R3R2 chain (c+1 rounds)
    rw [show s + 3 = (s + 2) + 1 from by ring]
    apply stepStar_trans (r3r2_chain (c + 1) (c + 2) (s + 2))
    rw [show s + 2 + 2 * (c + 1) + 1 = 2 * (c + 1) + s + 3 from by ring]
    finish

-- Main transition composing R4 chain + combined phase
theorem main_trans (d s : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, d, d + 1 + s⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 0, d + 1, 2 * d + s + 3⟩ := by
  rcases d with _ | d
  · exact combined_phase 0 s
  · -- R4 chain: (0,0,0,d+1,d+2+s) → (0,0,d+1,0,d+2+s)
    apply stepStar_stepPlus_stepPlus
      (show ⟨(0 : ℕ), 0, 0, d + 1, d + 1 + 1 + s⟩ [fm]⊢*
            ⟨(0 : ℕ), 0, d + 1, 0, d + 1 + 1 + s⟩ by
        rw [show d + 1 = 0 + (d + 1) from by ring]; exact d_to_c (d + 1) 0 0 _)
    exact combined_phase (d + 1) s

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 3⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, s⟩ ↦ ⟨0, 0, 0, d, d + 1 + s⟩) ⟨0, 2⟩
  intro ⟨d, s⟩
  refine ⟨⟨d + 1, d + s + 1⟩, ?_⟩
  show ⟨(0 : ℕ), (0 : ℕ), 0, d, d + 1 + s⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, d + 1, (d + 1) + 1 + (d + s + 1)⟩
  rw [show (d + 1) + 1 + (d + s + 1) = 2 * d + s + 3 from by ring]
  exact main_trans d s

end Sz22_2003_unofficial_1312
