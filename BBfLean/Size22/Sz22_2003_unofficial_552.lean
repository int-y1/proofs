import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #552: [297/35, 5/6, 4/5, 7/11, 55/2]

Vector representation:
```
 0  3 -1 -1  1
-1 -1  1  0  0
 2  0 -1  0  0
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_552

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 repeated: transfer e to d
theorem e_to_d : ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  have many_step : ∀ k d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
    intro k; induction' k with k h <;> intro d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k d

-- R3 repeated: drain c to a
theorem c_to_a : ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
  have many_step : ∀ k a, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
    intro k; induction' k with k h <;> intro a
    · exists 0
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k a

-- (R2,R1) interleave chain: used after R5+R1
-- From (a+k, b+1, 0, k, e) reach (a, b+2*k+1, 0, 0, e+k)
theorem r2r1_chain : ⟨a + k, b + 1, 0, k, e⟩ [fm]⊢* ⟨a, b + 2 * k + 1, 0, 0, e + k⟩ := by
  have many_step : ∀ k a b e, ⟨a + k, b + 1, 0, k, e⟩ [fm]⊢* ⟨a, b + 2 * k + 1, 0, 0, e + k⟩ := by
    intro k; induction' k with k h <;> intro a b e
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (h a (b + 2) (e + 1))
    ring_nf; finish
  exact many_step k a b e

-- Drain: (A, B, C, 0, E) ->* (A+B+2*C, 0, 0, 0, E)
-- Proved by strong induction on 2*B + C.
-- Condition: if B >= 1 then A + C >= 1 (to avoid R4 firing).
theorem drain : ∀ S, ∀ A B C, 2 * B + C = S → (B = 0 ∨ A + C ≥ 1) →
    ⟨A, B, C, 0, e⟩ [fm]⊢* ⟨A + B + 2 * C, 0, 0, 0, e⟩ := by
  intro S; induction' S using Nat.strongRecOn with S ih
  intro A B C hS hcond
  rcases B with _ | B
  · -- B = 0: R3 chain drains c
    rcases C with _ | C
    · exists 0
    step fm
    apply stepStar_trans (ih C (by omega) (A + 2) 0 C (by omega) (by omega))
    ring_nf; finish
  · -- B + 1 >= 1
    have hAC : A + C ≥ 1 := by omega
    rcases A with _ | A
    · -- A = 0: C >= 1, R3 fires
      rcases C with _ | C
      · omega
      step fm
      apply stepStar_trans (ih (2 * (B + 1) + C) (by omega) 2 (B + 1) C (by omega) (by omega))
      ring_nf; finish
    · -- A + 1 >= 1, B + 1 >= 1: R2 fires
      step fm
      apply stepStar_trans (ih (2 * B + (C + 1)) (by omega) A B (C + 1) (by omega) (by omega))
      ring_nf; finish

-- Main transition: (a, 0, 0, 0, e+1) ->+ (a+e+2, 0, 0, 0, e+2)
-- Phases: R4 transfer -> R5 -> R1 -> R2R1 chain -> drain
theorem main_trans (ha : a ≥ e + 2) :
    ⟨a, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨a + e + 2, 0, 0, 0, e + 2⟩ := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + (e + 2) := ⟨a - (e + 2), by omega⟩
  -- Phase 1: R4 transfer: ->* (a'+e+2, 0, 0, e+1, 0)
  rw [show e + 1 = 0 + (e + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_d (a := a' + (e + 2)) (d := 0) (e := 0) (k := e + 1))
  simp only [Nat.zero_add]
  -- Phase 2+3: R5 then R1 (gives us ⊢⁺ via step)
  rw [show a' + (e + 2) = (a' + e + 1) + 1 from by ring]
  step fm; step fm
  -- Goal: (a'+e+1, 3, 0, e, 2) [fm]⊢* (a'+e+1+1+e+2, 0, 0, 0, e+2)
  -- Phase 4: R2R1 chain
  rw [show a' + e + 1 = (a' + 1) + e from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r2r1_chain (a := a' + 1) (b := 2) (k := e) (e := 2))
  -- After chain: (a'+1, 2+2*e+1, 0, 0, 2+e)
  -- Phase 5: Drain
  have hdrain := drain (e := 2 + e) (2 * (2 + 2 * e + 1)) (a' + 1) (2 + 2 * e + 1) 0
    (by ring) (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at hdrain
  apply stepStar_trans hdrain
  ring_nf; finish

-- Nonhalting theorem
theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) ->* (2, 0, 0, 0, 1) in 2 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 2)
  -- Use progress_nonhalt_simple with A = ℕ × ℕ
  -- C(a, e) = (a, 0, 0, 0, e + 1) with a >= e + 2
  -- Initial: (2, 0, 0, 0, 1) = C(2, 0)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e + 1⟩ ∧ a ≥ e + 2)
  · intro c ⟨a, e, hq, ha⟩
    subst hq
    exact ⟨⟨a + e + 2, 0, 0, 0, e + 2⟩, ⟨a + e + 2, e + 1, rfl, by omega⟩, main_trans ha⟩
  · exact ⟨2, 0, rfl, by omega⟩

end Sz22_2003_unofficial_552
