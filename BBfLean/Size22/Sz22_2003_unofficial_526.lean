import BBfLean.FM

/-!
# sz22_2003_unofficial #526: [28/15, 33/7, 1/3, 25/2, 1/55, 3/5]

Vector representation:
```
 2 -1 -1  1  0
 0  1  0 -1  1
 0 -1  0  0  0
-1  0  2  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_526

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1+R2 chain + R3: (a, 1, k+1, 0, e) does k+1 rounds of R1,R2 then R3
theorem r1r2_chain : ∀ k, ∀ a e, ⟨a, 1, k + 1, 0, e⟩ [fm]⊢* ⟨a + 2*k + 2, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; step fm; step fm; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih _ _)
    show (a + 2 + 2 * k + 2, 0, 0, 0, e + 1 + k + 1) [fm]⊢*
         (a + 2 * (k + 1) + 2, 0, 0, 0, e + (k + 1) + 1)
    rw [show a + 2 + 2 * k + 2 = a + 2 * (k + 1) + 2 from by omega,
        show e + 1 + k + 1 = e + (k + 1) + 1 from by omega]
    finish

-- R4 chain: convert a to c
theorem r4_chain : ∀ k, ∀ c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2*k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  have : c + 2 + 2 * k = c + 2 * (k + 1) := by omega
  rw [this]; finish

-- R5 chain: annihilate c and e
theorem r5_chain : ∀ k, ∀ c, ⟨0, 0, c + k, 0, k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by omega]
  step fm
  exact ih _

-- Main transition: (0, 0, c+2, 0, 0) →⁺ (0, 0, 3*c+3, 0, 0)
theorem main_trans : ⟨0, 0, c + 2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3*c + 3, 0, 0⟩ := by
  -- R6: (0, 0, c+2, 0, 0) -> (0, 1, c+1, 0, 0)
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- R1/R2 chain + R3: ->* (2*c+2, 0, 0, 0, c+1)
  apply stepStar_trans (r1r2_chain c 0 0)
  simp only [Nat.zero_add]
  -- R4 chain: ->* (0, 0, 4*c+4, 0, c+1)
  apply stepStar_trans (r4_chain (2*c + 2) 0 (c + 1))
  -- R5 chain: ->* (0, 0, 3*c+3, 0, 0)
  have : 0 + 2 * (2 * c + 2) = 3 * c + 3 + (c + 1) := by omega
  rw [this]
  exact r5_chain (c + 1) (3 * c + 3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 0, 0⟩) 0
  intro n; exists 3*n + 1; exact main_trans

end Sz22_2003_unofficial_526
