import BBfLean.FM

/-!
# sz22_2003_unofficial #561: [315/2, 2/55, 1/5, 121/3, 1/77, 5/11]

Vector representation:
```
-1  2  1  1  0
 1  0 -1  0 -1
 0  0 -1  0  0
 0 -1  0  0  2
 0  0  0 -1 -1
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_561

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R1/R2 interleaving: each round does R1 then R2, consuming one e
theorem r1r2_chain : ⟨1, b, 0, d, e+k⟩ [fm]⊢* ⟨1, b+2*k, 0, d+k, e⟩ := by
  have many_step : ∀ k b d, ⟨1, b, 0, d, e+k⟩ [fm]⊢* ⟨1, b+2*k, 0, d+k, e⟩ := by
    intro k; induction' k with k h <;> intro b d
    · exists 0
    rw [show e + (k + 1) = (e + k) + 1 from by omega]
    step fm; step fm
    apply stepStar_trans (h _ _)
    rw [show b + 2 + 2 * k = b + 2 * (k + 1) from by omega,
        show d + 1 + k = d + (k + 1) from by omega]
    finish
  exact many_step k b d

-- R4 repeated: convert b to e
theorem b_to_e : ⟨0, b+k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e+2*k⟩ := by
  have many_step : ∀ k b e, ⟨0, b+k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e+2*k⟩ := by
    intro k; induction' k with k h <;> intro b e
    · exists 0
    rw [show b + (k + 1) = (b + k) + 1 from by omega]
    step fm
    apply stepStar_trans (h _ _)
    rw [show e + 2 + 2 * k = e + 2 * (k + 1) from by omega]
    finish
  exact many_step k b e

-- R5 repeated: annihilate d and e
theorem de_annihilate : ⟨0, 0, 0, d+k, e+k⟩ [fm]⊢* ⟨0, 0, 0, d, e⟩ := by
  have many_step : ∀ k d e, ⟨0, 0, 0, d+k, e+k⟩ [fm]⊢* ⟨0, 0, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro d e
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by omega,
        show e + (k + 1) = (e + k) + 1 from by omega]
    step fm
    apply stepStar_trans (h _ _)
    finish
  exact many_step k d e

-- Main transition: (1, 0, 0, 0, n+1) →⁺ (1, 0, 0, 0, 3*n+4)
theorem main_trans : ⟨1, 0, 0, 0, n+1⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 3*n+4⟩ := by
  -- Phase 1: R1/R2 chain (n+1 rounds)
  rw [show (n : ℕ) + 1 = 0 + (n + 1) from by omega]
  apply stepStar_stepPlus_stepPlus (r1r2_chain (b := 0) (d := 0) (e := 0) (k := n + 1))
  simp only [Nat.zero_add]
  -- Phase 2: R1 + R3
  step fm; step fm
  -- Phase 3: R4 chain
  rw [show 2 * (n + 1) + 2 = 0 + (2 * n + 4) from by omega]
  apply stepStar_trans (b_to_e (b := 0) (d := n + 2) (e := 0) (k := 2 * n + 4))
  simp only [Nat.zero_add]
  -- Phase 4: R5 chain
  rw [show (n : ℕ) + 2 = 0 + (n + 2) from by omega,
      show 2 * (2 * n + 4) = (3 * n + 6) + (n + 2) from by omega]
  apply stepStar_trans (de_annihilate (d := 0) (e := 3 * n + 6) (k := n + 2))
  -- Phase 5: R6
  rw [show 3 * n + 6 = (3 * n + 5) + 1 from by omega]
  step fm
  -- Phase 6: R2
  rw [show 3 * n + 5 = (3 * n + 4) + 1 from by omega]
  step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, 0, n + 1⟩) 0
  intro n; exact ⟨3 * n + 3, main_trans⟩

end Sz22_2003_unofficial_561
