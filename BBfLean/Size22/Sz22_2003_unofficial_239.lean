import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #239: [11/105, 3/22, 20/3, 49/2, 33/7]

Vector representation:
```
 0 -1 -1 -1  1
-1  1  0  0 -1
 2 -1  1  0  0
-1  0  0  2  0
 0  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_239

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: convert a to d
theorem a_to_d : ∀ k c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  step fm
  apply stepStar_trans (ih c (d + 2))
  ring_nf; finish

-- R1+R5 drain: pairs reducing c and d, increasing e
theorem drain : ∀ k c d e, ⟨0, 0, c + k, d + 2 * k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih c d (e + 2))
  ring_nf; finish

-- Middle phase: 6 fixed steps
theorem middle_phase : ⟨0, 0, 0, 2, e + 1⟩ [fm]⊢* ⟨2, 0, 1, 0, e + 1⟩ := by
  execute fm 6

-- R3 chain: convert b to a and c
theorem r3_chain : ∀ k a b c, ⟨a, b + k, c, 0, 0⟩ [fm]⊢* ⟨a + 2 * k, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ b _)
  ring_nf; finish

-- R2, R2, R3 loop: each iteration consumes 2 from e, adds 1 to b and c
theorem r2r2r3_loop :
    ∀ k b c, ⟨2, b, c, 0, 2 * (k + 1)⟩ [fm]⊢* ⟨2, b + (k + 1), c + (k + 1), 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · step fm; step fm; step fm; finish
  rw [show 2 * (k + 1 + 1) = 2 * (k + 1) + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (b + 1) (c + 1))
  ring_nf; finish

-- Full conversion: (2, 0, 1, 0, 2*(k+1)) ->* (2*(k+2), 0, 2*(k+1)+1, 0, 0)
theorem convert_phase :
    ∀ k, ⟨2, 0, 1, 0, 2 * (k + 1)⟩ [fm]⊢* ⟨2 * (k + 2), 0, 2 * (k + 1) + 1, 0, 0⟩ := by
  intro k
  apply stepStar_trans (r2r2r3_loop k 0 1)
  rw [show (0 : ℕ) + (k + 1) = k + 1 from by ring,
      show (1 : ℕ) + (k + 1) = k + 2 from by ring]
  have h := r3_chain (k + 1) 2 0 (k + 2)
  rw [show (0 : ℕ) + (k + 1) = k + 1 from by ring] at h
  apply stepStar_trans h
  ring_nf; finish

-- Main cycle: f(n) = (2*(n+1), 0, 2*n+1, 0, 0) maps to f(2*n+1)
theorem main_cycle (n : ℕ) :
    ⟨2 * (n + 1), 0, 2 * n + 1, 0, 0⟩ [fm]⊢⁺ ⟨2 * (2 * n + 2), 0, 2 * (2 * n + 1) + 1, 0, 0⟩ := by
  -- First step via R4 to establish ⊢⁺
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
  step fm
  -- Now at (2*n+1, 0, 2*n+1, 2, 0), remaining a to convert
  -- Phase 1: finish converting a to d
  apply stepStar_trans (a_to_d (2 * n + 1) (2 * n + 1) 2)
  rw [show 2 + 2 * (2 * n + 1) = 4 * n + 4 from by ring]
  -- Now at (0, 0, 2*n+1, 4*n+4, 0)
  -- Phase 2: drain
  rw [show (2 * n + 1 : ℕ) = 0 + (2 * n + 1) from by ring,
      show (4 * n + 4 : ℕ) = 2 + 2 * (2 * n + 1) from by ring]
  apply stepStar_trans (drain (2 * n + 1) 0 2 0)
  rw [show (0 : ℕ) + (2 * n + 1) = 2 * n + 1 from by ring]
  -- Now at (0, 0, 0, 2, 4*n+2)
  rw [show (0 : ℕ) + 2 * (2 * n + 1) = 4 * n + 2 from by ring]
  -- Phase 3: middle phase
  rw [show (4 * n + 2 : ℕ) = (4 * n + 1) + 1 from by ring]
  apply stepStar_trans middle_phase
  rw [show (4 * n + 1 + 1 : ℕ) = 2 * (2 * n + 1) from by ring]
  -- Now at (2, 0, 1, 0, 2*(2*n+1))
  -- Phase 4: convert phase with k = 2*n
  rw [show 2 * (2 * n + 1) = 2 * (2 * n + 1) from rfl]
  have h4 := convert_phase (2 * n)
  rw [show 2 * n + 1 + 1 = 2 * n + 2 from by ring] at h4
  apply stepStar_trans h4
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨2 * (n + 1), 0, 2 * n + 1, 0, 0⟩) 0
  intro n
  exact ⟨2 * n + 1, main_cycle n⟩

end Sz22_2003_unofficial_239
