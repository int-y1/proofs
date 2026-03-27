import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #647: [35/6, 143/2, 52/55, 3/7, 35/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  1
 0  1  0 -1  0  0
 0  0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_647

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | _ => none

-- R4 repeated: transfer d to b
theorem d_to_b : ∀ k, ∀ b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R5+R3: preamble step
theorem preamble : ⟨0, b, 0, 0, e+1, f+1⟩ [fm]⊢⁺ ⟨2, b, 0, 1, e, f+1⟩ := by
  step fm; step fm; finish

-- Drain phase: strong induction on 2*B+C
-- Takes (2, B, C, D, E, F) to (2, 0, 0, D+B, E+C, F+2*B+3*C) when B ≤ E
theorem drain : ∀ N, ∀ B C D E F, 2*B+C = N → B ≤ E →
    ⟨2, B, C, D, E, F⟩ [fm]⊢* ⟨2, 0, 0, D+B, E+C, F+2*B+3*C⟩ := by
  intro N; induction' N using Nat.strongRecOn with N ih; intro B C D E F hN hBE
  rcases B with _ | _ | B
  · -- B = 0
    rcases C with _ | C
    · -- C = 0: done
      simp; finish
    · -- C ≥ 1: R2+R2+R3
      step fm; step fm; step fm
      rw [show D + 0 = D from by ring, show E + (C + 1) = (E + 1) + C from by ring,
          show F + 2 * 0 + 3 * (C + 1) = (F + 3) + 2 * 0 + 3 * C from by ring]
      apply ih (2*0+C) (by omega) 0 C D (E+1) (F+3) (by ring) (by omega)
  · -- B = 1: R1+R2+R3
    step fm; step fm; step fm
    rw [show D + 1 = (D + 1) + 0 from by ring, show E + C = E + C from by ring,
        show F + 2 * 1 + 3 * C = (F + 2) + 2 * 0 + 3 * C from by ring]
    apply ih (2*0+C) (by omega) 0 C (D+1) E (F+2) (by ring) (by omega)
  · -- B ≥ 2: R1+R1+R3
    obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
    step fm; step fm; step fm
    rw [show D + (B + 2) = (D + 2) + B from by ring,
        show E' + 1 + C = E' + (C + 1) from by ring,
        show F + 2 * (B + 2) + 3 * C = (F + 1) + 2 * B + 3 * (C + 1) from by ring]
    apply ih (2*B+(C+1)) (by omega) B (C+1) (D+2) E' (F+1) (by ring) (by omega)

-- Final R2+R2
theorem final_r2r2 : ⟨2, 0, 0, D, E, F⟩ [fm]⊢* ⟨0, 0, 0, D, E+2, F+2⟩ := by
  step fm; step fm; finish

-- Main transition: one full cycle
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, n, n+1, n*n+n+1⟩ [fm]⊢⁺ ⟨0, 0, 0, n+1, n+2, (n+1)*(n+1)+(n+1)+1⟩ := by
  -- Phase 1: d_to_b
  apply stepStar_stepPlus_stepPlus (d_to_b n 0 (n+1) (n*n+n+1))
  simp only [Nat.zero_add]
  -- Phase 2: preamble (R5+R3)
  rw [show n * n + n + 1 = (n * n + n) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (@preamble n n (n*n+n))
  -- Phase 3: drain
  have hdrain := drain (2*n+0) n 0 1 n (n*n+n+1) (by ring) (le_refl n)
  apply stepStar_trans hdrain
  -- Phase 4: final R2+R2
  apply stepStar_trans final_r2r2
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n, n+1, n*n+n+1⟩) 0
  intro n; exists n+1; exact main_trans n
