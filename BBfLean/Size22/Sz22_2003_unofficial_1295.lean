import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1295: [63/10, 121/2, 2/33, 5/7, 10/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 1 -1  0  0 -1
 0  0  1 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1295

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- Phase 1: R1/R3 interleaved chain.
-- Each round: (1, B, C+1, D, E+1) -> R1 -> (0, B+2, C, D+1, E+1) -> R3 -> (1, B+1, C, D+1, E)
-- Net: b+1, c-1, d+1, e-1.
theorem r1r3_chain : ∀ k, ∀ b c d e, ⟨1, b, c + k, d, e + k⟩ [fm]⊢* ⟨1, b + k, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) c (d + 1) e); ring_nf; finish

-- Phase 2: R2/R3 interleaved chain (b to e transfer).
-- Each round: (1, B+1, 0, D, E) -> R2 -> (0, B+1, 0, D, E+2) -> R3 -> (1, B, 0, D, E+1)
-- Net: b-1, e+1.
theorem r2r3_chain : ∀ k, ∀ b d e, ⟨1, b + k, 0, d, e⟩ [fm]⊢* ⟨1, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b d (e + 1)); ring_nf; finish

-- Phase 3: R4 chain (d to c transfer).
theorem d_to_c : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e); ring_nf; finish

-- Main transition: (1, 0, n+1, 0, n+1) ⊢⁺ (1, 0, n+2, 0, n+2)
theorem main_trans (n : ℕ) :
    ⟨1, 0, n + 1, 0, n + 1⟩ [fm]⊢⁺ ⟨1, 0, n + 2, 0, n + 2⟩ := by
  -- Phase 1: R1/R3 chain, n+1 rounds.
  have h1 := r1r3_chain (n + 1) 0 0 0 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2: R2/R3 chain, n+1 rounds.
  have h2 := r2r3_chain (n + 1) 0 (n + 1) 0
  simp only [Nat.zero_add] at h2
  apply stepStar_stepPlus_stepPlus h2
  -- Now at (1, 0, 0, n+1, n+1). R2 fires.
  step fm
  -- Normalize n+1+2 to n+3.
  rw [show n + 1 + 2 = n + 3 from by ring]
  -- Phase 3: R4 chain, n+1 rounds.
  have h3 := d_to_c (n + 1) 0 0 (n + 3)
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  -- Phase 4: R5 fires once.
  rw [show n + 3 = (n + 2) + 1 from by ring]
  step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 1, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, n + 1, 0, n + 1⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1295
