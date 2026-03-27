import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #583: [35/6, 11/2, 56/55, 3/7, 10/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 3  0 -1  1 -1
 0  1  0 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6

-/

namespace Sz22_2003_unofficial_583

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b d

-- c-drain: (3, 0, C, D, E) →* (0, 0, 0, D+C, E+2*C+3)
theorem c_drain : ∀ C, ∀ D E, ⟨3, 0, C, D, E⟩ [fm]⊢* ⟨0, 0, 0, D+C, E+2*C+3⟩ := by
  intro C; induction' C with C ih <;> intro D E
  · step fm; step fm; step fm; finish
  · step fm; step fm; step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Main interleaving by strong induction on B
-- (3, B, C, D, B+F) →* (0, 0, 0, D+2*B+C, 2*B+F+2*C+3)
theorem interleave : ∀ B, ∀ C D F,
    ⟨3, B, C, D, B+F⟩ [fm]⊢* ⟨0, 0, 0, D+2*B+C, 2*B+F+2*C+3⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih
  intro C D F
  rcases B with _ | _ | _ | B
  · -- B=0: c_drain
    simp only [Nat.zero_add, Nat.mul_zero]
    exact c_drain C D F
  · -- B=1: R1, R2×2, R3, then c_drain
    step fm; step fm; step fm; step fm
    rw [show D + 1 + 1 = D + 2 from by ring, show 1 + F + 1 = 2 + F from by ring]
    apply stepStar_trans (c_drain C (D+2) (2+F))
    ring_nf; finish
  · -- B=2: R1×2, R2, R3, then c_drain
    step fm; step fm; step fm; step fm
    rw [show D + 1 + 1 + 1 = D + 3 from by ring]
    apply stepStar_trans (c_drain (C+1) (D+3) (2+F))
    ring_nf; finish
  · -- B+3: R1×3, R3, then recurse with B
    rw [show B + 3 + F = (B + (F + 2)) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih B (by omega) (C+2) (D+4) (F+2))
    ring_nf; finish

-- Transition for d=0: (0, 0, 0, 0, f+1) →⁺ (0, 0, 0, 1, f+3)
theorem trans_d0 : ⟨0, 0, 0, 0, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, f+3⟩ := by
  execute fm 6

-- Transition for d≥1: (0, 0, 0, d+1, d+2+f) →⁺ (0, 0, 0, 2*d+3, 2*d+f+5)
theorem trans_succ : ⟨0, 0, 0, d+1, d+2+f⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*d+3, 2*d+f+5⟩ := by
  -- Phase 1: R4 chain → (0, d+1, 0, 0, d+2+f)
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0))
  simp only [Nat.zero_add]
  -- Phase 2: R5, R1, R3 → (3, d, 1, 2, d+f)
  rw [show d + 2 + f = d + f + 1 + 1 from by ring]
  step fm; step fm; step fm
  -- Phase 3: interleave with B=d, F=f
  apply stepStar_trans (interleave d 1 2 f)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, f⟩ ↦ ⟨0, 0, 0, d, d+1+f⟩) ⟨0, 0⟩
  intro ⟨d, f⟩
  rcases d with _ | d
  · refine ⟨⟨1, f+1⟩, ?_⟩
    show ⟨0, 0, 0, 0, 0+1+f⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, 1+1+(f+1)⟩
    rw [show (0:ℕ)+1+f = f+1 from by ring, show 1+1+(f+1) = f+3 from by ring]
    exact trans_d0
  · refine ⟨⟨2*d+3, f+1⟩, ?_⟩
    show ⟨0, 0, 0, d+1, d+1+1+f⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*d+3, 2*d+3+1+(f+1)⟩
    rw [show d+1+1+f = d+2+f from by ring, show 2*d+3+1+(f+1) = 2*d+f+5 from by ring]
    exact trans_succ

end Sz22_2003_unofficial_583
