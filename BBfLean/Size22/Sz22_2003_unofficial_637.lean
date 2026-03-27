import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #637: [35/6, 143/2, 4/55, 3/7, 385/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 0  0  1  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_637

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d+1, e+1, f⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R3R2R2 chain: each round converts c+e into e+1 and f+2
theorem r3r2r2_chain : ∀ k c e f, ⟨0, 0, c+k, d, e+k, f⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k, f+2*k⟩ := by
  intro k; induction' k with k h <;> intro c e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show e + k + 1 + 1 = (e + 2) + k from by ring,
      show f + 1 + 1 = f + 2 from by ring]
  apply stepStar_trans (h c (e + 2) (f + 2))
  ring_nf; finish

-- R1R1R3 chain: each round consumes 2 from b and 1 from e, produces 1 for c and 2 for d
theorem r1r1r3_chain : ∀ k c d e,
    ⟨2, b+2*k, c, d, e+k, f⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e, f⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h (c + 1) (d + 2) e)
  ring_nf; finish

-- Full transition for even case: n = 2k+1, n+1 = 2(k+1)
theorem main_even (k : ℕ) :
    ⟨0, 0, 0, 2*k+1+1, 2*(2*k+1)+3, f+1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*k+1+2, 2*(2*k+1)+5, f+(2*k+1)+3⟩ := by
  -- Normalize arithmetic in the goal
  rw [show 2 * (2 * k + 1) + 3 = 4 * k + 5 from by ring,
      show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
      show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
      show 2 * (2 * k + 1) + 5 = 4 * k + 7 from by ring,
      show f + (2 * k + 1) + 3 = f + 2 * k + 4 from by ring]
  -- Phase 1: R4 chain
  rw [show (2 : ℕ) * k + 2 = 0 + (2 * k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2 * k + 2) 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5 + R3
  rw [show (4 : ℕ) * k + 5 = (4 * k + 4) + 1 from by ring]
  step fm
  rw [show (4 : ℕ) * k + 4 + 1 + 1 = (4 * k + 5) + 1 from by ring]
  step fm
  -- Phase 3: R1R1R3 chain with (k+1) rounds
  rw [show (2 : ℕ) * k + 2 = 0 + 2 * (k + 1) from by ring,
      show (4 : ℕ) * k + 5 = (3 * k + 4) + (k + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (k + 1) 0 1 (3 * k + 4))
  simp only [Nat.zero_add]
  -- Phase 4: R2 + R2
  step fm; step fm
  -- Phase 5: R3R2R2 chain with (k+1) rounds
  rw [show (k : ℕ) + 1 = 0 + (k + 1) from by ring,
      show (3 : ℕ) * k + 4 + 1 + 1 = (2 * k + 5) + (k + 1) from by ring]
  apply stepStar_trans (r3r2r2_chain (k + 1) 0 (2 * k + 5) (f + 2))
  simp only [Nat.zero_add]
  ring_nf; finish

-- Full transition for odd case: n = 2K, n+1 = 2K+1
theorem main_odd (K : ℕ) :
    ⟨0, 0, 0, 2*K+1, 2*(2*K)+3, f+1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*K+2, 2*(2*K)+5, f+2*K+3⟩ := by
  -- Normalize arithmetic in the goal
  rw [show 2 * (2 * K) + 3 = 4 * K + 3 from by ring,
      show 2 * (2 * K) + 5 = 4 * K + 5 from by ring]
  -- Phase 1: R4 chain
  rw [show (2 : ℕ) * K + 1 = 0 + (2 * K + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2 * K + 1) 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5 + R3
  rw [show (4 : ℕ) * K + 3 = (4 * K + 2) + 1 from by ring]
  step fm
  rw [show (4 : ℕ) * K + 2 + 1 + 1 = (4 * K + 3) + 1 from by ring]
  step fm
  -- Phase 3: R1R1R3 chain with K rounds
  rw [show (2 : ℕ) * K + 1 = 1 + 2 * K from by ring,
      show (4 : ℕ) * K + 3 = (3 * K + 3) + K from by ring]
  apply stepStar_trans (r1r1r3_chain K 0 1 (3 * K + 3))
  simp only [Nat.zero_add]
  -- Phase 4: R1 + R2
  rw [show (3 : ℕ) * K + 3 = (3 * K + 2) + 1 from by ring]
  step fm; step fm
  -- Phase 5: R3R2R2 chain with (K+1) rounds
  rw [show K + 1 = 0 + (K + 1) from by ring,
      show (3 : ℕ) * K + 2 + 1 + 1 = (2 * K + 3) + (K + 1) from by ring]
  apply stepStar_trans (r3r2r2_chain (K + 1) 0 (2 * K + 3) (f + 1))
  ring_nf; finish

-- Main transition composing even/odd cases
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, n+1, 2*n+3, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, n+2, 2*n+5, f+n+3⟩ := by
  rcases Nat.even_or_odd (n + 1) with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK
    obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    have hn : n = 2 * k + 1 := by omega
    subst hn
    exact main_even k
  · have hn : n = 2 * K := by omega
    subst hn
    exact main_odd K

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3, 2⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, 0, n+1, 2*n+3, f+1⟩) ⟨0, 1⟩
  intro ⟨n, f⟩
  exact ⟨⟨n + 1, f + n + 2⟩, main_trans n⟩
