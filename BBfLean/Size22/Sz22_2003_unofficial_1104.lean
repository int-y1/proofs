import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1104: [5/6, 4/35, 539/2, 3/11, 1/5, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  2  1
 0  1  0  0 -1
 0  0 -1  0  0
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1104

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 chain: drain a into d and e, with b=0 and c=0.
theorem r3_chain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

-- R4 chain: drain e into b, with a=0 and c=0.
theorem r4_chain : ∀ k, ∀ b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- R2 chain with b=0: drain c into a, with b=0 and e=0.
theorem r2_chain : ∀ k, ∀ a d, ⟨a, 0, k, d + k, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d)
    ring_nf; finish

-- Mix round: one round of the interleaving phase (R2, R1, R1).
theorem mix_round : ⟨0, b + 2, c + 1, d + 1, 0⟩ [fm]⊢* ⟨0, b, c + 2, d, 0⟩ := by
  step fm; step fm; step fm; finish

-- Mixing phase: general form by strong induction on B.
theorem mix_general : ∀ B, ∀ C d,
    ⟨0, B, C + 1, d + B + C + 1, 0⟩ [fm]⊢* ⟨B + 2 * C + 2, 0, 0, d, 0⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro C d
  rcases B with _ | _ | B
  · -- B = 0: pure R2 chain
    show ⟨0, 0, C + 1, d + 0 + C + 1, 0⟩ [fm]⊢* ⟨0 + 2 * C + 2, 0, 0, d, 0⟩
    rw [show d + 0 + C + 1 = d + (C + 1) from by ring]
    apply stepStar_trans (r2_chain (C + 1) 0 d)
    ring_nf; finish
  · -- B = 1: R2, R1, then R2 chain
    show ⟨0, 1, C + 1, d + 1 + C + 1, 0⟩ [fm]⊢* ⟨1 + 2 * C + 2, 0, 0, d, 0⟩
    rw [show d + 1 + C + 1 = (d + C + 1) + 1 from by ring]
    step fm -- R2: (2, 1, C, d+C+1, 0)
    step fm -- R1: (1, 0, C+1, d+C+1, 0)
    rw [show d + C + 1 = d + (C + 1) from by ring]
    apply stepStar_trans (r2_chain (C + 1) 1 d)
    ring_nf; finish
  · -- B + 2: R2, R1, R1, then IH with B and C+1
    show ⟨0, B + 2, C + 1, d + (B + 2) + C + 1, 0⟩ [fm]⊢* ⟨(B + 2) + 2 * C + 2, 0, 0, d, 0⟩
    rw [show d + (B + 2) + C + 1 = (d + B + (C + 1) + 1) + 1 from by ring]
    step fm -- R2
    step fm -- R1
    step fm -- R1
    show ⟨0, B, C + 2, d + B + (C + 1) + 1, 0⟩ [fm]⊢* ⟨B + 2 + 2 * C + 2, 0, 0, d, 0⟩
    apply stepStar_trans (ih B (by omega) (C + 1) d)
    ring_nf; finish

-- Main transition: from canonical (n+2, 0, 0, d, 0) to (n+4, 0, 0, d+n, 0).
theorem main_transition : ∀ n d, ⟨n + 2, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨n + 4, 0, 0, d + n, 0⟩ := by
  intro n d
  -- Phase 1: first R3 step (to get ⊢⁺)
  step fm
  -- Remaining R3 steps
  apply stepStar_trans (r3_chain (n + 1) (d + 2) 1)
  -- Now at (0, 0, 0, d+2+2*(n+1), 1+(n+1)) = (0, 0, 0, d+2n+4, n+2)
  -- Phase 2: R4 chain
  rw [show d + 2 + 2 * (n + 1) = d + 2 * n + 4 from by ring,
      show 1 + (n + 1) = n + 2 from by ring]
  apply stepStar_trans (r4_chain (n + 2) 0 (d + 2 * n + 4))
  -- Now at (0, 0+(n+2), 0, d+2n+4, 0)
  rw [Nat.zero_add]
  -- Phase 3: R6 step
  rw [show d + 2 * n + 4 = (d + 2 * n + 3) + 1 from by ring]
  step fm
  -- Now at (0, n+2, 1, d+2*n+3, 0)
  -- Phase 4: mixing
  rw [show d + 2 * n + 3 = (d + n) + (n + 2) + 0 + 1 from by ring]
  apply stepStar_trans (mix_general (n + 2) 0 (d + n))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 0⟩) (by execute fm 20)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, d⟩ ↦ ⟨n + 2, 0, 0, d, 0⟩) ⟨3, 0⟩
  intro ⟨n, d⟩; exact ⟨⟨n + 2, d + n⟩, main_transition n d⟩

end Sz22_2003_unofficial_1104
