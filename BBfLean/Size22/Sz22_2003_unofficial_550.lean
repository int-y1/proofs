import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #550: [28/45, 5/22, 9/2, 11/7, 14/3]

Vector representation:
```
 2 -2 -1  1  0
-1  0  1  0 -1
-1  2  0  0  0
 0  0  0 -1  1
 1 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6

---

Canonical states are (n+2, 0, 0, 2*n+2, 0) for n = 0, 1, 2, ...
Each transition from (n+2, 0, 0, 2*n+2, 0) to (n+3, 0, 0, 2*n+4, 0)
proceeds in two rounds through an intermediate state.
-/

namespace Sz22_2003_unofficial_550

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R3 chain: repeated R3 converting a to b
theorem r3_chain : ∀ k, ∀ a b d, ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b+2*k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 chain: repeated R4 converting d to e
theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b, 0, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R2R1 chain: interleaved R2,R1 rounds
theorem r2r1_chain : ∀ k, ∀ a b d e,
    ⟨a+1, b+2*k, 0, d, e+k⟩ [fm]⊢* ⟨a+k+1, b, 0, d+k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R2 drain with b=0
theorem r2_drain_b0 : ∀ k, ∀ a c d, ⟨a+k, 0, c, d, k⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R2 drain with b=1
theorem r2_drain_b1 : ∀ k, ∀ a c d, ⟨a+k, 1, c, d, k⟩ [fm]⊢* ⟨a, 1, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3R1 chain with b oscillating 0/2
theorem r3r1_chain_b0 : ∀ k, ∀ a c d,
    ⟨a+1, 0, c+k, d, 0⟩ [fm]⊢* ⟨a+k+1, 0, c, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3R1 chain with b oscillating 1/3
theorem r3r1_chain_b1 : ∀ k, ∀ a c d,
    ⟨a+1, 1, c+k, d, 0⟩ [fm]⊢* ⟨a+k+1, 1, c, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Round 2: (n+1, 3, 0, 2*n+3, 0) →* (n+3, 0, 0, 2*n+4, 0)
theorem round2 (n : ℕ) : ⟨n+1, 3, 0, 2*n+3, 0⟩ [fm]⊢* ⟨n+3, 0, 0, 2*n+4, 0⟩ := by
  -- Phase 11: r3_chain (n+1 steps)
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (r3_chain (n+1) 0 3 (2*n+3))
  -- Phase 12: r4_chain (2n+3 steps)
  rw [show 3 + 2 * (n + 1) = 2 * n + 5 from by ring,
      show 2 * n + 3 = 0 + (2 * n + 3) from by ring]
  apply stepStar_trans (r4_chain (2*n+3) (2*n+5) 0 0)
  -- Phase 13: R5
  rw [show 0 + (2 * n + 3) = 2 * n + 3 from by ring,
      show 2 * n + 5 = (2 * n + 4) + 1 from by ring]
  step fm
  -- Phase 14: r2r1_chain (n+2 rounds) — combines R2,R1 rounds directly after R5
  -- Current: (1, 2n+4, 0, 1, 2n+3)
  -- r2r1_chain(n+2) with a=0, b=0, d=1, e=n+1:
  rw [show 2 * n + 4 = 0 + 2 * (n + 2) from by ring,
      show 2 * n + 3 = (n + 1) + (n + 2) from by ring]
  apply stepStar_trans (r2r1_chain (n+2) 0 0 1 (n+1))
  -- Phase 15: r2_drain_b0 (n+1 steps)
  -- Current: (n+3, 0, 0, n+3, n+1) in some normalized form
  rw [show 0 + (n + 2) + 1 = 2 + (n + 1) from by ring,
      show 1 + (n + 2) = n + 3 from by ring]
  apply stepStar_trans (r2_drain_b0 (n+1) 2 0 _)
  -- Phase 16: r3r1_chain_b0 (n+1 rounds)
  -- Current: (2, 0, n+1, n+3, 0) in some normalized form
  have h16 := @r3r1_chain_b0 (n+1) 1 0
  simp only [Nat.zero_add] at h16
  rw [show 0 + (n + 1) = n + 1 from by ring]
  apply stepStar_trans (h16 _)
  ring_nf; finish

-- Full transition: (n+2, 0, 0, 2*(n+1), 0) →⁺ (n+3, 0, 0, 2*(n+2), 0)
theorem main_trans (n : ℕ) : ⟨n+2, 0, 0, 2*n+2, 0⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 2*n+4, 0⟩ := by
  -- === Round 1 ===
  -- Phase 1: R3 chain
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r3_chain (n+2) 0 0 (2*n+2))
  -- Phase 2: R4 chain
  rw [show 0 + 2 * (n + 2) = 2 * (n + 2) from by ring,
      show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2*n+2) (2*(n+2)) 0 0)
  rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring]
  -- Phase 3: R5
  rw [show 2 * (n + 2) = (2 * n + 3) + 1 from by ring]
  step fm
  -- Phase 4: r2r1_chain (n rounds)
  rw [show 2 * n + 3 = 3 + 2 * n from by ring,
      show 2 * n + 2 = (n + 2) + n from by ring]
  apply stepStar_trans (r2r1_chain n 0 3 1 (n+2))
  -- Phase 5: R2, R1
  rw [show 0 + n + 1 = n + 1 from by ring,
      show n + 2 = (n + 1) + 1 from by ring,
      show 1 + n = n + 1 from by ring]
  step fm; step fm
  -- Phase 6: r2_drain_b1 (n+1 steps)
  rw [show n + 1 + 1 = 1 + (n + 1) from by ring]
  apply stepStar_trans (r2_drain_b1 (n+1) 1 0 _)
  -- Phase 7: R3
  rw [show 0 + (n + 1) = n + 1 from by ring]
  step fm
  -- Phase 8: R1
  step fm
  -- Phase 9: r3r1_chain_b1 (n rounds)
  have h9 := @r3r1_chain_b1 n 1 0
  simp only [Nat.zero_add] at h9
  apply stepStar_trans (h9 _)
  -- Phase 10: R3
  rw [show 1 + n + 1 = (n + 1) + 1 from by ring]
  step fm
  -- === Round 2 ===
  -- The d component `1 + (n + 1) + 1 + n` needs to be normalized to `2 * n + 3`
  rw [show 1 + (n + 1) + 1 + n = 2 * n + 3 from by ring]
  exact round2 n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 2*n+2, 0⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩
