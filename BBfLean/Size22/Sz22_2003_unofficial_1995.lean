import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1995: [99/35, 5/6, 4/5, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  1  0  0
 2  0 -1  0  0
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1995

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 repeated: move e to d.
theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

-- R3 repeated: convert c to a.
theorem r3_chain : ∀ k a, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih (a + 2))
    ring_nf; finish

-- R1,R2 alternating chain: each pair shifts a-=1, b+=1, d-=1, e+=1.
theorem r1r2_chain : ∀ k, ∀ a b d e, ⟨a + k, b, 1, d + k, e⟩ [fm]⊢* ⟨a, b + k, 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih a (b + 1) d (e + 1))
    ring_nf; finish

-- Drain: (0, b, c+1, 0, e) →* (b + 2*c + 2, 0, 0, 0, e).
theorem drain : ∀ b, ∀ c, ⟨(0 : ℕ), b, c + 1, 0, e⟩ [fm]⊢* ⟨b + 2 * c + 2, 0, 0, 0, e⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro c
  rcases b with _ | _ | b
  · -- b = 0: R3 chain
    apply stepStar_trans (r3_chain (c + 1) 0 (e := e))
    ring_nf; finish
  · -- b = 1: R3, R2, then R3 chain
    step fm
    step fm
    apply stepStar_trans (r3_chain (c + 1) 1 (e := e))
    ring_nf; finish
  · -- b + 2: R3, R2, R2, then IH with b, c+1
    step fm
    step fm
    step fm
    apply stepStar_trans (ih b (by omega) (c + 1))
    ring_nf; finish

-- Main transition: (n+1, 0, 0, 0, n) →⁺ (n+2, 0, 0, 0, n+1).
theorem main_trans : ⟨n + 1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, n + 1⟩ := by
  -- Phase 1: e_to_d: (n+1, 0, 0, 0, n) →* (n+1, 0, 0, n, 0)
  apply stepStar_stepPlus_stepPlus (e_to_d n 0 (a := n + 1))
  -- Phase 2: R5: (n+1, 0, 0, n, 0) → (n, 0, 1, n, 1)
  step fm
  -- Phase 3: R1R2 chain
  -- Goal has: (n, 0, 1, 0 + n, 1) [fm]⊢* (n + 2, 0, 0, 0, n + 1)
  -- r1r2_chain n 0 0 0 1 gives: (0 + n, 0, 1, 0 + n, 1) →* (0, 0 + n, 1, 0, 1 + n)
  -- Use stepStar_trans with exact term
  have h_chain := r1r2_chain n 0 0 0 1
  -- h_chain : (0 + n, 0, 1, 0 + n, 1) [fm]⊢* (0, 0 + n, 1, 0, 1 + n)
  -- goal has (n, ..., 0 + n, ...), h_chain has (0 + n, ..., 0 + n, ...)
  -- But 0 + n and n differ. Use Nat.zero_add to convert h_chain.
  rw [Nat.zero_add] at h_chain
  -- h_chain : (n, 0, 1, n, 1) [fm]⊢* (0, n, 1, 0, 1 + n)
  simp only [Nat.zero_add] -- normalize goal
  apply stepStar_trans h_chain
  -- Phase 4: drain
  rw [show (1 : ℕ) + n = n + 1 from by ring]
  show ⟨0, n, 0 + 1, 0, n + 1⟩ [fm]⊢* ⟨n + 2, 0, 0, 0, n + 1⟩
  apply stepStar_trans (drain n 0 (e := n + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, n + 1⟩) 0
  intro n
  exists n + 1
  exact main_trans
