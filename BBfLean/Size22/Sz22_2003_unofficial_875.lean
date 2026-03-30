import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #875: [4/15, 1/154, 21/2, 11/3, 375/7]

Vector representation:
```
 2 -1 -1  0  0
-1  0  0 -1 -1
-1  1  0  1  0
 0 -1  0  0  1
 0  1  3 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_875

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+3, d, e⟩
  | _ => none

def tri : ℕ → ℕ
  | 0 => 0
  | n + 1 => tri n + n + 1

theorem tri_succ (n : ℕ) : tri (n + 1) = tri n + n + 1 := by rfl

-- R3 chain: transfer a to b
theorem a_to_b : ∀ k b d, ⟨k, b, 0, d, 0⟩ [fm]⊢* ⟨0, b + k, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) (d + 1))
    ring_nf; finish

-- R4 chain: transfer b to e
theorem b_to_e : ∀ k d e, ⟨0, k, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- One drain round: R5, R1, R2, R2
theorem drain_round : ∀ c d e, ⟨0, 0, c, d + 3, e + 2⟩ [fm]⊢* ⟨0, 0, c + 2, d, e⟩ := by
  intro c d e
  step fm; step fm; step fm; step fm; finish

-- Drain loop: k rounds
theorem drain_loop : ∀ k c D E, ⟨0, 0, c, D + 3 * k, E + 2 * k⟩ [fm]⊢* ⟨0, 0, c + 2 * k, D, E⟩ := by
  intro k; induction' k with k ih <;> intro c D E
  · exists 0
  · rw [show D + 3 * (k + 1) = (D + 3 * k) + 3 from by ring,
        show E + 2 * (k + 1) = (E + 2 * k) + 2 from by ring]
    apply stepStar_trans (drain_round c (D + 3 * k) (E + 2 * k))
    apply stepStar_trans (ih (c + 2) D E)
    ring_nf; finish

-- Exit for general case: (0, 0, c, d+2, 1) → (1, 0, c+2, d, 0) in 3 steps
theorem exit_d2 : ⟨0, 0, c, d + 2, 1⟩ [fm]⊢⁺ ⟨1, 0, c + 2, d, 0⟩ := by
  step fm; step fm; step fm; finish

-- Exit for d=1 case: (0, 0, c, 1, 1) → (2, 0, c+1, 0, 0) in 5 steps
theorem exit_d1 : ⟨0, 0, c, 1, 1⟩ [fm]⊢⁺ ⟨2, 0, c + 1, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- R3+R1 interleaved chain
theorem r3r1_chain : ∀ k a d, ⟨a + 1, 0, k, d, 0⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm; step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (d + 1))
    ring_nf; finish

-- Main transition for n = 0: (3, 0, 0, 1, 0) ⊢⁺ (5, 0, 0, 3, 0)
theorem main_trans_n0 : ⟨3, 0, 0, 1, 0⟩ [fm]⊢⁺ ⟨5, 0, 0, 3, 0⟩ := by
  execute fm 21

-- Key arithmetic: tri(n) + 2*n + 3 = tri(n+2)
theorem tri_add_2n3 (n : ℕ) : tri n + 2 * n + 3 = tri (n + 2) := by
  simp [tri_succ]; ring

-- Key arithmetic: tri(n+1) + 2*n + 3 - 3*(n+1) = tri(n) + 1
-- i.e., tri(n+1) - n = tri(n) + 1
theorem tri_drain (n : ℕ) : tri (n + 1) + 2 * n + 3 - 3 * (n + 1) = tri n + 1 := by
  simp [tri_succ]; omega

-- Phase 1+2: (a, 0, 0, d, 0) →* (0, 0, 0, d+a, a)
theorem phase12 (a d : ℕ) : ⟨a, 0, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d + a, a⟩ := by
  apply stepStar_trans (a_to_b a 0 d)
  rw [Nat.zero_add]
  apply stepStar_trans (b_to_e a (d + a) 0)
  rw [Nat.zero_add]; finish

-- tri(n) >= 1 for n >= 1
theorem tri_pos (n : ℕ) (hn : n ≥ 1) : tri n ≥ 1 := by
  rcases n with _ | n
  · omega
  · unfold tri; omega

-- Main transition for n >= 1:
-- (2n+3, 0, 0, tri(n+1), 0) ⊢⁺ (2n+5, 0, 0, tri(n+2), 0)
theorem main_trans_ge1 (n : ℕ) (hn : n ≥ 1) :
    ⟨2 * n + 3, 0, 0, tri (n + 1), 0⟩ [fm]⊢⁺
    ⟨2 * n + 5, 0, 0, tri (n + 2), 0⟩ := by
  -- Phase 1+2: R3 then R4 chain
  apply stepStar_stepPlus_stepPlus (phase12 (2 * n + 3) (tri (n + 1)))
  -- Now at (0, 0, 0, tri(n+1)+2n+3, 2n+3)
  -- Phase 3: Drain loop with n+1 rounds
  apply stepStar_stepPlus_stepPlus
  · rw [show tri (n + 1) + (2 * n + 3) = (tri n + 1) + 3 * (n + 1) from by
          simp [tri_succ]; ring,
        show 2 * n + 3 = 1 + 2 * (n + 1) from by ring]
    exact drain_loop (n + 1) 0 (tri n + 1) 1
  -- Now at (0, 0, 2*(n+1), tri(n)+1, 1)
  -- Phase 4: Exit (tri(n)+1 >= 2 since n >= 1)
  have htri : tri n ≥ 1 := tri_pos n hn
  rw [show 0 + 2 * (n + 1) = 2 * (n + 1) from by ring,
      show tri n + 1 = (tri n - 1) + 2 from by omega]
  apply stepPlus_stepStar_stepPlus (exit_d2 (c := 2 * (n + 1)) (d := tri n - 1))
  -- Now at (1, 0, 2*(n+1)+2, tri(n)-1, 0)
  -- Phase 5: R3R1 chain
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1_chain (2 * (n + 1) + 2) 0 (tri n - 1))
  rw [show 0 + 1 + (2 * (n + 1) + 2) = 2 * n + 5 from by ring,
      show tri n - 1 + (2 * (n + 1) + 2) = tri n + 2 * n + 3 from by omega,
      tri_add_2n3]
  finish

-- Combined main transition
theorem main_trans (n : ℕ) :
    ⟨2 * n + 3, 0, 0, tri (n + 1), 0⟩ [fm]⊢⁺
    ⟨2 * (n + 1) + 3, 0, 0, tri (n + 2), 0⟩ := by
  rcases n with _ | n
  · -- n = 0: tri(1) = 1, tri(2) = 3
    simp [tri]; exact main_trans_n0
  · -- n >= 1
    rw [show 2 * (n + 1 + 1) + 3 = 2 * (n + 1) + 5 from by ring]
    exact main_trans_ge1 (n + 1) (by omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩)
  · show c₀ [fm]⊢* ⟨3, 0, 0, tri 1, 0⟩
    simp [tri]; execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, 0, tri (n + 1), 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
