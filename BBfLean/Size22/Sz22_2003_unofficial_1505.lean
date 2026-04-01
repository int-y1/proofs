import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1505: [7/15, 9/77, 250/7, 11/25, 7/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 1  0  3 -1  0
 0  0 -2  0  1
-1  0  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1505

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+3, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: (a, 0, 1 + 2*k, 0, e) ⊢* (a, 0, 1, 0, e + k)
theorem r4_chain : ∀ k, ∀ a e, ⟨a, 0, 1 + 2 * k, 0, e⟩ [fm]⊢* ⟨a, 0, 1, 0, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a e; exists 0
  · intro a e
    rw [show 1 + 2 * (k + 1) = (1 + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (e + 1)); ring_nf; finish

-- R5+R2 chain: (a + k, b, 0, 0, k) ⊢* (a, b + 2*k, 0, 0, 0)
theorem r5r2_chain : ∀ k, ∀ a b, ⟨a + k, b, 0, 0, k⟩ [fm]⊢* ⟨a, b + 2 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih
  · intro a b; exists 0
  · intro a b
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih a (b + 2)); ring_nf; finish

-- Interleave: (a + 1, 0, 1, 0, a + 1) ⊢* (1, 2*a + 1, 3, 0, 0)
theorem interleave : ∀ a, ⟨a + 1, 0, 1, 0, a + 1⟩ [fm]⊢* ⟨1, 2 * a + 1, 3, 0, 0⟩ := by
  intro a; induction' a with a ih
  · execute fm 4
  · rw [show (a + 1 : ℕ) + 1 = (a + 1) + 1 from rfl]
    step fm; step fm; step fm; step fm
    rw [show (a : ℕ) + 1 = 1 + a from by ring]
    apply stepStar_trans (r5r2_chain a 1 3)
    rw [show 3 + 2 * a = 2 * (a + 1) + 1 from by ring]
    step fm; step fm; ring_nf; finish

-- R3 chain: (a, 0, c, k, 0) ⊢* (a + k, 0, c + 3*k, 0, 0)
theorem r3_chain : ∀ k, ∀ a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a + k, 0, c + 3 * k, 0, 0⟩ := by
  intro k; induction' k with k ih
  · intro a c; simp; exists 0
  · intro a c
    rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 1) (c + 3)); ring_nf; finish

-- Drain: (K, b, 3, D, 0) ⊢* (K + b + D, 0, 2*b + 3*D + 3, 0, 0)
theorem drain : ∀ b, ∀ K D, ⟨K, b, 3, D, 0⟩ [fm]⊢* ⟨K + b + D, 0, 2 * b + 3 * D + 3, 0, 0⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih
  rcases b with _ | _ | _ | b
  · intro K D
    rw [show K + 0 + D = K + D from by ring,
        show 2 * 0 + 3 * D + 3 = 3 + 3 * D from by ring]
    exact r3_chain D K 3
  · intro K D
    step fm
    rw [show K + 1 + D = K + (D + 1) from by ring,
        show 2 * 1 + 3 * D + 3 = 2 + 3 * (D + 1) from by ring]
    exact r3_chain (D + 1) K 2
  · intro K D
    step fm; step fm
    rw [show K + 2 + D = K + (D + 2) from by ring,
        show 2 * 2 + 3 * D + 3 = 1 + 3 * (D + 2) from by ring]
    exact r3_chain (D + 2) K 1
  · intro K D
    rw [show (b + 3 : ℕ) = (b + 2) + 1 from by ring]
    step fm
    rw [show (b + 2 : ℕ) = (b + 1) + 1 from by ring]
    step fm
    rw [show (b + 1 : ℕ) = b + 1 from rfl]
    step fm
    rw [show D + 1 + 1 + 1 = (D + 3) from by ring]
    step fm
    apply stepStar_trans (ih b (by omega) (K + 1) (D + 2))
    ring_nf; finish

-- Main transition: (n+1, 0, 2n+3, 0, 0) ⊢⁺ (2n+2, 0, 4n+5, 0, 0)
theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, 2 * n + 3, 0, 0⟩ [fm]⊢⁺ ⟨2 * n + 2, 0, 4 * n + 5, 0, 0⟩ := by
  -- First R4 step (⊢⁺)
  rw [show 2 * n + 3 = (1 + 2 * n) + 2 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨n + 1, 0, (1 + 2 * n) + 2, 0, 0⟩ = some ⟨n + 1, 0, 1 + 2 * n, 0, 1⟩; rfl
  -- Now: (n+1, 0, 1+2n, 0, 1) ⊢* (2n+2, 0, 4n+5, 0, 0)
  -- Remaining R4 steps
  apply stepStar_trans (r4_chain n (n + 1) 1)
  rw [show (1 : ℕ) + n = n + 1 from by ring]
  -- Interleave: (n+1, 0, 1, 0, n+1) ⊢* (1, 2n+1, 3, 0, 0)
  apply stepStar_trans (interleave n)
  -- Drain: (1, 2n+1, 3, 0, 0) ⊢* (2n+2, 0, 4n+5, 0, 0)
  apply stepStar_trans (drain (2 * n + 1) 1 0)
  rw [show 1 + (2 * n + 1) + 0 = 2 * n + 2 from by ring,
      show 2 * (2 * n + 1) + 3 * 0 + 3 = 4 * n + 5 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 3, 0, 0⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 2 * n + 3, 0, 0⟩) 0
  intro n
  refine ⟨2 * n + 1, ?_⟩
  rw [show 2 * n + 1 + 1 = 2 * n + 2 from by ring,
      show 2 * (2 * n + 1) + 3 = 4 * n + 5 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1505
