import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #264: [14/15, 1/77, 27/7, 11/9, 175/2]

Vector representation:
```
 1 -1 -1  1  0
 0  0  0 -1 -1
 0  3  0 -1  0
 0 -2  0  0  1
-1  0  2  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_264

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+2, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | _ => none

-- R3 chain: convert d to b when c=0 and e=0
theorem r3_chain : ∀ k, ∀ A B, ⟨A, B, 0, k, 0⟩ [fm]⊢* ⟨A, B+3*k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B
  · simp; exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih A _)
  ring_nf; finish

-- R4 chain (odd b): (A, 2K+1, 0, 0, E) →* (A, 1, 0, 0, E+K)
theorem r4_odd : ∀ K, ∀ A E, ⟨A, 2*K+1, 0, 0, E⟩ [fm]⊢* ⟨A, 1, 0, 0, E+K⟩ := by
  intro K; induction' K with K ih <;> intro A E
  · simp; exists 0
  rw [show 2 * (K + 1) + 1 = (2 * K + 1) + 2 from by ring]
  step fm
  apply stepStar_trans (ih A _)
  ring_nf; finish

-- R5+R2 chain: repeatedly do rule5 then rule2
theorem r5r2_chain : ∀ K, ∀ A C, ⟨A+K, 0, C, 0, K⟩ [fm]⊢* ⟨A, 0, C+2*K, 0, 0⟩ := by
  intro K; induction' K with K ih <;> intro A C
  · simp; exists 0
  rw [show A + (K + 1) = (A + K) + 1 from by ring,
      show (K + 1 : ℕ) = K + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (ih A _)
  ring_nf; finish

-- Process: the key lemma. From (A, 0, C, D+1, 0), all of c and d are consumed.
-- Result: (A+C, 2*C+3*D+3, 0, 0, 0)
theorem process : ∀ C, ∀ A D, ⟨A, 0, C, D+1, 0⟩ [fm]⊢* ⟨A+C, 2*C+3*D+3, 0, 0, 0⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih
  rcases C with _ | _ | _ | C
  · -- C = 0
    intro A D
    have h := r3_chain (D+1) A 0
    simp only [Nat.zero_add] at h
    rw [show 3 * (D + 1) = 3 * D + 3 from by ring] at h
    rw [show A + 0 = A from by ring, show 2 * 0 + 3 * D + 3 = 3 * D + 3 from by ring]
    exact h
  · -- C = 1: R3 then R1, then r3_chain
    intro A D
    step fm; step fm
    have h := r3_chain (D+1) (A+1) 2
    rw [show 2 + 3 * (D + 1) = 2 * 1 + 3 * D + 3 from by ring] at h
    exact h
  · -- C = 2: R3, R1, R1, then r3_chain
    intro A D
    step fm; step fm; step fm
    have h := r3_chain (D+2) (A+2) 1
    rw [show 1 + 3 * (D + 2) = 2 * 2 + 3 * D + 3 from by ring] at h
    exact h
  · -- C + 3: R3, R1, R1, R1, then use IH on C
    intro A D
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih C (by omega) (A+3) (D+2))
    ring_nf; finish

-- Main cycle: (1, 0, c+3, 0, 0) ⊢⁺ (1, 0, 2*c+9, 0, 0)
theorem main_cycle (c : ℕ) : ⟨1, 0, c+3, 0, 0⟩ [fm]⊢⁺ ⟨1, 0, 2*c+9, 0, 0⟩ := by
  -- Phase 1: 5 steps to (3, 0, c+2, 3, 0)
  step fm; step fm; step fm; step fm; step fm
  -- Phase 2: process (c+2, 3, 2) -> (c+5, 2c+13, 0, 0, 0)
  apply stepStar_trans (process (c+2) 3 2)
  -- Phase 3: r4_odd with K=c+6 -> (c+5, 1, 0, 0, c+6)
  rw [show 3 + (c + 2) = c + 5 from by ring,
      show 2 * (c + 2) + 3 * 2 + 3 = 2 * (c + 6) + 1 from by ring]
  apply stepStar_trans (r4_odd (c+6) (c+5) 0)
  -- Phase 4: unwind_init (6 steps) -> (c+4, 0, 3, 0, c+3)
  simp only [Nat.zero_add]
  rw [show c + 5 = (c + 3) + 2 from by ring]
  step fm; step fm; step fm; step fm; step fm; step fm
  -- Phase 5: r5r2_chain with K=c+3, A=1, C=3 -> (1, 0, 2c+9, 0, 0)
  rw [show (c + 3) + 1 = 1 + (c + 3) from by ring]
  apply stepStar_trans (r5r2_chain (c+3) 1 3)
  rw [show 3 + 2 * (c + 3) = 2 * c + 9 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 3, 0, 0⟩)
  · execute fm 15
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, n+3, 0, 0⟩) 0
  intro n; exact ⟨2*n+6, by
    show ⟨1, 0, n+3, 0, 0⟩ [fm]⊢⁺ ⟨1, 0, (2*n+6)+3, 0, 0⟩
    rw [show (2 * n + 6) + 3 = 2 * n + 9 from by ring]
    exact main_cycle n⟩

end Sz22_2003_unofficial_264
