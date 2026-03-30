import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #689: [35/6, 4/55, 11/2, 3/7, 350/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 1  0  2  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_689

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+2, d+1, e⟩
  | _ => none

-- R4 chain: move d to b (when a=0, c=0)
theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R3 chain: move a to e (when b=0, c=0)
theorem a_to_e : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 1))
    ring_nf; finish

-- R2 chain: consume c and e pairwise (when b=0)
theorem r2_chain : ∀ k, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

-- R1,R1,R2 chain: k rounds
-- (2, b+2*k, c, d, e+k) ->* (2, b, c+k, d+2*k, e)
theorem r112_chain : ∀ k, ⟨2, b + 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b := b + 2) (e := e + 1))
    step fm; step fm; step fm
    ring_nf; finish

-- n=1 transition: (0, 0, 0, 1, 3) ⊢⁺ (0, 0, 0, 2, 5)
theorem trans_one : ⟨0, 0, 0, 1, 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2, 5⟩ := by
  execute fm 12

-- Odd transition: n = 2*m+1 (m >= 1)
-- (0, 0, 0, 2*m+1, 4*m+3) ⊢⁺ (0, 0, 0, 2*m+2, 4*m+5)
theorem trans_odd (m : ℕ) (hm : m ≥ 1) :
    ⟨0, 0, 0, 2 * m + 1, 4 * m + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * m + 2, 4 * m + 5⟩ := by
  -- Phase 1: R4 chain (2*m+1 steps)
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2 * m + 1) (b := 0) (d := 0) (e := 4 * m + 3))
  rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring]
  -- Phase 2: R5 step. State: (0, 2*m+1, 0, 0, 4*m+3)
  rw [show (4 * m + 3 : ℕ) = (4 * m + 2) + 1 from by ring]
  step fm
  -- State: (1, 2*m+1, 2, 1, 4*m+2)
  -- Phase 3: R1, R2 (first unit)
  rw [show (4 * m + 2 : ℕ) = (4 * m + 1) + 1 from by ring]
  step fm; step fm
  -- State: (2, 2*m, 2, 2, 4*m+1)
  -- Phase 4: r112_chain (m rounds)
  rw [show 2 * m = 0 + 2 * m from by ring,
      show 4 * m + 1 = (3 * m + 1) + m from by omega]
  apply stepStar_trans (r112_chain m (b := 0) (c := 2) (d := 2) (e := 3 * m + 1))
  -- State: (2, 0, m+2, 2*m+2, 3*m+1)
  -- Phase 5: R2 chain (m+2 rounds)
  rw [show 2 + m = 0 + (m + 2) from by ring,
      show 2 + 2 * m = 2 * m + 2 from by ring,
      show 3 * m + 1 = (2 * m - 1) + (m + 2) from by omega]
  apply stepStar_trans (r2_chain (m + 2) (a := 2) (c := 0) (d := 2 * m + 2) (e := 2 * m - 1))
  -- State: (2*m+6, 0, 0, 2*m+2, 2*m-1)
  -- Phase 6: R3 chain (2*m+6 steps)
  rw [show 2 + 2 * (m + 2) = 0 + (2 * m + 6) from by ring]
  apply stepStar_trans (a_to_e (2 * m + 6) (a := 0) (d := 2 * m + 2) (e := 2 * m - 1))
  rw [show 2 * m - 1 + (2 * m + 6) = 4 * m + 5 from by omega,
      show 0 + 2 * m + 2 = 2 * m + 2 from by ring]
  finish

-- Even transition: n = 2*m (m >= 1)
-- (0, 0, 0, 2*m, 4*m+1) ⊢⁺ (0, 0, 0, 2*m+1, 4*m+3)
theorem trans_even (m : ℕ) (hm : m ≥ 1) :
    ⟨0, 0, 0, 2 * m, 4 * m + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * m + 1, 4 * m + 3⟩ := by
  -- Phase 1: R4 chain
  rw [show 2 * m = 0 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2 * m) (b := 0) (d := 0) (e := 4 * m + 1))
  rw [show 0 + 2 * m = 2 * m from by ring]
  -- Phase 2: R5 step. State: (0, 2*m, 0, 0, 4*m+1)
  rw [show (4 * m + 1 : ℕ) = 4 * m + 1 from rfl]
  step fm
  -- State: (1, 2*m, 2, 1, 4*m)
  -- Phase 3: R1, R2 (first unit)
  rw [show 2 * m = (2 * m - 1) + 1 from by omega,
      show 4 * m = (4 * m - 1) + 1 from by omega]
  step fm; step fm
  -- State: (2, 2*m-1, 2, 2, 4*m-1)
  -- Phase 4: r112_chain (m-1 rounds)
  rw [show 2 * m - 1 = 1 + 2 * (m - 1) from by omega,
      show 4 * m - 1 = 3 * m + (m - 1) from by omega]
  apply stepStar_trans (r112_chain (m - 1) (b := 1) (c := 2) (d := 2) (e := 3 * m))
  -- State: (2, 1, m+1, 2*m, 3*m)
  rw [show 2 + (m - 1) = m + 1 from by omega,
      show 2 + 2 * (m - 1) = 2 * m from by omega]
  -- Phase 4.5: final R1 (b=1 -> b=0)
  rw [show m + 1 = (m + 1) from rfl]
  step fm
  -- State: (1, 0, m+2, 2*m+1, 3*m)
  rw [show m + 1 + 1 = m + 2 from by ring]
  -- Phase 5: R2 chain (m+2 rounds)
  rw [show m + 2 = 0 + (m + 2) from by ring,
      show 3 * m = (2 * m - 2) + (m + 2) from by omega]
  apply stepStar_trans (r2_chain (m + 2) (a := 1) (c := 0) (d := 2 * m + 1) (e := 2 * m - 2))
  -- State: (2*m+5, 0, 0, 2*m+1, 2*m-2)
  -- Phase 6: R3 chain (2*m+5 steps)
  rw [show 1 + 2 * (m + 2) = 0 + (2 * m + 5) from by ring]
  apply stepStar_trans (a_to_e (2 * m + 5) (a := 0) (d := 2 * m + 1) (e := 2 * m - 2))
  rw [show 2 * m - 2 + (2 * m + 5) = 4 * m + 3 from by omega,
      show 1 + 2 * (m - 1) + 1 + 1 = 2 * m + 1 from by omega,
      show 2 * m - 2 + (m + 2) + (m - 1) + 1 + 3 = 4 * m + 3 from by omega]
  finish

-- Main transition: (0, 0, 0, n+1, 2*n+3) ⊢⁺ (0, 0, 0, n+2, 2*n+5)
theorem main_trans : ∀ n, ⟨0, 0, 0, n + 1, 2 * n + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 2, 2 * n + 5⟩ := by
  intro n
  rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n+1 = 2*m (even)
    rcases m with _ | m
    · omega
    · rw [show n + 1 = 2 * (m + 1) from by omega,
          show 2 * n + 3 = 4 * (m + 1) + 1 from by omega,
          show n + 2 = 2 * (m + 1) + 1 from by omega,
          show 2 * n + 5 = 4 * (m + 1) + 3 from by omega]
      exact trans_even (m + 1) (by omega)
  · -- n+1 = 2*m+1 (odd)
    rcases m with _ | m
    · rw [show n = 0 from by omega]
      exact trans_one
    · rw [show n + 1 = 2 * (m + 1) + 1 from by omega,
          show 2 * n + 3 = 4 * (m + 1) + 3 from by omega,
          show n + 2 = 2 * (m + 1) + 2 from by omega,
          show 2 * n + 5 = 4 * (m + 1) + 5 from by omega]
      exact trans_odd (m + 1) (by omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩)
  · execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 1, 2 * n + 3⟩) 0
  intro n; exists n + 1; exact main_trans n

end Sz22_2003_unofficial_689
