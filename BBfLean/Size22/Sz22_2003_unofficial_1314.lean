import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1314: [63/10, 1331/2, 2/33, 5/7, 21/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  3
 1 -1  0  0 -1
 0  0  1 -1  0
 0  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1314

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: move d to c. (0, 0, c, k, e) →* (0, 0, c+k, 0, e)
theorem d_to_c : ∀ k c e, ⟨(0 : ℕ), (0 : ℕ), c, k, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + k, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e)
    rw [show c + 1 + k = c + (k + 1) from by ring]
    finish

-- R3+R1 chain: k rounds. (0, b+1, k, d, e+k) →* (0, b+k+1, 0, d+k, e)
theorem r3r1_chain : ∀ k b d e, ⟨(0 : ℕ), b + 1, k, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k + 1, (0 : ℕ), d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R3: (1, b, k+1, d, e+k)
    step fm  -- R1: (0, b+2, k, d+1, e+k)
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 1) (d + 1) e)
    rw [show b + 1 + k + 1 = b + (k + 1) + 1 from by ring,
        show d + 1 + k = d + (k + 1) from by ring]
    finish

-- R3+R2 chain: k rounds. (0, k, 0, d, f+k) →* (0, 0, 0, d, f+3*k)
theorem r3r2_chain : ∀ k d f, ⟨(0 : ℕ), k, (0 : ℕ), d, f + k⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d, f + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro d f
  · exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm  -- R3: (1, k, 0, d, f+k)
    step fm  -- R2: (0, k, 0, d, f+k+3)
    rw [show f + k + 3 = (f + 3) + k from by ring]
    apply stepStar_trans (ih d (f + 3))
    ring_nf; finish

-- Main transition: (0, 0, 0, n, e) →⁺ (0, 0, 0, n+1, e+n+1)
-- Requires: e ≥ 2*n + 2 (for d=0 case: e ≥ 2 suffices, for d≥1 case: e ≥ 2*n+2)
theorem main_trans (n : ℕ) (e : ℕ) (he : e ≥ 2 * n + 2) :
    ⟨(0 : ℕ), (0 : ℕ), 0, n, e⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 0, n + 1, e + n + 1⟩ := by
  rcases n with _ | n
  · -- n = 0: R5, R3, R2
    rw [show e = (e - 1) + 1 from by omega]
    step fm  -- R5: (0, 1, 0, 1, e-1)
    rw [show e - 1 = (e - 2) + 1 from by omega]
    step fm  -- R3: (1, 0, 0, 1, e-2)
    step fm  -- R2: (0, 0, 0, 1, e+1)
    rw [show e - 2 + 3 = e + 0 + 1 from by omega]
    finish
  · -- n = n+1 ≥ 1
    obtain ⟨f, hf⟩ : ∃ f, e = f + 2 * n + 4 := ⟨e - 2 * n - 4, by omega⟩
    subst hf
    -- Phase 1: R4 chain
    apply stepStar_stepPlus_stepPlus (d_to_c (n + 1) 0 (f + 2 * n + 4))
    rw [show 0 + (n + 1) = n + 1 from by ring]
    -- State: (0, 0, n+1, 0, f+2n+4)
    -- Phase 2: R5 step
    rw [show f + 2 * n + 4 = (f + 2 * n + 3) + 1 from by ring]
    step fm  -- R5: (0, 1, n+1, 1, f+2n+3)
    -- Phase 3: R3+R1 chain (n+1 rounds)
    rw [show f + 2 * n + 3 = (f + n + 2) + (n + 1) from by ring]
    apply stepStar_trans (r3r1_chain (n + 1) 0 1 (f + n + 2))
    rw [show 0 + (n + 1) + 1 = n + 2 from by ring,
        show 1 + (n + 1) = n + 2 from by ring]
    -- State: (0, n+2, 0, n+2, f+n+2)
    -- Phase 4: R3+R2 chain (n+2 rounds)
    rw [show f + n + 2 = f + (n + 2) from by ring]
    apply stepStar_trans (r3r2_chain (n + 2) (n + 2) f)
    ring_nf; finish

-- Triangular number
def tri : ℕ → ℕ
  | 0 => 0
  | n + 1 => tri n + n + 1

theorem tri_bound : ∀ n, tri n + 1 ≥ 2 * n := by
  intro n; induction' n with n ih
  · omega
  · simp only [tri]; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 3⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n, tri n + 3⟩) 0
  intro n; refine ⟨n + 1, ?_⟩
  rw [show tri (n + 1) + 3 = (tri n + 3) + n + 1 from by simp [tri]; ring]
  exact main_trans n (tri n + 3) (by have := tri_bound n; omega)

end Sz22_2003_unofficial_1314
