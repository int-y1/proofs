import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1655: [77/15, 3/154, 25/7, 4/5, 21/2]

Vector representation:
```
 0 -1 -1  1  1
-1  1  0 -1 -1
 0  0  2 -1  0
 2  0 -1  0  0
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1655

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R5/R2 pairs: (2E+4, B, 0, 0, E) -> (4, B+2E, 0, 0, 0)
theorem r5r2_pairs : ∀ E, ∀ B,
    ⟨2 * E + 4, B, 0, 0, E⟩ [fm]⊢* ⟨4, B + 2 * E, 0, 0, 0⟩ := by
  intro E; induction' E with E ih <;> intro B
  · simp; exists 0
  · rw [show 2 * (E + 1) + 4 = (2 * E + 4) + 1 + 1 from by ring,
        show (E + 1 : ℕ) = E + 1 from rfl]
    step fm; step fm
    rw [show B + 2 * (E + 1) = (B + 2) + 2 * E from by ring]
    exact ih (B + 2)

-- Phase 2: 6 steps from (4, B+1, 0, 0, 0) to (1, B+2, 0, 0, 0)
theorem phase2 : ∀ B, ⟨4, B + 1, 0, 0, 0⟩ [fm]⊢* ⟨1, B + 2, 0, 0, 0⟩ := by
  intro B
  step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Phase 3: R5 then R3: (1, B, 0, 0, 0) -> (0, B+1, 2, 0, 0)
theorem phase3 : ⟨1, B, 0, 0, 0⟩ [fm]⊢* ⟨0, B + 1, 2, 0, 0⟩ := by
  step fm; step fm; finish

-- Phase 5a: 2 R1 steps: (0, B+2, 2, 0, 0) -> (0, B, 0, 2, 2)
theorem phase5a : ∀ B, ⟨0, B + 2, 2, 0, 0⟩ [fm]⊢* ⟨0, B, 0, 2, 2⟩ := by
  intro B; step fm; step fm; finish

-- R3/R1/R1 chain: K rounds, using b+2 offset to ensure b >= 2 for R1
-- (0, 2K+B+2, 0, D+1, E) -> (0, B+2, 0, D+K+1, E+2K)
theorem r3r1r1_chain : ∀ K, ∀ B D E,
    ⟨0, 2 * K + (B + 2), 0, D + 1, E⟩ [fm]⊢* ⟨0, B + 2, 0, D + K + 1, E + 2 * K⟩ := by
  intro K; induction' K with K ih <;> intro B D E
  · simp; exists 0
  · rw [show 2 * (K + 1) + (B + 2) = (2 * K + (B + 2) + 1) + 1 from by ring,
        show D + 1 = D + 1 from rfl]
    -- state: (0, (2K+B+2+1)+1, 0, D+1, E)
    -- R3: (0, (2K+B+2+1)+1, 2, D, E)
    step fm
    -- state: (0, (2K+B+2+1)+1, 2, D, E)
    -- rewrite c=2 as 1+1 for R1
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    -- R1: (0, 2K+B+2+1, 1, D+1, E+1)
    step fm
    -- R1: (0, 2K+B+2, 0, D+2, E+2)
    step fm
    rw [show D + (K + 1) + 1 = (D + 1) + K + 1 from by ring,
        show E + 2 * (K + 1) = (E + 2) + 2 * K from by ring,
        show 2 * K + (B + 2) = 2 * K + (B + 2) from rfl]
    exact ih B (D + 1) (E + 2)

-- Phase 5c: 3 steps from (0, 2, 0, D+1, E) to (0, 0, 0, D+2, E+2)
theorem phase5c : ∀ D E, ⟨0, 2, 0, D + 1, E⟩ [fm]⊢* ⟨0, 0, 0, D + 2, E + 2⟩ := by
  intro D E
  step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm; step fm; ring_nf; finish

-- R3 chain: (0, 0, C, D+K, E) -> (0, 0, C+2K, D, E)
theorem r3_chain : ∀ K, ∀ C D E,
    ⟨0, 0, C, D + K, E⟩ [fm]⊢* ⟨0, 0, C + 2 * K, D, E⟩ := by
  intro K; induction' K with K ih <;> intro C D E
  · simp; exists 0
  · rw [show D + (K + 1) = (D + K) + 1 from by ring]
    step fm
    rw [show C + 2 * (K + 1) = (C + 2) + 2 * K from by ring]
    exact ih (C + 2) D E

-- R4 chain: (A, 0, K, 0, E) -> (A+2K, 0, 0, 0, E)
theorem r4_chain : ∀ K, ∀ A E,
    ⟨A, 0, K, 0, E⟩ [fm]⊢* ⟨A + 2 * K, 0, 0, 0, E⟩ := by
  intro K; induction' K with K ih <;> intro A E
  · simp; exists 0
  · rw [show (K + 1 : ℕ) = K + 1 from rfl]
    step fm
    rw [show A + 2 * (K + 1) = (A + 2) + 2 * K from by ring]
    exact ih (A + 2) E

-- Main transition: (2E+6, 0, 0, 0, E+1) ⊢⁺ (4E+12, 0, 0, 0, 2E+4)
theorem main_trans (E : ℕ) :
    ⟨2 * E + 6, 0, 0, 0, E + 1⟩ [fm]⊢⁺ ⟨4 * E + 12, 0, 0, 0, 2 * E + 4⟩ := by
  -- Phase 1: R5/R2 pairs: (2E+6, 0, 0, 0, E+1) -> (4, 2E+2, 0, 0, 0)
  have p1 : ⟨2 * E + 6, 0, 0, 0, E + 1⟩ [fm]⊢* ⟨4, 2 * E + 2, 0, 0, 0⟩ := by
    rw [show 2 * E + 6 = 2 * (E + 1) + 4 from by ring]
    have h := r5r2_pairs (E + 1) 0
    rw [show 0 + 2 * (E + 1) = 2 * E + 2 from by ring] at h
    exact h
  -- Phase 2: (4, 2E+2, 0, 0, 0) -> (1, 2E+3, 0, 0, 0)
  have p2 : ⟨4, 2 * E + 2, 0, 0, 0⟩ [fm]⊢* ⟨1, 2 * E + 3, 0, 0, 0⟩ := by
    rw [show 2 * E + 2 = (2 * E + 1) + 1 from by ring,
        show 2 * E + 3 = (2 * E + 1) + 2 from by ring]
    exact phase2 (2 * E + 1)
  -- Phase 3: (1, 2E+3, 0, 0, 0) -> (0, 2E+4, 2, 0, 0)
  have p3 : ⟨1, 2 * E + 3, 0, 0, 0⟩ [fm]⊢* ⟨0, 2 * E + 4, 2, 0, 0⟩ := phase3
  -- Phase 5a: (0, 2E+4, 2, 0, 0) -> (0, 2E+2, 0, 2, 2)
  have p5a : ⟨0, 2 * E + 4, 2, 0, 0⟩ [fm]⊢* ⟨0, 2 * E + 2, 0, 2, 2⟩ := by
    rw [show 2 * E + 4 = (2 * E + 2) + 2 from by ring]
    exact phase5a (2 * E + 2)
  -- Phase 5b: (0, 2E+2, 0, 2, 2) -> (0, 2, 0, E+2, 2E+2)
  -- r3r1r1_chain with K=E, B=0, D=1, E_param=2
  -- source: (0, 2E+(0+2), 0, 1+1, 2)
  -- target: (0, 0+2, 0, 1+E+1, 2+2E)
  have p5b : ⟨0, 2 * E + 2, 0, 2, 2⟩ [fm]⊢* ⟨0, 2, 0, E + 2, 2 * E + 2⟩ := by
    have h := r3r1r1_chain E 0 1 2
    rw [show 2 * E + (0 + 2) = 2 * E + 2 from by ring,
        show 1 + 1 = 2 from by ring,
        show 1 + E + 1 = E + 2 from by ring,
        show 2 + 2 * E = 2 * E + 2 from by ring] at h
    exact h
  -- Phase 5c: (0, 2, 0, E+2, 2E+2) -> (0, 0, 0, E+3, 2E+4)
  have p5c' : ⟨0, 2, 0, E + 2, 2 * E + 2⟩ [fm]⊢* ⟨0, 0, 0, E + 3, 2 * E + 4⟩ := by
    rw [show E + 2 = (E + 1) + 1 from by ring]
    have h := phase5c (E + 1) (2 * E + 2)
    rw [show (E + 1) + 2 = E + 3 from by ring,
        show 2 * E + 2 + 2 = 2 * E + 4 from by ring] at h
    exact h
  -- Phase 6: R3 chain: (0, 0, 0, E+3, 2E+4) -> (0, 0, 2E+6, 0, 2E+4)
  have p6 : ⟨0, 0, 0, E + 3, 2 * E + 4⟩ [fm]⊢* ⟨0, 0, 2 * E + 6, 0, 2 * E + 4⟩ := by
    rw [show E + 3 = 0 + (E + 3) from by ring]
    have h := r3_chain (E + 3) 0 0 (2 * E + 4)
    rw [show 0 + 2 * (E + 3) = 2 * E + 6 from by ring] at h
    exact h
  -- Phase 7: R4 chain: (0, 0, 2E+6, 0, 2E+4) -> (4E+12, 0, 0, 0, 2E+4)
  have p7 : ⟨0, 0, 2 * E + 6, 0, 2 * E + 4⟩ [fm]⊢* ⟨4 * E + 12, 0, 0, 0, 2 * E + 4⟩ := by
    have h := r4_chain (2 * E + 6) 0 (2 * E + 4)
    rw [show 0 + 2 * (2 * E + 6) = 4 * E + 12 from by ring] at h
    exact h
  have pall : ⟨2 * E + 6, 0, 0, 0, E + 1⟩ [fm]⊢* ⟨4 * E + 12, 0, 0, 0, 2 * E + 4⟩ :=
    stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p5a
      (stepStar_trans p5b (stepStar_trans p5c' (stepStar_trans p6 p7))))))
  exact stepStar_stepPlus pall (by simp [Q]; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨6, 0, 0, 0, 1⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun E ↦ ⟨2 * E + 6, 0, 0, 0, E + 1⟩) 0
  intro E
  refine ⟨2 * E + 3, ?_⟩
  show ⟨2 * E + 6, 0, 0, 0, E + 1⟩ [fm]⊢⁺ ⟨2 * (2 * E + 3) + 6, 0, 0, 0, (2 * E + 3) + 1⟩
  rw [show 2 * (2 * E + 3) + 6 = 4 * E + 12 from by ring,
      show (2 * E + 3) + 1 = 2 * E + 4 from by ring]
  exact main_trans E

end Sz22_2003_unofficial_1655
