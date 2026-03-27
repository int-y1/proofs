import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #369: [2/15, 7/3, 99/2, 125/77, 3/35]

Vector representation:
```
 1 -1 -1  0  0
 0 -1  0  1  0
-1  2  0  0  1
 0  0  3 -1 -1
 0  1 -1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_369

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1: Rule 4 loop: (0,0,c,d+k,e+k) ⊢* (0,0,c+3*k,d,e)
theorem rule4_loop : ∀ k c d e,
    ⟨0, 0, c, d + k, e + k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + 3 * k, d, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase 3: Eating loop: (a, 2, c+2*k, 0, e) ⊢* (a+k, 2, c, 0, e+k)
theorem eat_loop : ∀ k a c e,
    ⟨a, 2, c + 2 * k, 0, e⟩ [fm]⊢* ⟨a + k, (2 : ℕ), c, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    -- Rule 1: (a, 2, C+1+1, 0, E) = (a, 1+1, (C+1)+1, 0, E) -> (a+1, 1, C+1, 0, E)
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    -- Rule 1: (a+1, 1, C+1, 0, E) = (a+1, 0+1, C+1, 0, E) -> (a+2, 0, C, 0, E)
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]
    step fm
    -- Rule 3: (a+2, 0, C, 0, E) = ((a+1)+1, 0, C, 0, E) -> (a+1, 2, C, 0, E+1)
    rw [show a + 1 + 1 = (a + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase 4: Drain loop: (a+k, 2, 0, d, e) ⊢* (a, 2, 0, d+2*k, e+k)
theorem drain_loop : ∀ k a d e,
    ⟨a + k, 2, 0, d, e⟩ [fm]⊢* ⟨a, (2 : ℕ), 0, d + 2 * k, e + k⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    -- Rule 3: ((a+k)+1, 2, 0, d, e) -> but wait, rule 2 fires first since b≥1
    -- Actually: b=2≥1 and c=0, so rule 2 fires: (A, b+1, c, d, e) -> (A, b, c, d+1, e)
    -- (A, 2, 0, d, e) = (A, 1+1, 0, d, e) -> (A, 1, 0, d+1, e)
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    -- (A, 1, 0, d+1, e) = (A, 0+1, 0, d+1, e) -> (A, 0, 0, d+2, e)
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    -- (A, 0, 0, d+2, e) = ((a+k)+1, 0, 0, d+2, e) -> rule 3 -> (a+k, 2, 0, d+2, e+1)
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Even case: (0, 2, 2*M, 0, 1) ⊢* (0, 0, 0, 2*M+2, 2*M+1)
theorem phase_even (M : ℕ) :
    ⟨0, 2, 2 * M, 0, 1⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, 2 * M + 2, 2 * M + 1⟩ := by
  -- eat M rounds: (0, 2, 2*M, 0, 1) -> (M, 2, 0, 0, M+1)
  apply stepStar_trans (c₂ := ⟨M, 2, 0, 0, M + 1⟩)
  · have h := eat_loop M 0 0 1
    simp only [Nat.zero_add] at h
    rw [show 1 + M = M + 1 from by ring] at h; exact h
  -- drain M rounds: (M, 2, 0, 0, M+1) -> (0, 2, 0, 2*M, 2*M+1)
  apply stepStar_trans (c₂ := ⟨0, 2, 0, 2 * M, 2 * M + 1⟩)
  · have h := drain_loop M 0 0 (M + 1)
    simp only [Nat.zero_add] at h
    rw [show M + 1 + M = 2 * M + 1 from by ring] at h
    exact h
  -- Final 2 steps: (0, 2, 0, 2*M, 2*M+1) -> (0, 0, 0, 2*M+2, 2*M+1)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  finish

-- Odd case: (0, 2, 2*M+1, 0, 1) ⊢* (0, 0, 0, 2*M+3, 2*M+2)
theorem phase_odd (M : ℕ) :
    ⟨0, 2, 2 * M + 1, 0, 1⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, 2 * M + 3, 2 * M + 2⟩ := by
  -- eat M rounds: (0, 2, 2*M+1, 0, 1) -> (M, 2, 1, 0, M+1)
  apply stepStar_trans (c₂ := ⟨M, 2, 1, 0, M + 1⟩)
  · have h := eat_loop M 0 1 1
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * M = 2 * M + 1 from by ring,
        show 1 + M = M + 1 from by ring] at h
    exact h
  -- 3 extra steps: (M, 2, 1, 0, M+1) -> (M, 2, 0, 1, M+2)
  -- Rule 1: (M, 2, 1, 0, M+1) = (M, 1+1, 0+1, 0, M+1) -> (M+1, 1, 0, 0, M+1)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- Rule 2: (M+1, 1, 0, 0, M+1) = (M+1, 0+1, 0, 0, M+1) -> (M+1, 0, 0, 1, M+1)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  step fm
  -- drain M rounds: (M, 2, 0, 1, M+2) -> (0, 2, 0, 2*M+1, 2*M+2)
  apply stepStar_trans (c₂ := ⟨0, 2, 0, 2 * M + 1, 2 * M + 2⟩)
  · have h := drain_loop M 0 1 (M + 2)
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * M = 2 * M + 1 from by ring,
        show M + 2 + M = 2 * M + 2 from by ring] at h
    exact h
  -- Final 2 steps: (0, 2, 0, 2*M+1, 2*M+2) -> (0, 0, 0, 2*M+3, 2*M+2)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  finish

-- Main transition: (0, 0, 0, N+2, N+1) ⊢⁺ (0, 0, 0, 3*N+3, 3*N+2)
theorem main_trans (N : ℕ) :
    ⟨0, 0, 0, N + 2, N + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * N + 3, 3 * N + 2⟩ := by
  -- Phase 1: rule4 loop N+1 times: (0,0,0,N+2,N+1) -> (0,0,3*N+3,1,0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3 * N + 3, 1, 0⟩)
  · have h := rule4_loop (N + 1) 0 1 0
    simp only [Nat.zero_add] at h
    rw [show 1 + (N + 1) = N + 2 from by ring] at h
    rw [show 3 * (N + 1) = 3 * N + 3 from by ring] at h
    exact h
  -- Phase 2-4: (0,0,3*N+3,1,0) -> (0,1,3*N+2,0,0) -> (1,0,3*N+1,0,0) -> (0,2,3*N+1,0,1)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 3 * N + 2, 0, 0⟩)
  · rw [show 3 * N + 3 = (3 * N + 2) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]; simp [fm]
  apply stepStar_trans (c₂ := ⟨1, 0, 3 * N + 1, 0, 0⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 3 * N + 2 = (3 * N + 1) + 1 from by ring]
    step fm; finish
  apply stepStar_trans (c₂ := ⟨0, 2, 3 * N + 1, 0, 1⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm; finish
  -- Now at (0, 2, 3*N+1, 0, 1). Split on parity of N.
  rcases Nat.even_or_odd N with ⟨J, hJ⟩ | ⟨J, hJ⟩
  · -- N = 2*J, so 3*N+1 = 2*(3*J) + 1 (odd)
    rw [show 3 * N + 1 = 2 * (3 * J) + 1 from by omega]
    apply stepStar_trans (phase_odd (3 * J))
    rw [show 2 * (3 * J) + 3 = 3 * N + 3 from by omega,
        show 2 * (3 * J) + 2 = 3 * N + 2 from by omega]
    finish
  · -- N = 2*J+1, so 3*N+1 = 2*(3*J+2) (even)
    rw [show 3 * N + 1 = 2 * (3 * J + 2) from by omega]
    apply stepStar_trans (phase_even (3 * J + 2))
    rw [show 2 * (3 * J + 2) + 2 = 3 * N + 3 from by omega,
        show 2 * (3 * J + 2) + 1 = 3 * N + 2 from by omega]
    finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun N ↦ ⟨0, 0, 0, N + 2, N + 1⟩) 0
  intro N
  exact ⟨3 * N + 1, main_trans N⟩

end Sz22_2003_unofficial_369
