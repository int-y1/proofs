import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #242: [11/105, 4/3, 15/22, 35/2, 9/5]

Vector representation:
```
 0 -1 -1 -1  1
 2 -1  0  0  0
-1  1  1  0 -1
-1  0  1  1  0
 0  2 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_242

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- Helper: rule 2 fires when b>=1, a=0, d=0 (case-split on c for matcher)
theorem step_r2 (b c e : ℕ) : ⟨0, b+1, c, 0, e⟩ [fm]⊢ ⟨2, b, c, 0, e⟩ := by
  unfold fm; rcases c with _ | c <;> rfl

-- Phase 1: rule 4 applied A times
theorem phase1 : ∀ A C D, ⟨A, 0, C, D, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, C + A, D + A, 0⟩ := by
  intro A; induction A with
  | zero => intro C D; simp; exists 0
  | succ A ih =>
    intro C D
    step fm
    apply stepStar_trans (ih (C + 1) (D + 1))
    ring_nf; finish

-- Drain: 3-step loop
theorem drain : ∀ k C D E,
    ⟨0, 0, C + 3 * k, D + 2 * k, E⟩ [fm]⊢* ⟨(0 : ℕ), 0, C, D, E + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro C D E; simp; exists 0
  | succ k ih =>
    intro C D E
    rw [show C + 3 * (k + 1) = (C + 3 * k + 2) + 1 from by ring,
        show D + 2 * (k + 1) = (D + 2 * k + 1) + 1 from by ring]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show C + 3 * k + 2 = (C + 3 * k + 1) + 1 from by ring,
        show (D + 2 * k + 1) + 1 = (D + 2 * k + 1) + 1 from rfl]
    step fm
    rw [show C + 3 * k + 1 = (C + 3 * k) + 1 from by ring,
        show D + 2 * k + 1 = (D + 2 * k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih C D (E + 1 + 1))
    ring_nf; finish

-- Drain ending when D=1
theorem drain_end (C E : ℕ) :
    ⟨0, 0, C + 2, 1, E⟩ [fm]⊢* ⟨(2 : ℕ), 0, C, 0, E + 1⟩ := by
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  exact step_stepStar (step_r2 0 C (E + 1))

-- Pump: rule 3 + rule 2 pairs
theorem pump : ∀ E A C, ⟨A + 2, 0, C, 0, E⟩ [fm]⊢* ⟨A + E + 2, (0 : ℕ), C + E, 0, 0⟩ := by
  intro E; induction E with
  | zero => intro A C; simp; exists 0
  | succ E ih =>
    intro A C
    rw [show A + 2 = (A + 1) + 1 from by ring,
        show E + 1 = E + 1 from rfl]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show C + 1 = C + 1 from rfl]
    step fm
    rw [show A + 1 + 2 = (A + 1) + 2 from by ring]
    apply stepStar_trans (ih (A + 1) (C + 1))
    ring_nf; finish

-- Combined phase 2 + drain end + pump
-- From (0, 0, M+3*N+5, 2*N+3, 0) to (2*N+5, 0, M+2*N+3, 0, 0)
theorem phase2_pump (N M : ℕ) :
    ⟨0, 0, M + 3 * (N + 1) + 2, 1 + 2 * (N + 1), 0⟩ [fm]⊢⁺
    ⟨2 * N + 5, (0 : ℕ), M + 2 * N + 3, 0, 0⟩ := by
  -- Drain N+1 iterations
  rw [show M + 3 * (N + 1) + 2 = (M + 2) + 3 * (N + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (drain (N + 1) (M + 2) 1 0)
  rw [show 0 + 2 * (N + 1) = 2 * N + 2 from by ring]
  -- Drain end: (0, 0, M+2, 1, 2N+2) ->* (2, 0, M, 0, 2N+3)
  apply stepStar_stepPlus_stepPlus (drain_end M (2 * N + 2))
  rw [show 2 * N + 2 + 1 = 2 * N + 3 from by ring]
  -- First step of pump (for stepPlus)
  rw [show (2 : ℕ) = (1 : ℕ) + 1 from by ring,
      show 2 * N + 3 = (2 * N + 2) + 1 from by ring]
  step fm
  -- State: (0, 1, M+1, 0, 2N+2)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- State: (3, 0, M+1, 0, 2N+2)
  rw [show (3 : ℕ) = 1 + 2 from by ring]
  apply stepStar_trans (pump (2 * N + 2) 1 (M + 1))
  ring_nf; finish

-- Main cycle
theorem main_cycle (n m : ℕ) :
    ⟨2*n+3, 0, m+n+2, 0, 0⟩ [fm]⊢⁺ ⟨2*n+5, (0 : ℕ), m+2*n+3, 0, 0⟩ := by
  -- Phase 1: rule 4 applied 2n+3 times
  apply stepStar_stepPlus_stepPlus (phase1 (2*n+3) (m+n+2) 0)
  -- State: (0, 0, m+n+2+(2n+3), 0+(2n+3), 0) = (0, 0, m+3(n+1)+2, 1+2(n+1), 0)
  rw [show m + n + 2 + (2 * n + 3) = m + 3 * (n + 1) + 2 from by ring,
      show 0 + (2 * n + 3) = 1 + 2 * (n + 1) from by ring]
  exact phase2_pump n m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 2, 0, 0⟩) (by execute fm 24)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n m, q = ⟨2*n+3, 0, m+n+2, 0, 0⟩)
  · intro c ⟨n, m, hq⟩; subst hq
    exact ⟨⟨2*n+5, 0, m+2*n+3, 0, 0⟩,
           ⟨n+1, m+n, by ring_nf⟩,
           main_cycle n m⟩
  · exact ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_242
