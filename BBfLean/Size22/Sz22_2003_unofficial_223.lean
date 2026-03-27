import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #223: [105/2, 1/363, 2/39, 1859/5, 3/77]

Vector representation:
```
-1  1  1  1  0  0
 0 -1  0  0 -2  0
 1 -1  0  0  0 -1
 0  0 -1  0  1  2
 0  1  0 -1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_223

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c+1, d+1, e, f⟩
  | ⟨a, b+1, c, d, e+2, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+2⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

-- R3/R1 loop: (0,1,C,D,0,F) →* (0,1,C+F,D+F,0,0)
theorem r3r1_loop : ∀ F C D, ⟨0, 1, C, D, 0, F⟩ [fm]⊢* ⟨0, 1, C + F, D + F, 0, 0⟩ := by
  intro F; induction F with
  | zero => intro C D; exists 0
  | succ F ih =>
    intro C D
    step fm; step fm
    apply stepStar_trans (ih (C + 1) (D + 1))
    ring_nf; finish

-- R4 drain: (0,0,C,D,E,F) →* (0,0,0,D,E+C,F+2*C)
theorem r4_drain : ∀ C D E F, ⟨0, 0, C, D, E, F⟩ [fm]⊢* ⟨0, 0, 0, D, E + C, F + 2 * C⟩ := by
  intro C; induction C with
  | zero => intro D E F; simp; exists 0
  | succ C ih =>
    intro D E F
    step fm
    apply stepStar_trans (ih D (E + 1) (F + 2))
    ring_nf; finish

-- R5/R2 drain: (0,0,0,D+K,3*K+1,F) →* (0,0,0,D,1,F)
theorem r5r2_drain : ∀ K D F, ⟨0, 0, 0, D + K, 3 * K + 1, F⟩ [fm]⊢* ⟨0, 0, 0, D, 1, F⟩ := by
  intro K; induction K with
  | zero => intro D F; simp; exists 0
  | succ K ih =>
    intro D F
    rw [show D + (K + 1) = (D + K) + 1 from by ring,
        show 3 * (K + 1) + 1 = (3 * K + 1) + 2 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih D F)
    finish

-- Full cycle: (0,0,0,2*N+1,1,3*N+1) →* (0,0,0,4*N+3,1,6*N+4)
theorem full_cycle (N : ℕ) : ⟨0, 0, 0, 2 * N + 1, 1, 3 * N + 1⟩ [fm]⊢* ⟨0, 0, 0, 4 * N + 3, 1, 6 * N + 4⟩ := by
  -- Phase 1 (R5): (0,0,0,2N+1,1,3N+1) -> (0,1,0,2N,0,3N+1)
  rw [show 2 * N + 1 = 2 * N + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- Phase 2 (R3/R1 loop): (0,1,0,2N,0,3N+1) -> (0,1,3N+1,5N+1,0,0)
  apply stepStar_trans (r3r1_loop (3 * N + 1) 0 (2 * N))
  rw [show 0 + (3 * N + 1) = 3 * N + 1 from by ring,
      show 2 * N + (3 * N + 1) = 5 * N + 1 from by ring]
  -- Phase 3 (middle 7 steps): (0,1,3N+1,5N+1,0,0) -> (0,0,3N+1,5N+3,0,2)
  rw [show 3 * N + 1 = 3 * N + 1 from rfl,
      show 5 * N + 1 = 5 * N + 1 from rfl]
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  -- Phase 4 (R4 drain): (0,0,3N+1,5N+3,0,2) -> (0,0,0,5N+3,3N+1,6N+4)
  apply stepStar_trans (r4_drain (3 * N + 1) (5 * N + 3) 0 2)
  rw [show 0 + (3 * N + 1) = 3 * N + 1 from by ring,
      show 2 + 2 * (3 * N + 1) = 6 * N + 4 from by ring]
  -- Phase 5 (R5/R2 drain): (0,0,0,5N+3,3N+1,6N+4) -> (0,0,0,4N+3,1,6N+4)
  rw [show 5 * N + 3 = (4 * N + 3) + N from by ring,
      show 3 * N + 1 = 3 * N + 1 from rfl]
  exact r5r2_drain N (4 * N + 3) (6 * N + 4)

-- Promote to stepPlus
theorem main_trans (N : ℕ) : ⟨0, 0, 0, 2 * N + 1, 1, 3 * N + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * N + 3, 1, 6 * N + 4⟩ :=
  stepStar_stepPlus (full_cycle N) (by
    intro heq
    have h := congr_arg (fun q : Q => q.2.2.2.2.2) heq
    simp only at h
    omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 1, 4⟩) (by unfold c₀; execute fm 9)
  show ¬halts fm (⟨0, 0, 0, 2 * 1 + 1, 1, 3 * 1 + 1⟩ : Q)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun N ↦ ⟨0, 0, 0, 2 * N + 1, 1, 3 * N + 1⟩) 1
  intro N
  refine ⟨2 * N + 1, ?_⟩
  show ⟨0, 0, 0, 2 * N + 1, 1, 3 * N + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * (2 * N + 1) + 1, 1, 3 * (2 * N + 1) + 1⟩
  rw [show 2 * (2 * N + 1) + 1 = 4 * N + 3 from by ring,
      show 3 * (2 * N + 1) + 1 = 6 * N + 4 from by ring]
  exact main_trans N

end Sz22_2003_unofficial_223
