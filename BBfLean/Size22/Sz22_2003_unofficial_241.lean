import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #241: [11/105, 4/3, 15/22, 35/2, 33/5]

Vector representation:
```
 0 -1 -1 -1  1
 2 -1  0  0  0
-1  1  1  0 -1
-1  0  1  1  0
 0  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_241

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: (a+k, 0, c, d, 0) ->* (a, 0, c+k, d+k, 0)
theorem r4_chain : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d+k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (d + 1))
    ring_nf; finish

-- R5/R1 drain: (0, 0, 2k+1, k+1, e) ->* (0, 1, 0, 1, e+2k+1)
theorem r5r1_drain : ∀ k e, ⟨0, 0, 2*k+1, k+1, e⟩ [fm]⊢* ⟨0, 1, 0, 1, e+2*k+1⟩ := by
  intro k; induction k with
  | zero =>
    intro e
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    ring_nf; finish
  | succ k ih =>
    intro e
    rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show (k + 1) + 1 = (k + 1) + 1 from rfl]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring,
        show (k + 1) + 1 = k + 1 + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e + 1 + 1))
    ring_nf; finish

-- Phase 3: (0, 1, 0, 1, E+1) ->* (1, 0, 0, 0, E+1)
theorem phase3 : ∀ E, ⟨0, 1, 0, 1, E+1⟩ [fm]⊢* ⟨1, 0, 0, 0, E+1⟩ := by
  intro E
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show E + 1 = E + 1 from rfl]
  step fm
  step fm
  finish

-- R3/R2 pump: (a+1, 0, c, 0, e+k) ->* (a+k+1, 0, c+k, 0, e)
theorem r3r2_pump : ∀ k a c e, ⟨a+1, 0, c, 0, e+k⟩ [fm]⊢* ⟨a+k+1, 0, c+k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (c + 1) e)
    ring_nf; finish

-- Main transition: (N+1, 0, N, 0, 0) ->+ (2N+2, 0, 2N+1, 0, 0)
theorem main_trans (N : ℕ) : ⟨N+1, 0, N, 0, 0⟩ [fm]⊢⁺ ⟨2*N+2, 0, 2*N+1, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2*N+1, N+1, 0⟩)
  · have h := r4_chain (N+1) 0 N 0
    simp only [show N + (N + 1) = 2 * N + 1 from by ring,
               show 0 + (N + 1) = N + 1 from by omega] at h
    exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, 0, 1, 2*N+1⟩)
  · have h := r5r1_drain N 0
    simp only [Nat.zero_add] at h; exact h
  rw [show 2 * N + 1 = (2 * N) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (phase3 (2 * N))
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * N + 1 = (2 * N) + 1 from by ring]
  step fm
  step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show 2 * N = 0 + 2 * N from by omega]
  apply stepStar_trans (r3r2_pump (2 * N) 1 1 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, n, 0, 0⟩) 0
  intro n
  exact ⟨2 * n + 1, main_trans n⟩

end Sz22_2003_unofficial_241
