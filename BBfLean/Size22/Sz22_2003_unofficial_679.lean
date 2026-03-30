import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #679: [35/6, 3025/2, 4/77, 3/5, 2/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  2  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_679

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R3R2R2 chain: each round applies R3 then R2 twice.
theorem r3r2r2_chain : ∀ n c e, ⟨0, 0, c, n, e + 1⟩ [fm]⊢* ⟨0, 0, c + 4 * n, 0, e + 1 + 3 * n⟩ := by
  intro n; induction' n with n ih <;> intro c e
  · exists 0
  · step fm; step fm; step fm
    rw [show e + 4 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (c + 4) (e + 3))
    ring_nf; finish

-- R4 chain: move c to b.
theorem c_to_b : ∀ n b e, ⟨0, b, n, 0, e⟩ [fm]⊢* ⟨0, b + n, 0, 0, e⟩ := by
  intro n; induction' n with n ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- R3R1R1 chain: each round applies R3 then R1 twice.
theorem r3r1r1_chain : ∀ n b c d e, ⟨0, b + 2 * n, c, d + 1, e + n⟩ [fm]⊢* ⟨0, b, c + 2 * n, d + 1 + n, e⟩ := by
  intro n; induction' n with n ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (n + 1) = (b + 2 * n) + 2 from by ring,
        show e + (n + 1) = (e + n) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih b (c + 2) (d + 1) e)
    ring_nf; finish

-- Spiral: from (0, 2*K+1, 1, 1, K+1) to (1, 0, 2*(K+1), K+1, 0).
theorem spiral : ∀ K, ⟨0, 2 * K + 1, 1, 1, K + 1⟩ [fm]⊢* ⟨1, 0, 2 * (K + 1), K + 1, 0⟩ := by
  intro K; rcases K with _ | K
  · step fm; step fm; finish
  · rw [show 2 * (K + 1) + 1 = 3 + 2 * K from by ring,
        show (K + 1 : ℕ) + 1 = 2 + K from by ring]
    apply stepStar_trans (r3r1r1_chain K 3 1 0 2)
    rw [show 1 + 2 * K = 2 * K + 1 from by ring,
        show 0 + 1 + K = K + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm
    ring_nf; finish

-- Main transition: (1, 0, 2*D, D, 0) ->+ (1, 0, 2*(3*D+1), 3*D+1, 0).
theorem main_transition : ∀ D, ⟨1, 0, 2 * D, D, 0⟩ [fm]⊢⁺ ⟨1, 0, 2 * (3 * D + 1), 3 * D + 1, 0⟩ := by
  intro D
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain D (2 * D + 2) 1)
  rw [show 2 * D + 2 + 4 * D = 6 * D + 2 from by ring,
      show 1 + 1 + 3 * D = 3 * D + 2 from by ring]
  apply stepStar_trans (c_to_b (6 * D + 2) 0 (3 * D + 2))
  rw [show 0 + (6 * D + 2) = 6 * D + 2 from by ring,
      show (3 * D + 2 : ℕ) = (3 * D + 1) + 1 from by ring]
  step fm
  rw [show (6 * D + 2 : ℕ) = (6 * D + 1) + 1 from by ring]
  step fm
  rw [show 6 * D + 1 = 2 * (3 * D) + 1 from by ring,
      show 3 * D + 1 = 3 * D + 1 from rfl]
  apply stepStar_trans (spiral (3 * D))
  rw [show 2 * (3 * D + 1) = 2 * (3 * D + 1) from rfl]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 2, 1, 0⟩)
  · execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun D ↦ ⟨1, 0, 2 * D, D, 0⟩) 1
  intro D
  exact ⟨3 * D + 1, main_transition D⟩

end Sz22_2003_unofficial_679
