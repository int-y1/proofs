import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #408: [25/18, 49/2, 22/35, 3/11, 25/7]

Vector representation:
```
-1 -2  2  0  0
-1  0  0  2  0
 1  0 -1 -1  1
 0  1  0  0 -1
 0  0  2 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_408

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

-- R2/R3 pairs: (1, 0, k, d, e) ->* (1, 0, 0, d+k, e+k)
theorem r2r3_loop : ∀ k d e, ⟨1, 0, k, d, e⟩ [fm]⊢* ⟨1, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · simp; exists 0
  · step fm; step fm
    apply stepStar_trans (ih (d + 1) (e + 1))
    rw [show d + 1 + k = d + (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]
    finish

-- R4 repeated: (0, b, 0, d, k) ->* (0, b+k, 0, d, 0)
theorem e_to_b : ∀ k b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d)
    rw [show b + 1 + k = b + (k + 1) from by ring]
    finish

-- R1/R3 pairs: (1, 2k+b, c, k+d, e) ->* (1, b, c+k, d, e+k)
theorem r1r3_loop : ∀ k b c d e,
    ⟨1, 2 * k + b, c, k + d, e⟩ [fm]⊢* ⟨1, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · simp; exists 0
  · rw [show 2 * (k + 1) + b = (2 * k + b) + 2 from by ring,
        show (k + 1) + d = (k + d) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    rw [show c + 1 + k = c + (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]
    finish

-- Main cycle: (1, 0, n, 0, n) ->+ (1, 0, n+1, 0, n+1)
theorem main_cycle (n : ℕ) :
    ⟨1, 0, n, 0, n⟩ [fm]⊢⁺ ⟨1, 0, n + 1, 0, n + 1⟩ := by
  -- Phase 1: R2/R3 pairs then final R2
  apply stepStar_stepPlus_stepPlus
  · exact r2r3_loop n 0 n
  step fm
  -- Now at (0, 0, 0, 0+n+2, n+n)
  show (⟨0, 0, 0, 0 + n + 2, n + n⟩ : Q) [fm]⊢* ⟨1, 0, n + 1, 0, n + 1⟩
  -- Phase 2: R4 repeated
  apply stepStar_trans
  · have h := e_to_b (n + n) 0 (n + 2)
    rw [show 0 + (n + n) = n + n from by ring] at h
    rw [show 0 + n + 2 = n + 2 from by ring]
    exact h
  -- Now at (0, n+n, 0, n+2, 0)
  -- Phase 3: R5, R3, then n R1/R3 pairs
  step fm; step fm
  show (⟨1, n + n, 1, n, 1⟩ : Q) [fm]⊢* ⟨1, 0, n + 1, 0, n + 1⟩
  apply stepStar_trans
  · have h := r1r3_loop n 0 1 0 1
    rw [show 2 * n + 0 = n + n from by ring, show n + 0 = n from by ring] at h
    exact h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 2, 0, 2⟩) (by execute fm 12)
  refine progress_nonhalt_simple (fm := fm)
    (fun n ↦ (⟨1, 0, n + 2, 0, n + 2⟩ : Q)) 0 (fun n ↦ ?_)
  exact ⟨n + 1, main_cycle (n + 2)⟩

end Sz22_2003_unofficial_408
