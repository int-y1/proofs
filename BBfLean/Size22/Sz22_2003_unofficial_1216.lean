import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1216: [5/6, 539/2, 44/35, 3/11, 55/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  1
 0  1  0  0 -1
 0  0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1216

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 chain: (0, b, 0, d, k) →* (0, b+k, 0, d, 0)
theorem e_to_b : ∀ k b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- R3R1R1 chain: (0, b+2k, c+1, d+k, e) →* (0, b, c+k+1, d, e+k)
theorem r3r1r1_chain : ∀ k b c d e, ⟨0, b + 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨0, b, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    -- State: (0, b+2, c+k+1, d+1, e+k)
    rw [show c + k + 1 = (c + k) + 1 from by ring]
    step fm
    -- State: (2, b+2, c+k, d, e+k+1)
    rw [show b + 2 = (b + 1) + 1 from by ring]
    step fm
    -- State: (1, b+1, c+k+1, d, e+k+1)
    step fm
    -- State: (0, b, c+k+2, d, e+k+1)
    rw [show c + (k + 1) + 1 = c + k + 2 from by ring]
    finish

-- R3R2R2 chain: (0, 0, c+k, d+1, e) →* (0, 0, c, d+1+3*k, e+3*k)
theorem r3r2r2_chain : ∀ k c d e, ⟨0, 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 1 + 3 * k, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 3))
    ring_nf; finish

-- Main transition: (0, 0, 0, n+e+5, 2*e+6) →⁺ (0, 0, 0, n+3*e+13, 4*e+16)
theorem main_trans (n e : ℕ) :
    ⟨(0 : ℕ), 0, 0, n + e + 5, 2 * e + 6⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, n + 3 * e + 13, 4 * e + 16⟩ := by
  -- R4 step to establish ⊢⁺
  rw [show 2 * e + 6 = (2 * e + 5) + 1 from by ring]
  step fm
  -- State: (0, 1, 0, n+e+5, 2*e+5)
  -- Remaining R4 steps
  apply stepStar_trans (e_to_b (2 * e + 5) 1 (n + e + 5))
  rw [show 1 + (2 * e + 5) = 2 * e + 6 from by ring]
  -- State: (0, 2*e+6, 0, n+e+5, 0)
  -- R5
  rw [show n + e + 5 = (n + e + 4) + 1 from by ring]
  step fm
  -- State: (0, 2*e+6, 1, n+e+4, 1)
  -- R3R1R1 chain (e+3 rounds)
  rw [show 2 * e + 6 = 0 + 2 * (e + 3) from by ring,
      show n + e + 4 = (n + 1) + (e + 3) from by ring]
  apply stepStar_trans (r3r1r1_chain (e + 3) 0 0 (n + 1) 1)
  rw [show 0 + (e + 3) + 1 = 0 + (e + 4) from by ring,
      show 1 + (e + 3) = e + 4 from by ring]
  -- State: (0, 0, 0+(e+4), n+1, e+4)
  -- R3R2R2 chain (e+4 rounds)
  apply stepStar_trans (r3r2r2_chain (e + 4) 0 n (e + 4))
  rw [show n + 1 + 3 * (e + 4) = n + 3 * e + 13 from by ring,
      show e + 4 + 3 * (e + 4) = 4 * e + 16 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 6⟩)
  · execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨0, 0, 0, n + e + 5, 2 * e + 6⟩) ⟨0, 0⟩
  intro ⟨n, e⟩
  refine ⟨⟨n + e + 3, 2 * e + 5⟩, ?_⟩
  show ⟨(0 : ℕ), 0, 0, n + e + 5, 2 * e + 6⟩ [fm]⊢⁺
    ⟨0, 0, 0, (n + e + 3) + (2 * e + 5) + 5, 2 * (2 * e + 5) + 6⟩
  rw [show (n + e + 3) + (2 * e + 5) + 5 = n + 3 * e + 13 from by ring,
      show 2 * (2 * e + 5) + 6 = 4 * e + 16 from by ring]
  exact main_trans n e

end Sz22_2003_unofficial_1216
