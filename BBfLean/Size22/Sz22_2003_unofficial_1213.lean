import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1213: [5/6, 539/2, 44/35, 3/11, 22/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  1
 0  1  0  0 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1213

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R4 chain: (0, b, 0, d, e+k) →* (0, b+k, 0, d, e)
theorem r4_chain : ∀ k b d e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R1R1R3 chain: (2, 2k+r, c, D+k, E) →* (2, r, c+k, D, E+k)
theorem r1r1r3_chain : ∀ k r c D E, ⟨2, 2 * k + r, c, D + k, E⟩ [fm]⊢* ⟨2, r, c + k, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro r c D E
  · simp; exists 0
  · rw [show 2 * (k + 1) + r = 2 * k + (r + 2) from by ring,
        show D + (k + 1) = (D + 1) + k from by ring]
    apply stepStar_trans (ih (r + 2) c (D + 1) E)
    rw [show r + 2 = (r + 1) + 1 from by ring]
    step fm
    step fm
    rw [show c + k + 1 = c + (k + 1) from by ring]
    step fm
    ring_nf; finish

-- R3R2R2 chain: (0, 0, c+k, d+1, e) →* (0, 0, c, d+1+3k, e+3k)
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

-- Main transition: (0, 0, 0, 2a+n+4, 2a+2n+4) →⁺ (0, 0, 0, 4a+3n+9, 4a+4n+10)
theorem main_trans (a n : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * a + n + 4, 2 * a + 2 * n + 4⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 4 * a + 3 * n + 9, 4 * a + 4 * n + 10⟩ := by
  -- Phase 1: first R4 step for ⊢⁺
  rw [show 2 * a + 2 * n + 4 = 0 + (2 * a + 2 * n + 4) from by ring]
  step fm
  -- Remaining R4 chain
  apply stepStar_trans (r4_chain (2 * a + 2 * n + 3) 1 (2 * a + n + 4) 0)
  rw [show 1 + (2 * a + 2 * n + 3) = 2 * a + 2 * n + 4 from by ring]
  -- State: (0, 2a+2n+4, 0, 2a+n+4, 0)
  -- R5
  rw [show 2 * a + n + 4 = (2 * a + n + 3) + 1 from by ring]
  step fm
  -- State: (1, 2a+2n+4, 0, 2a+n+3, 1)
  -- R1
  rw [show 2 * a + 2 * n + 4 = (2 * a + 2 * n + 3) + 1 from by ring]
  step fm
  -- State: (0, 2a+2n+3, 1, 2a+n+3, 1)
  -- R3
  rw [show 2 * a + n + 3 = (2 * a + n + 2) + 1 from by ring]
  step fm
  -- State: (2, 2a+2n+3, 0, 2a+n+2, 2)
  -- R1R1R3 chain: k = a+n+1 rounds
  rw [show 2 * a + 2 * n + 3 = 2 * (a + n + 1) + 1 from by ring,
      show 2 * a + n + 2 = (a + 1) + (a + n + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (a + n + 1) 1 0 (a + 1) 2)
  rw [show 0 + (a + n + 1) = a + n + 1 from by ring,
      show 2 + (a + n + 1) = a + n + 3 from by ring]
  -- State: (2, 1, a+n+1, a+1, a+n+3)
  -- R1
  step fm
  -- State: (1, 0, a+n+2, a+1, a+n+3)
  -- R2
  step fm
  -- State: (0, 0, a+n+2, a+3, a+n+4)
  -- R3R2R2 chain: a+n+2 rounds
  rw [show a + n + 2 = 0 + (a + n + 2) from by ring,
      show a + 3 = (a + 2) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (a + n + 2) 0 (a + 2) (a + n + 4))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 4⟩)
  · execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨0, 0, 0, 2 * a + n + 4, 2 * a + 2 * n + 4⟩) ⟨0, 0⟩
  intro ⟨a, n⟩
  refine ⟨⟨2 * a + n + 2, n + 1⟩, ?_⟩
  show ⟨(0 : ℕ), 0, 0, 2 * a + n + 4, 2 * a + 2 * n + 4⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * (2 * a + n + 2) + (n + 1) + 4, 2 * (2 * a + n + 2) + 2 * (n + 1) + 4⟩
  rw [show 2 * (2 * a + n + 2) + (n + 1) + 4 = 4 * a + 3 * n + 9 from by ring,
      show 2 * (2 * a + n + 2) + 2 * (n + 1) + 4 = 4 * a + 4 * n + 10 from by ring]
  exact main_trans a n

end Sz22_2003_unofficial_1213
