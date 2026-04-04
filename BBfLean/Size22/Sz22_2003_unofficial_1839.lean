import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1839: [9/2, 28/15, 11/3, 5/847, 14/11]

Vector representation:
```
-1  2  0  0  0
 2 -1 -1  1  0
 0 -1  0  0  1
 0  0  1 -1 -2
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1839

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R2-R1-R1 chain: each iteration consumes 1 from c, adds 3 to b, adds 1 to d.
-- (0, b, c+k, d, e) →* (0, b+3*k, c, d+k, e)
theorem r2r1r1_chain : ∀ k, ⟨(0 : ℕ), b + 2, c + k, d, e⟩ [fm]⊢* ⟨(0 : ℕ), b + 3 * k + 2, c, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b := b + 3) (d := d + 1))
    ring_nf; finish

-- R3 drain: move b to e. (0, b+k, 0, d, e) →* (0, b, 0, d, e+k)
theorem r3_drain : ∀ k, ⟨(0 : ℕ), b + k, 0, d, e⟩ [fm]⊢* ⟨(0 : ℕ), b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b) (e := e + 1))
    ring_nf; finish

-- R4 drain: convert d to c, consuming 2 from e per step.
-- (0, 0, c, d+k, e+2*k) →* (0, 0, c+k, d, e)
theorem r4_drain : ∀ k, ∀ c d e, ⟨(0 : ℕ), 0, c, d + k, e + 2 * k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- Main transition: (0, 0, n+1, 0, e+1) →⁺ (0, 0, n+2, 0, e+n+1)
theorem main_trans : ∀ n e, ⟨(0 : ℕ), 0, n + 1, 0, e + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, n + 2, 0, e + n + 1⟩ := by
  intro n e
  -- R5: (0, 0, n+1, 0, e+1) -> (1, 0, n+1, 1, e)
  step fm
  -- R1: (1, 0, n+1, 1, e) -> (0, 2, n+1, 1, e)
  step fm
  -- n+1 iterations of R2-R1-R1
  rw [show (2 : ℕ) = 0 + 2 from by ring, show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (r2r1r1_chain (n + 1) (b := 0) (c := 0) (d := 1) (e := e))
  -- R3 drain
  rw [show 0 + 3 * (n + 1) + 2 = 0 + (3 * (n + 1) + 2) from by ring]
  apply stepStar_trans (r3_drain (3 * (n + 1) + 2) (b := 0) (d := 1 + (n + 1)) (e := e))
  -- R4 drain
  rw [show 1 + (n + 1) = 0 + (n + 2) from by ring,
      show e + (3 * (n + 1) + 2) = (e + n + 1) + 2 * (n + 2) from by ring,
      show (0 : ℕ) = 0 from rfl]
  apply stepStar_trans (r4_drain (n + 2) 0 0 (e + n + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 1⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨0, 0, n + 1, 0, e + 1⟩) ⟨0, 0⟩
  intro ⟨n, e⟩; exact ⟨⟨n + 1, e + n⟩, main_trans n e⟩

end Sz22_2003_unofficial_1839
