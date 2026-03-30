import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #922: [4/15, 33/14, 1375/2, 7/11, 3/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  3  0  1
 0  0  0  1 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_922

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    have := ih (a + 1) c d (e + 1)
    ring_nf at this ⊢; exact this

theorem r3_drain : ∀ j, ∀ c e,
    ⟨j, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 3 * j, 0, e + j⟩ := by
  intro j; induction' j with j ih <;> intro c e
  · exists 0
  · step fm
    have := ih (c + 3) (e + 1)
    ring_nf at this ⊢; exact this

theorem e_to_d : ∀ k, ∀ c d e,
    ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    have := ih c (d + 1) e
    ring_nf at this ⊢; exact this

theorem main_trans (n : ℕ) :
    ⟨0, 0, 2 * n + 3, n + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 4 * n + 9, 2 * n + 4, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2 * n + 3, n + 1, 0⟩ = some ⟨0, 1, 2 * n + 2, n + 1, 0⟩
    unfold fm; simp only
  -- R1: (0, 1, 2n+2, n+1, 0) -> (2, 0, 2n+1, n+1, 0)
  step fm
  -- R2+R1 chain (n+1 rounds): (2, 0, 2n+1, n+1, 0) -> (n+3, 0, n, 0, n+1)
  have h1 : ⟨2, 0, 2 * n + 1, n + 1, 0⟩ [fm]⊢*
      ⟨n + 3, 0, n, 0, n + 1⟩ := by
    have := r2r1_chain (n + 1) 1 n 0 0
    ring_nf at this ⊢; exact this
  -- R3 drain (n+3 steps): (n+3, 0, n, 0, n+1) -> (0, 0, 4n+9, 0, 2n+4)
  have h2 : ⟨n + 3, 0, n, 0, n + 1⟩ [fm]⊢*
      ⟨0, 0, 4 * n + 9, 0, 2 * n + 4⟩ := by
    have := r3_drain (n + 3) n (n + 1)
    ring_nf at this ⊢; exact this
  -- R4 drain (2n+4 steps): (0, 0, 4n+9, 0, 2n+4) -> (0, 0, 4n+9, 2n+4, 0)
  have h3 : ⟨0, 0, 4 * n + 9, 0, 2 * n + 4⟩ [fm]⊢*
      ⟨0, 0, 4 * n + 9, 2 * n + 4, 0⟩ := by
    have := e_to_d (2 * n + 4) (4 * n + 9) 0 0
    ring_nf at this ⊢; exact this
  exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 1, 0⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 * n + 3, n + 1, 0⟩) 0
  intro n
  refine ⟨2 * n + 3, ?_⟩
  show ⟨0, 0, 2 * n + 3, n + 1, 0⟩ [fm]⊢⁺
    ⟨0, 0, 2 * (2 * n + 3) + 3, (2 * n + 3) + 1, 0⟩
  rw [show 2 * (2 * n + 3) + 3 = 4 * n + 9 from by ring,
      show (2 * n + 3) + 1 = 2 * n + 4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_922
