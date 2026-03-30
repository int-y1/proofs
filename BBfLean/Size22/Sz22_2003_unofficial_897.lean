import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #897: [4/15, 21/2, 121/3, 25/77, 3/55]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  1  0
 0 -1  0  0  2
 0  0  2 -1 -1
 0  1 -1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_897

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: (0, 0, c, d+k, e+k) →* (0, 0, c+2*k, d, e)
theorem r4_chain : ∀ k, ⟨0, 0, c, d + k, e + k⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 2))
    ring_nf; finish

-- R1-R2 interleaved chain
theorem r1r2_chain : ∀ k, ⟨a, 1, c + k, d, n⟩ [fm]⊢* ⟨a + k, 1, c, d + k, n⟩ := by
  intro k; induction' k with k ih generalizing a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a + 1) (c := c) (d := d + 1))
    ring_nf; finish

-- R2 drain: (k, b, 0, d, n) →* (0, b+k, 0, d+k, n)
theorem r2_drain : ∀ k, ⟨k, b, 0, d, n⟩ [fm]⊢* ⟨0, b + k, 0, d + k, n⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b := b + 1) (d := d + 1))
    ring_nf; finish

-- R3 drain: (0, k, 0, d, e) →* (0, 0, 0, d, e+2*k)
theorem r3_drain : ∀ k, ⟨0, k, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing e
  · exists 0
  · step fm
    apply stepStar_trans (ih (e := e + 2))
    ring_nf; finish

-- Phases 2-6 combined: (0, 0, 2*d+2, 0, n+1) →* (0, 0, 0, 4*d+2, 4*d+n+4)
theorem phases_2_6 (d n : ℕ) : ⟨0, 0, 2 * d + 2, 0, n + 1⟩ [fm]⊢* ⟨0, 0, 0, 4 * d + 2, 4 * d + n + 4⟩ := by
  rw [show 2 * d + 2 = (2 * d + 1) + 1 from by ring]
  step fm
  rw [show 2 * d + 1 = 1 + 2 * d from by ring]
  apply stepStar_trans (r1r2_chain (2 * d) (a := 0) (c := 1) (d := 0) (n := n))
  show ⟨0 + 2 * d, 1, 1, 0 + 2 * d, n⟩ [fm]⊢* _
  rw [show 0 + 2 * d = 2 * d from by ring]
  step fm
  show ⟨2 * d + 2, 0, 0, 2 * d, n⟩ [fm]⊢* _
  apply stepStar_trans (r2_drain (2 * d + 2) (b := 0) (d := 2 * d) (n := n))
  rw [show 0 + (2 * d + 2) = 2 * d + 2 from by ring,
      show 2 * d + (2 * d + 2) = 4 * d + 2 from by ring]
  apply stepStar_trans (r3_drain (2 * d + 2) (d := 4 * d + 2) (e := n))
  rw [show n + 2 * (2 * d + 2) = 4 * d + n + 4 from by ring]
  finish

-- Main transition
theorem main_trans (d n : ℕ) : ⟨0, 0, 0, d + 1, d + n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * d + 2, 4 * d + n + 4⟩ := by
  -- Rewrite to form expected by r4_chain with k = d+1
  rw [show d + 1 = 0 + (d + 1) from by ring,
      show d + n + 2 = (n + 1) + (d + 1) from by ring]
  -- Now goal: (0, 0, 0, 0+(d+1), (n+1)+(d+1)) ⊢⁺ (0, 0, 0, 4*d+2, 4*d+n+4)
  -- First R4 step
  step fm
  -- Now ⊢*. After step, Lean has (0, 0, 2, d, (n+1)+d) or similar.
  -- The step fm macro matches R4: (0, 0, c, d+1, e+1) => (0, 0, c+2, d, e)
  -- Input: (0, 0, 0, 0+(d+1), (n+1)+(d+1))
  -- Lean sees: 0+(d+1) = d+1 (after succ matching), and (n+1)+(d+1) = n+1+d+1 (after succ)
  -- After R4: (0, 0, 2, 0+d, (n+1)+d) — these are the d and e from the match
  -- remaining d R4 steps
  apply stepStar_trans (r4_chain d (c := 2) (d := 0) (e := n + 1))
  -- Now at (0, 0, 2+2*d, 0, n+1)
  rw [show 2 + 2 * d = 2 * d + 2 from by ring]
  exact phases_2_6 d n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, n⟩ ↦ ⟨0, 0, 0, d + 1, d + n + 2⟩) ⟨0, 0⟩
  intro ⟨d, n⟩; exists ⟨4 * d + 1, n + 1⟩
  show ⟨0, 0, 0, d + 1, d + n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * d + 1 + 1, 4 * d + 1 + (n + 1) + 2⟩
  rw [show 4 * d + 1 + 1 = 4 * d + 2 from by ring,
      show 4 * d + 1 + (n + 1) + 2 = 4 * d + n + 4 from by ring]
  exact main_trans d n

end Sz22_2003_unofficial_897
