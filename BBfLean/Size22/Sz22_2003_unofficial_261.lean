import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #261: [14/15, 1/3, 363/2, 25/11, 1/35, 3/5]

Vector representation:
```
 1 -1 -1  1  0
 0 -1  0  0  0
-1  1  0  0  2
 0  0  2  0 -1
 0  0 -1 -1  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_261

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1+R3 loop: k iterations of (R1, R3) pairs
theorem r1r3_loop : ∀ k c d e, ⟨0, 1, c+k, d, e⟩ [fm]⊢* ⟨0, 1, c, d+k, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm  -- R1
  step fm  -- R3
  apply stepStar_trans (h c (d+1) (e+2))
  ring_nf; finish

-- R4 repeated: convert e to c
theorem e_to_c : ∀ k c d e, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c+2*k, d, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R4
  apply stepStar_trans (h (c+2) d e)
  ring_nf; finish

-- R5 repeated: subtract c and d together
theorem cd_sub : ∀ k c d, ⟨0, 0, c+k, d+k, 0⟩ [fm]⊢* ⟨0, 0, c, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm  -- R5
  exact h c d

-- Main transition: (0, 0, c+1, 0, 0) ->+ (0, 0, 3*c, 0, 0) for any c
theorem main_trans (c : ℕ) : ⟨0, 0, c+1, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3*c, 0, 0⟩ := by
  -- R6: (0, 1, c, 0, 0)
  step fm
  -- R1+R3 loop c times: (0, 1, 0, c, 2*c)
  apply stepStar_trans (c₂ := ⟨0, 1, 0, c, 2*c⟩)
  · have h := r1r3_loop c 0 0 0; simp only [Nat.zero_add] at h; exact h
  -- R2 (b>=1, c=0): (0, 0, 0, c, 2*c)
  step fm
  -- R4 loop 2*c times: (0, 0, 4*c, c, 0)
  apply stepStar_trans (c₂ := ⟨0, 0, 4*c, c, 0⟩)
  · have h := e_to_c (2*c) 0 c 0; simp only [Nat.zero_add, (by ring : 2 * (2 * c) = 4 * c)] at h; exact h
  -- R5 loop c times: (0, 0, 3*c, 0, 0)
  apply stepStar_trans
  · have h := cd_sub c (3*c) 0
    simp only [Nat.zero_add, (by ring : 3 * c + c = 4 * c)] at h; exact h
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 0⟩)
  · execute fm 4
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 0, n+2, 0, 0⟩)
  · intro q ⟨n, hq⟩; subst hq
    refine ⟨⟨0, 0, 3*(n+1), 0, 0⟩, ⟨3*n+1, by ring_nf⟩, ?_⟩
    exact main_trans (n+1)
  · exact ⟨2, rfl⟩

end Sz22_2003_unofficial_261
