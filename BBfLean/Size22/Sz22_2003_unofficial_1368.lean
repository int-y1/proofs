import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1368: [63/10, 4/77, 121/2, 5/3, 21/11]

Vector representation:
```
-1  2 -1  1  0
 2  0  0 -1 -1
-1  0  0  0  2
 0 -1  1  0  0
 0  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1368

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3 drain: a -> e (with c=0, d=0)
theorem r3_drain : ∀ j, ∀ b e,
    ⟨j, b, 0, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e + 2 * j⟩ := by
  intro j; induction' j with j ih
  · intro b e; exists 0
  · intro b e; step fm
    apply stepStar_trans (ih b (e + 2)); ring_nf; finish

-- R4 drain: b -> c (with a=0, d=0)
theorem r4_drain : ∀ b, ∀ c e,
    ⟨0, b, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + b, 0, e⟩ := by
  intro b; induction' b with b ih
  · intro c e; exists 0
  · intro c e; step fm
    apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- R2 drain: d -> a (with c=0)
theorem r2_drain : ∀ j, ∀ a b e,
    ⟨a, b, 0, j, e + j⟩ [fm]⊢* ⟨a + 2 * j, b, 0, 0, e⟩ := by
  intro j; induction' j with j ih
  · intro a b e; exists 0
  · intro a b e
    rw [show e + (j + 1) = (e + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) b e); ring_nf; finish

-- R1R1R2 chain: each round does R1,R1,R2 consuming 2 from c
theorem r1r1r2_chain : ∀ k, ∀ b d e,
    ⟨2, b, 2 * k + 1, d, e + k⟩ [fm]⊢* ⟨2, b + 4 * k, 1, d + k, e⟩ := by
  intro k; induction' k with k ih
  · intro b d e; simp; exists 0
  · intro b d e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 4) (d + 1) e); ring_nf; finish

-- Main transition: (0, 0, 2k+1, 0, E+2k+3) ⊢⁺ (0, 0, 4k+3, 0, E+4k+6)
theorem main_trans (k E : ℕ) :
    ⟨0, 0, 2 * k + 1, 0, E + 2 * k + 3⟩ [fm]⊢⁺
    ⟨0, 0, 4 * k + 3, 0, E + 4 * k + 6⟩ := by
  -- R5: (0, 0, 2k+1, 0, E+2k+3) -> (0, 1, 2k+1, 1, E+2k+2)
  -- R2: -> (2, 1, 2k+1, 0, E+2k+1)
  rw [show E + 2 * k + 3 = (E + 2 * k + 1) + 1 + 1 from by ring]
  step fm; step fm
  -- Now at (2, 1, 2k+1, 0, E+2k+1)
  -- R1R1R2 chain: (2, 1, 2k+1, 0, E+2k+1) ⊢* (2, 4k+1, 1, k, E+k+1)
  rw [show E + 2 * k + 1 = (E + k + 1) + k from by ring]
  apply stepStar_trans (r1r1r2_chain k 1 0 (E + k + 1))
  rw [show 1 + 4 * k = 4 * k + 1 from by ring,
      show (0 + k : ℕ) = k from by ring]
  -- Now at (2, 4k+1, 1, k, E+k+1)
  -- R1: (2, 4k+1, 1, k, E+k+1) -> (1, 4k+3, 0, k+1, E+k+1)
  step fm
  -- Now at (1, 4k+3, 0, k+1, E+k+1)
  -- R2 drain: (1, 4k+3, 0, k+1, E+k+1) ⊢* (2k+3, 4k+3, 0, 0, E)
  rw [show E + k + 1 = E + (k + 1) from by ring]
  apply stepStar_trans (r2_drain (k + 1) 1 (4 * k + 3) E)
  rw [show 1 + 2 * (k + 1) = 2 * k + 3 from by ring]
  -- Now at (2k+3, 4k+3, 0, 0, E)
  -- R3 drain: (2k+3, 4k+3, 0, 0, E) ⊢* (0, 4k+3, 0, 0, E+2(2k+3))
  apply stepStar_trans (r3_drain (2 * k + 3) (4 * k + 3) E)
  -- Now at (0, 4k+3, 0, 0, E+2*(2k+3))
  rw [show E + 2 * (2 * k + 3) = E + 4 * k + 6 from by ring]
  -- R4 drain: (0, 4k+3, 0, 0, E+4k+6) ⊢* (0, 0, 4k+3, 0, E+4k+6)
  apply stepStar_trans (r4_drain (4 * k + 3) 0 (E + 4 * k + 6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 4⟩)
  · execute fm 6
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k E, q = ⟨0, 0, 2 * k + 1, 0, E + 2 * k + 3⟩)
  · intro q ⟨k, E, hq⟩; subst hq
    exact ⟨⟨0, 0, 4 * k + 3, 0, E + 4 * k + 6⟩,
           ⟨2 * k + 1, E + 1, by ring_nf⟩, main_trans k E⟩
  · exact ⟨0, 1, by ring_nf⟩

end Sz22_2003_unofficial_1368
