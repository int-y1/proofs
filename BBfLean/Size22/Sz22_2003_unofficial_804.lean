import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #804: [35/6, 605/2, 8/77, 3/5, 2/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 3  0  0 -1 -1
 0  1 -1  0  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_804

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 chain: move c to b.
theorem c_to_b : ∀ k, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- Spiral opening: R5, R1, R3.
theorem spiral_open : ⟨0, 3 * k + 1, 0, 0, e + 2⟩ [fm]⊢* ⟨3, 3 * k, 1, 0, e⟩ := by
  step fm; step fm; step fm; finish

-- Spiral inner loop: k rounds of (R1 x 3, R3).
theorem spiral_loop : ∀ k c d, ⟨3, 3 * k, c, d, e + k⟩ [fm]⊢* ⟨3, 0, c + 3 * k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show 3 * (k + 1) = (3 * k) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (c + 3) (d + 2))
    ring_nf; finish

-- R2x3 + R3 chain.
theorem r2r3_chain : ∀ k c d f, ⟨3, 0, c, d + k, f + k⟩ [fm]⊢* ⟨3, 0, c + 3 * k, d, f + 6 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show c + 1 + 1 + 1 = c + 3 from by ring,
        show f + k + 6 = (f + 6) + k from by ring]
    apply stepStar_trans (ih (c + 3) d (f + 6))
    ring_nf; finish

-- Final R2 drain.
theorem r2_drain : ⟨3, 0, c, 0, e⟩ [fm]⊢⁺ ⟨0, 0, c + 3, 0, e + 6⟩ := by
  execute fm 3

-- Main transition: (0, 0, 3k+1, 0, E+3k+2) →⁺ (0, 0, 9k+4, 0, E+12k+6).
-- Decomposition:
--   c_to_b:      (0, 0, 3k+1, 0, E+3k+2) →* (0, 3k+1, 0, 0, E+3k+2)
--   spiral_open:  (0, 3k+1, 0, 0, (E+3k)+2) →* (3, 3k, 1, 0, E+3k)
--   spiral_loop:  (3, 3k, 1, 0, (E+2k)+k) →* (3, 0, 3k+1, 2k, E+2k)
--   r2r3_chain:   (3, 0, 3k+1, 0+2k, E+2k) →* (3, 0, 9k+1, 0, E+12k)
--   r2_drain:     (3, 0, 9k+1, 0, E+12k) →⁺ (0, 0, 9k+4, 0, E+12k+6)
theorem main_trans (k E : ℕ) :
    ⟨0, 0, 3 * k + 1, 0, E + 3 * k + 2⟩ [fm]⊢⁺ ⟨0, 0, 9 * k + 4, 0, E + 12 * k + 6⟩ := by
  -- c_to_b
  rw [show (3 * k + 1 : ℕ) = 0 + (3 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (c_to_b (3 * k + 1) (b := 0) (c := 0) (e := E + 3 * k + 2))
  -- spiral_open
  rw [show (0 : ℕ) + (3 * k + 1) = 3 * k + 1 from by ring,
      show E + 3 * k + 2 = (E + 3 * k) + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (spiral_open (k := k) (e := E + 3 * k))
  -- spiral_loop
  rw [show E + 3 * k = (E + 2 * k) + k from by ring]
  apply stepStar_stepPlus_stepPlus (spiral_loop (e := E + 2 * k) k 1 0)
  -- Now goal should be (3, 0, 1+3k, 0+2k, E+2k) ⊢⁺ (0, 0, 9k+4, 0, E+12k+6)
  rw [show 1 + 3 * k = 3 * k + 1 from by ring]
  -- r2r3_chain: need (3, 0, 3k+1, 0+2k, E+2k) in form (3, 0, c, d+n, f+n)
  -- with c=3k+1, d=0, n=2k, f=E: f+n = E+2k ✓
  apply stepStar_stepPlus_stepPlus (r2r3_chain (2 * k) (3 * k + 1) 0 E)
  rw [show 3 * k + 1 + 3 * (2 * k) = 9 * k + 1 from by ring,
      show E + 6 * (2 * k) = E + 12 * k from by ring]
  exact r2_drain

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 3 * p.1 + 1, 0, p.2 + 3 * p.1 + 2⟩) ⟨0, 0⟩
  intro ⟨k, E⟩
  refine ⟨⟨3 * k + 1, E + 3 * k + 1⟩, ?_⟩
  show ⟨0, 0, 3 * k + 1, 0, E + 3 * k + 2⟩ [fm]⊢⁺
       ⟨0, 0, 3 * (3 * k + 1) + 1, 0, (E + 3 * k + 1) + 3 * (3 * k + 1) + 2⟩
  rw [show 3 * (3 * k + 1) + 1 = 9 * k + 4 from by ring,
      show (E + 3 * k + 1) + 3 * (3 * k + 1) + 2 = E + 12 * k + 6 from by ring]
  exact main_trans k E

end Sz22_2003_unofficial_804
