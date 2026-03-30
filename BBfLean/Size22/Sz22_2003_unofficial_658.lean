import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #658: [35/6, 1573/2, 4/55, 3/7, 6/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  2  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 1  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_658

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d, e, f⟩
  | _ => none

-- R4 repeated: move d to b.
theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (b := b + 1)); ring_nf; finish

-- R3+R2+R2 drain chain.
-- (0, 0, c+k, d, e+1, f) ⊢* (0, 0, c, d, e+3*k+1, f+2*k)
theorem r3r2r2_chain : ∀ k, ⟨0, 0, c + k, d, e + 1, f⟩ [fm]⊢* ⟨0, 0, c, d, e + 3 * k + 1, f + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + 2 + 2 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (c := c) (e := e + 3) (f := f + 2))
    ring_nf; finish

-- R3+R1+R1 interleaving chain (even b = 2k).
-- (0, 2*k, c+1, d, e+1+k, f) ⊢* (0, 0, c+k+1, d+2*k, e+1, f)
theorem r3r1r1_chain : ∀ k, ⟨0, 2 * k, c + 1, d, e + 1 + k, f⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, e + 1, f⟩ := by
  intro k; induction' k with k ih generalizing c d e f
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + 1 + (k + 1) = (e + 1 + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c := c + 1) (d := d + 2))
    ring_nf; finish

-- R3+R1+R1 chain for odd b = 2k+1, with R3+R1+R2 tail.
-- (0, 2*k+1, c+1, d, e+2+k, f) ⊢* (0, 0, c+k+1, d+2*k+1, e+3, f+1)
theorem r3r1r1_odd_chain : ∀ k, ⟨0, 2 * k + 1, c + 1, d, e + 2 + k, f⟩ [fm]⊢*
    ⟨0, 0, c + k + 1, d + 2 * k + 1, e + 3, f + 1⟩ := by
  intro k; induction' k with k ih generalizing c d e f
  · -- k=0: (0, 1, c+1, d, e+2, f). R3+R1+R2.
    rw [show e + 2 = (e + 1) + 1 from by ring]
    step fm  -- R3: (2, 1, c, d, e+1, f)
    step fm  -- R1: (1, 0, c+1, d+1, e+1, f)
    step fm  -- R2: (0, 0, c+1, d+1, e+3, f+1)
    ring_nf; finish
  · -- k+1: do one R3+R1+R1 round, then apply ih.
    rw [show 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 from by ring,
        show e + 2 + (k + 1) = (e + 2 + k) + 1 from by ring]
    step fm  -- R3
    step fm  -- R1
    step fm  -- R1
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c := c + 1) (d := d + 2))
    ring_nf; finish

-- Full transition for even d (d = 2*m+2, m >= 0).
-- (0, 0, 0, 2*m+2, g+4*m+6, g+1) ⊢⁺ (0, 0, 0, 2*m+3, g+6*m+11, g+2*m+4)
theorem trans_even (m : ℕ) :
    ⟨0, 0, 0, 2 * m + 2, g + 4 * m + 6, g + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 3, g + 6 * m + 11, g + 2 * m + 4⟩ := by
  rw [show (0 : ℕ) = 0 + 0 from by ring,
      show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2 * m + 2) (b := 0) (d := 0))
  simp only [Nat.zero_add]
  step fm; step fm
  rw [show 2 * m + 2 = 2 * (m + 1) from by ring,
      show g + 4 * m + 6 = (g + 3 * m + 4) + 1 + (m + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain (m + 1) (c := 0) (d := 1) (e := g + 3 * m + 4))
  rw [show 0 + (m + 1) + 1 = 0 + (m + 2) from by ring,
      show 1 + 2 * (m + 1) = 2 * m + 3 from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 2) (c := 0) (d := 2 * m + 3) (e := g + 3 * m + 4) (f := g))
  ring_nf; finish

-- Full transition for odd d (d = 2*m+3, m >= 0).
-- (0, 0, 0, 2*m+3, g+4*m+8, g+1) ⊢⁺ (0, 0, 0, 2*m+4, g+6*m+14, g+2*m+5)
theorem trans_odd (m : ℕ) :
    ⟨0, 0, 0, 2 * m + 3, g + 4 * m + 8, g + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 4, g + 6 * m + 14, g + 2 * m + 5⟩ := by
  rw [show (0 : ℕ) = 0 + 0 from by ring,
      show 2 * m + 3 = 0 + (2 * m + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2 * m + 3) (b := 0) (d := 0))
  simp only [Nat.zero_add]
  step fm; step fm
  rw [show 2 * m + 3 = 2 * (m + 1) + 1 from by ring,
      show g + 4 * m + 8 = (g + 3 * m + 5) + 2 + (m + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1r1_odd_chain (m + 1) (c := 0) (d := 1) (e := g + 3 * m + 5))
  rw [show 0 + (m + 1) + 1 = 0 + (m + 2) from by ring,
      show 1 + 2 * (m + 1) + 1 = 2 * m + 4 from by ring,
      show (g + 3 * m + 5) + 3 = (g + 3 * m + 7) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 2) (c := 0) (d := 2 * m + 4) (e := g + 3 * m + 7) (f := g + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 9, 4⟩)
  · execute fm 15
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d g, q = ⟨0, 0, 0, d, g + 2 * d + 2, g + 1⟩ ∧ d ≥ 2)
  · intro c ⟨d, g, hq, hd⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
      refine ⟨⟨0, 0, 0, 2 * m + 3, (g + 2 * m + 3) + 2 * (2 * m + 3) + 2, (g + 2 * m + 3) + 1⟩,
        ⟨2 * m + 3, g + 2 * m + 3, rfl, by omega⟩, ?_⟩
      show ⟨0, 0, 0, 2 * m + 2, g + 2 * (2 * m + 2) + 2, g + 1⟩ [fm]⊢⁺
        ⟨0, 0, 0, 2 * m + 3, (g + 2 * m + 3) + 2 * (2 * m + 3) + 2, (g + 2 * m + 3) + 1⟩
      rw [show g + 2 * (2 * m + 2) + 2 = g + 4 * m + 6 from by ring,
          show (g + 2 * m + 3) + 2 * (2 * m + 3) + 2 = g + 6 * m + 11 from by ring,
          show (g + 2 * m + 3) + 1 = g + 2 * m + 4 from by ring]
      exact trans_even m
    · subst hK
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
      refine ⟨⟨0, 0, 0, 2 * m + 4, (g + 2 * m + 4) + 2 * (2 * m + 4) + 2, (g + 2 * m + 4) + 1⟩,
        ⟨2 * m + 4, g + 2 * m + 4, rfl, by omega⟩, ?_⟩
      show ⟨0, 0, 0, 2 * m + 3, g + 2 * (2 * m + 3) + 2, g + 1⟩ [fm]⊢⁺
        ⟨0, 0, 0, 2 * m + 4, (g + 2 * m + 4) + 2 * (2 * m + 4) + 2, (g + 2 * m + 4) + 1⟩
      rw [show g + 2 * (2 * m + 3) + 2 = g + 4 * m + 8 from by ring,
          show (g + 2 * m + 4) + 2 * (2 * m + 4) + 2 = g + 6 * m + 14 from by ring,
          show (g + 2 * m + 4) + 1 = g + 2 * m + 5 from by ring]
      exact trans_odd m
  · exact ⟨2, 3, by ring, by omega⟩
