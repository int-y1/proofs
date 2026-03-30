import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #788: [35/6, 605/2, 20/77, 3/5, 2/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  1 -1 -1
 0  1 -1  0  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_788

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 chain: move c to b.
theorem c_to_b : ∀ k b c e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c e)
    ring_nf; finish

-- R3-R2-R2 chain: (0, 0, c, d+k, e+1) →* (0, 0, c+3k, d, e+3k+1)
theorem r3r2r2_chain : ∀ k c d e, ⟨0, 0, c, d + k, e + 1⟩ [fm]⊢* ⟨0, 0, c + 3 * k, d, e + 3 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + 2 + 2 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (c + 3) d (e + 3))
    ring_nf; finish

-- R1-R1-R3 chain: (2, b+2k, c, d, e+k) →* (2, b, c+3k, d+k, e)
theorem r1r1r3_chain : ∀ k b c d e, ⟨2, b + 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + 3 * k, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R1
    step fm  -- R1
    step fm  -- R3
    apply stepStar_trans (ih b (c + 3) (d + 1) e)
    ring_nf; finish

-- Full transition for odd B: (0, 2m+1, 0, 0, m+f+2) →⁺ (0, 6m+4, 0, 0, 3m+f+4).
theorem trans_odd (m f : ℕ) :
    ⟨0, 2 * m + 1, 0, 0, m + f + 2⟩ [fm]⊢⁺ ⟨0, 6 * m + 4, 0, 0, 3 * m + f + 4⟩ := by
  step fm  -- R5
  rw [show 2 * m + 1 = 2 * m + 0 + 1 from by ring]
  step fm  -- R1
  step fm  -- R3
  rw [show (2 : ℕ) * m = 0 + 2 * m from by ring,
      show m + f = f + m from by ring]
  apply stepStar_trans (r1r1r3_chain m 0 2 0 f)
  -- (2, 0, 3m+2, m, f) - after chain produces (2, 0, 2 + 3*m, 0+m, f)
  -- Need to show this equals what step fm expects
  show ⟨2, 0, 2 + 3 * m, 0 + m, f⟩ [fm]⊢* ⟨0, 6 * m + 4, 0, 0, 3 * m + f + 4⟩
  step fm  -- R2
  step fm  -- R2
  show ⟨0, 0, 2 + 3 * m + 1 + 1, 0 + m, f + 2 + 2⟩ [fm]⊢* ⟨0, 6 * m + 4, 0, 0, 3 * m + f + 4⟩
  rw [show 2 + 3 * m + 1 + 1 = 3 * m + 4 from by ring,
      show f + 2 + 2 = (f + 3) + 1 from by ring,
      show (0 : ℕ) + m = 0 + m from by ring]
  apply stepStar_trans (r3r2r2_chain m (3 * m + 4) 0 (f + 3))
  rw [show 3 * m + 4 + 3 * m = 0 + (6 * m + 4) from by ring,
      show f + 3 + 3 * m + 1 = 3 * m + f + 4 from by ring]
  apply stepStar_trans (c_to_b (6 * m + 4) 0 0 (3 * m + f + 4))
  ring_nf; finish

-- Full transition for even B: (0, 2m+2, 0, 0, m+f+2) →⁺ (0, 6m+7, 0, 0, 3m+f+5).
theorem trans_even (m f : ℕ) :
    ⟨0, 2 * m + 2, 0, 0, m + f + 2⟩ [fm]⊢⁺ ⟨0, 6 * m + 7, 0, 0, 3 * m + f + 5⟩ := by
  step fm  -- R5
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm  -- R1
  step fm  -- R3
  rw [show 2 * m + 1 = 1 + 2 * m from by ring,
      show m + f = f + m from by ring]
  apply stepStar_trans (r1r1r3_chain m 1 2 0 f)
  -- (2, 1, 3m+2, m, f)
  show ⟨2, 1, 2 + 3 * m, 0 + m, f⟩ [fm]⊢* ⟨0, 6 * m + 7, 0, 0, 3 * m + f + 5⟩
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm  -- R1
  step fm  -- R2
  show ⟨0, 0, 2 + 3 * m + 1 + 1, 0 + m + 1, f + 2⟩ [fm]⊢* ⟨0, 6 * m + 7, 0, 0, 3 * m + f + 5⟩
  rw [show 2 + 3 * m + 1 + 1 = 3 * m + 4 from by ring,
      show 0 + m + 1 = 0 + (m + 1) from by ring,
      show f + 2 = (f + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 1) (3 * m + 4) 0 (f + 1))
  rw [show 3 * m + 4 + 3 * (m + 1) = 0 + (6 * m + 7) from by ring,
      show f + 1 + 3 * (m + 1) + 1 = 3 * m + f + 5 from by ring]
  apply stepStar_trans (c_to_b (6 * m + 7) 0 0 (3 * m + f + 5))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 2⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b e, q = ⟨0, b + 1, 0, 0, e⟩ ∧ 2 * e ≥ b + 3)
  · intro c ⟨b, e, hq, he⟩; subst hq
    rcases Nat.even_or_odd b with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- b even: b = 2m, B = b+1 = 2m+1 (odd)
      rw [show m + m = 2 * m from by ring] at hm; subst hm
      obtain ⟨f, rfl⟩ : ∃ f, e = m + f + 2 := ⟨e - m - 2, by omega⟩
      exact ⟨⟨0, 6 * m + 4, 0, 0, 3 * m + f + 4⟩,
        ⟨6 * m + 3, 3 * m + f + 4, rfl, by omega⟩, trans_odd m f⟩
    · -- b odd: b = 2m+1, B = b+1 = 2m+2 (even)
      subst hm
      obtain ⟨f, rfl⟩ : ∃ f, e = m + f + 2 := ⟨e - m - 2, by omega⟩
      exact ⟨⟨0, 6 * m + 7, 0, 0, 3 * m + f + 5⟩,
        ⟨6 * m + 6, 3 * m + f + 5, rfl, by omega⟩, trans_even m f⟩
  · exact ⟨0, 2, rfl, by omega⟩
