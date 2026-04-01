import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1404: [7/15, 1/847, 78/7, 1/3, 55/13, 7/2]

Vector representation:
```
 0 -1 -1  1  0  0
 0  0  0 -1 -2  0
 1  1  0 -1  0  1
 0 -1  0  0  0  0
 0  0  1  0  1 -1
-1  0  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1404

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d+1, e+2, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a+1, b+1, c, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | _ => none

-- Drain phase (even e): R6+R2 repeated h times.
theorem drain_even : ∀ h, ∀ a c, ⟨a + h, 0, c, 0, 2 * h, 0⟩ [fm]⊢* ⟨a, 0, c, 0, 0, 0⟩ := by
  intro h; induction' h with h ih <;> intro a c
  · exists 0
  · rw [show a + (h + 1) = (a + h) + 1 from by ring,
        show 2 * (h + 1) = 2 * h + 2 from by ring]
    step fm; step fm
    exact ih a c

-- Drain phase (odd e): R6+R2 repeated h times.
theorem drain_odd : ∀ h, ∀ a c, ⟨a + h, 0, c, 0, 2 * h + 1, 0⟩ [fm]⊢* ⟨a, 0, c, 0, 1, 0⟩ := by
  intro h; induction' h with h ih <;> intro a c
  · exists 0
  · rw [show a + (h + 1) = (a + h) + 1 from by ring,
        show 2 * (h + 1) + 1 = 2 * h + 1 + 2 from by ring]
    step fm; step fm
    exact ih a c

-- R1+R3 chain with e=0, ending with R4.
theorem r1r3_chain_0 : ∀ k, ∀ a f, ⟨a, 1, k, 0, 0, f⟩ [fm]⊢* ⟨a + k, 0, 0, 0, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a f
  · step fm; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (f + 1))
    ring_nf; finish

-- R1+R3 chain with e=1, ending with R4.
theorem r1r3_chain_1 : ∀ k, ∀ a f, ⟨a, 1, k, 0, 1, f⟩ [fm]⊢* ⟨a + k, 0, 0, 0, 1, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a f
  · step fm; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (f + 1))
    ring_nf; finish

-- R5 chain: transfer f to c and e.
theorem f_to_ce : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show (e : ℕ) + (k + 1) = (e + 1) + k from by ring,
        show (c : ℕ) + (k + 1) = (c + 1) + k from by ring]
    step fm
    exact ih a (c + 1) (e + 1)

-- Build phase with e_rem=0.
theorem build_even (a c : ℕ) :
    ⟨a + 1, 0, c, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + c + 1, 0, c + 1, 0, c + 1, 0⟩ := by
  step fm; step fm
  apply stepStar_trans (r1r3_chain_0 c (a + 1) 1)
  rw [show a + 1 + c = a + c + 1 from by ring,
      show 1 + c = c + 1 from by ring]
  apply stepStar_trans (f_to_ce (c + 1) (a + c + 1) 0 0)
  ring_nf; finish

-- Build phase with e_rem=1.
theorem build_odd (a c : ℕ) :
    ⟨a + 1, 0, c, 0, 1, 0⟩ [fm]⊢⁺ ⟨a + c + 1, 0, c + 1, 0, c + 2, 0⟩ := by
  step fm; step fm
  apply stepStar_trans (r1r3_chain_1 c (a + 1) 1)
  rw [show a + 1 + c = a + c + 1 from by ring,
      show 1 + c = c + 1 from by ring]
  apply stepStar_trans (f_to_ce (c + 1) (a + c + 1) 0 1)
  ring_nf; finish

-- Full transition for even e.
theorem trans_even (a c h : ℕ) :
    ⟨a + h + 1, 0, c, 0, 2 * h, 0⟩ [fm]⊢⁺ ⟨a + c + 1, 0, c + 1, 0, c + 1, 0⟩ := by
  rw [show a + h + 1 = (a + 1) + h from by ring]
  exact stepStar_stepPlus_stepPlus (drain_even h (a + 1) c) (build_even a c)

-- Full transition for odd e.
theorem trans_odd (a c h : ℕ) :
    ⟨a + h + 1, 0, c, 0, 2 * h + 1, 0⟩ [fm]⊢⁺ ⟨a + c + 1, 0, c + 1, 0, c + 2, 0⟩ := by
  rw [show a + h + 1 = (a + 1) + h from by ring]
  exact stepStar_stepPlus_stepPlus (drain_odd h (a + 1) c) (build_odd a c)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 2, 0, 3, 0⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c h, q = ⟨a + h + 1, 0, c + 2, 0, 2 * h, 0⟩ ∨
                            q = ⟨a + h + 1, 0, c + 2, 0, 2 * h + 1, 0⟩)
  · intro q ⟨a, c, h, hq⟩
    rcases hq with hq | hq <;> subst hq
    · -- Even case: result is (a+c+3, 0, c+3, 0, c+3, 0)
      rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- c = m+m: c+3 = 2(m+1)+1, odd
        subst hm; rw [show m + m + 2 = 2 * m + 2 from by ring]
        exact ⟨⟨a + 2 * m + 3, 0, 2 * m + 3, 0, 2 * m + 3, 0⟩,
          ⟨a + m + 1, 2 * m + 1, m + 1, Or.inr (by ring_nf)⟩,
          trans_even a (2 * m + 2) h⟩
      · -- c = 2m+1: c+3 = 2(m+2), even
        subst hm; rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring]
        exact ⟨⟨a + 2 * m + 4, 0, 2 * m + 4, 0, 2 * m + 4, 0⟩,
          ⟨a + m + 1, 2 * m + 2, m + 2, Or.inl (by ring_nf)⟩,
          trans_even a (2 * m + 3) h⟩
    · -- Odd case: result is (a+c+3, 0, c+3, 0, c+4, 0)
      rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- c = m+m: c+4 = 2(m+2), even
        subst hm; rw [show m + m + 2 = 2 * m + 2 from by ring]
        exact ⟨⟨a + 2 * m + 3, 0, 2 * m + 3, 0, 2 * m + 4, 0⟩,
          ⟨a + m, 2 * m + 1, m + 2, Or.inl (by ring_nf)⟩,
          trans_odd a (2 * m + 2) h⟩
      · -- c = 2m+1: c+4 = 2(m+2)+1, odd
        subst hm; rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring]
        exact ⟨⟨a + 2 * m + 4, 0, 2 * m + 4, 0, 2 * m + 5, 0⟩,
          ⟨a + m + 1, 2 * m + 2, m + 2, Or.inr (by ring_nf)⟩,
          trans_odd a (2 * m + 3) h⟩
  · exact ⟨0, 0, 1, Or.inr (by ring_nf)⟩

end Sz22_2003_unofficial_1404
