import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1124: [5/6, 44/35, 1/5, 49/2, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
 0  0 -1  0  0
-1  0  0  2  0
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1124

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 drain
theorem drain_a_plus : ∀ k, ∀ d e, ⟨k + 1, 0, 0, d, e⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2 * (k + 1), e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · step fm; finish
  · step fm
    apply stepStar_trans (stepPlus_stepStar (ih (d + 2) e))
    ring_nf; finish

-- R5 drain
theorem e_to_b_star : ∀ k, ∀ b D, ⟨0, b, 0, D, k⟩ [fm]⊢* ⟨0, b + k, 0, D, 0⟩ := by
  intro k; induction' k with k ih <;> intro b D
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) D)
    ring_nf; finish

-- R2 chain
theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

-- Interleave even
theorem interleave_even :
    ∀ k, ∀ c d e, ⟨2, 2 * k, c, d + k, e⟩ [fm]⊢* ⟨2, 0, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- Interleave odd
theorem interleave_odd :
    ∀ k, ∀ c d e, ⟨2, 2 * k + 1, c, d + k, e⟩ [fm]⊢* ⟨1, 0, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 + 1 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- Even case: (2m+3, 0, 0, d, 2m+2) ⊢⁺ (2m+4, 0, 0, d+2m+2, 2m+3)
theorem trans_even (m d : ℕ) :
    ⟨2 * m + 3, 0, 0, d, 2 * m + 2⟩ [fm]⊢⁺ ⟨2 * m + 4, 0, 0, d + 2 * m + 2, 2 * m + 3⟩ := by
  -- Phase 1: drain_a_plus
  rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (drain_a_plus (2 * m + 2) d (2 * m + 2))
  -- (0, 0, 0, d+2*(2m+3), 2m+2)
  rw [show d + 2 * (2 * m + 2 + 1) = d + 4 * m + 6 from by ring]
  -- Phase 2: e_to_b_star
  apply stepStar_trans (e_to_b_star (2 * m + 2) 0 (d + 4 * m + 6))
  -- (0, 0+(2m+2), 0, d+4m+6, 0) = (0, 2m+2, 0, d+4m+6, 0)
  simp only [Nat.zero_add]
  -- Phase 3: R6+R2
  rw [show d + 4 * m + 6 = (d + 4 * m + 4 + 1) + 1 from by ring]
  step fm
  rw [show d + 4 * m + 4 + 1 = (d + 4 * m + 4) + 1 from by ring]
  step fm
  -- (2, 2m+2, 0, d+4m+4, 1)
  -- Phase 4: interleave_even(m+1)
  rw [show 2 * m + 2 = 2 * (m + 1) from by ring,
      show d + 4 * m + 4 = (d + 3 * m + 3) + (m + 1) from by ring]
  apply stepStar_trans (interleave_even (m + 1) 0 (d + 3 * m + 3) 1)
  -- (2, 0, 0+(m+1), d+3m+3, 1+(m+1))
  -- Phase 5: r2_chain(m+1)
  -- Clean up 0+ terms
  simp only [Nat.zero_add]
  rw [show 1 + (m + 1) = m + 2 from by ring,
      show d + 3 * m + 3 = (d + 2 * m + 2) + (m + 1) from by ring]
  have h := r2_chain (m + 1) 2 0 (d + 2 * m + 2) (m + 2)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

-- Odd case: (2m+4, 0, 0, d, 2m+3) ⊢⁺ (2m+5, 0, 0, d+2m+3, 2m+4)
theorem trans_odd (m d : ℕ) :
    ⟨2 * m + 4, 0, 0, d, 2 * m + 3⟩ [fm]⊢⁺ ⟨2 * m + 5, 0, 0, d + 2 * m + 3, 2 * m + 4⟩ := by
  -- Phase 1: drain_a_plus
  rw [show 2 * m + 4 = (2 * m + 3) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (drain_a_plus (2 * m + 3) d (2 * m + 3))
  rw [show d + 2 * (2 * m + 3 + 1) = d + 4 * m + 8 from by ring]
  -- Phase 2: e_to_b_star
  apply stepStar_trans (e_to_b_star (2 * m + 3) 0 (d + 4 * m + 8))
  simp only [Nat.zero_add]
  -- Phase 3: R6+R2
  rw [show d + 4 * m + 8 = (d + 4 * m + 6 + 1) + 1 from by ring]
  step fm
  rw [show d + 4 * m + 6 + 1 = (d + 4 * m + 6) + 1 from by ring]
  step fm
  -- (2, 2m+3, 0, d+4m+6, 1)
  -- Phase 4: interleave_odd(m+1)
  rw [show 2 * m + 3 = 2 * (m + 1) + 1 from by ring,
      show d + 4 * m + 6 = (d + 3 * m + 5) + (m + 1) from by ring]
  apply stepStar_trans (interleave_odd (m + 1) 0 (d + 3 * m + 5) 1)
  simp only [Nat.zero_add]
  rw [show 1 + (m + 1) = m + 2 from by ring,
      show m + 1 + 1 = m + 2 from by ring,
      show d + 3 * m + 5 = (d + 2 * m + 3) + (m + 2) from by ring]
  have h := r2_chain (m + 2) 1 0 (d + 2 * m + 3) (m + 2)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

-- Main transition
theorem main_trans (e d : ℕ) :
    ⟨e + 3, 0, 0, d, e + 2⟩ [fm]⊢⁺ ⟨e + 4, 0, 0, d + e + 2, e + 3⟩ := by
  rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [hm, show m + m = 2 * m from by ring]
    exact trans_even m d
  · rw [hm]
    exact trans_odd m d

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 2⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨e, d⟩ ↦ ⟨e + 3, 0, 0, d, e + 2⟩) ⟨0, 1⟩
  intro ⟨e, d⟩
  exact ⟨⟨e + 1, d + e + 2⟩, main_trans e d⟩

end Sz22_2003_unofficial_1124
