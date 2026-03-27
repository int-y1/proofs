import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #52: [1/15, 9/385, 196/3, 5/7, 33/2]

Vector representation:
```
 0 -1 -1  0  0
 0  2 -1 -1 -1
 2 -1  0  2  0
 0  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_52

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: transfer d to c
theorem d_to_c : ∀ k c, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih _); ring_nf; finish

-- R5+R1 repeated: drain a and c into e
theorem ac_drain : ∀ k a e, ⟨a + k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [← Nat.add_assoc]; step fm; step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- Interleaved R4,R2,R3,R3 chain (requires D+2 >= 2 for R2)
theorem interleaved : ∀ k, ∀ A D E, ⟨A, 0, 0, D + 2, E + k⟩ [fm]⊢* ⟨A + 4 * k, 0, 0, D + 2 + 2 * k, E⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · exists 0
  rw [show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

-- Main transition: (a+1, 0, 0, 0, e) ⊢⁺ (a+2e+2, 0, 0, 0, 2e+4)
theorem main_trans : ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a + 2 * e + 2, 0, 0, 0, 2 * e + 4⟩ := by
  -- Phase 1: 6 init steps -> (a+6, 0, 0, 4, e)
  step fm; step fm; step fm; step fm; step fm; step fm
  -- Phase 2: interleaved chain, e rounds -> (a+6+4e, 0, 0, 4+2e, 0)
  rw [show (4 : ℕ) = 2 + 2 from by ring, show e = 0 + e from by ring]
  apply stepStar_trans (interleaved e (a + 2 + 2 + 2) 2 0)
  -- Phase 3: d_to_c -> (a+6+4e, 0, 2e+4, 0, 0)
  rw [show 2 + 2 + 2 * e = 0 + (2 * e + 4) from by ring]
  apply stepStar_trans (d_to_c (2 * e + 4) 0)
  simp only [Nat.zero_add]
  -- Phase 4: ac_drain -> (a+2e+2, 0, 0, 0, 2e+4)
  rw [show a + 2 + 2 + 2 + 4 * e = (a + 2 * e + 2) + (2 * e + 4) from by ring]
  apply stepStar_trans (ac_drain (2 * e + 4) _ 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + 1, 0, 0, 0, e⟩) ⟨0, 0⟩
  intro ⟨a, e⟩; exact ⟨⟨a + 2 * e + 1, 2 * e + 4⟩, main_trans⟩

end Sz22_2003_unofficial_52
