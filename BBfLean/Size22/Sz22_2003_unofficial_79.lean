import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #79: [1/18, 385/2, 2/65, 507/7, 2/33]

Vector representation:
```
-1 -2  0  0  0  0
-1  0  1  1  1  0
 1  0 -1  0  0 -1
 0  1  0 -1  0  2
 1 -1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_79

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e+1, f⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f+2⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- R2+R3 alternation: each pair increments d and e, decrements f.
theorem r2r3_chain : ∀ j d e, ⟨1, 0, 0, d, e, f + j⟩ [fm]⊢* ⟨1, 0, 0, d + j, e + j, f⟩ := by
  intro j; induction' j with j ih <;> intro d e
  · exists 0
  rw [show f + (j + 1) = (f + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- R4 chain: drains d into b and f.
theorem r4_chain : ∀ j b g, ⟨0, b, 0, d + j, e, g⟩ [fm]⊢* ⟨0, b + j, 0, d, e, g + 2 * j⟩ := by
  intro j; induction' j with j ih <;> intro b g
  · exists 0
  rw [show d + (j + 1) = (d + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- R5+R1 chain: each pair consumes 3 from b and 1 from e.
-- (0, 3*(j+1)+1, 0, 0, e+j+1, f) -R5-> (1, 3*j+3, 0, 0, e+j, f) -R1-> (0, 3*j+1, 0, 0, e+j, f)
theorem r5r1_chain : ∀ j e', ⟨0, 3 * j + 1, 0, 0, e' + j, f⟩ [fm]⊢* ⟨0, 1, 0, 0, e', f⟩ := by
  intro j; induction' j with j ih <;> intro e'
  · exists 0
  rw [show 3 * (j + 1) + 1 = (3 * j + 2) + 2 from by ring,
      show e' + (j + 1) = e' + j + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _); ring_nf; finish

-- Main transition: (1, 0, 0, 0, 2k, 3k) →⁺ (1, 0, 0, 0, 2(2k+1), 3(2k+1))
theorem main_trans (k : ℕ) :
    (⟨1, 0, 0, 0, 2 * k, 3 * k⟩ : Q) [fm]⊢⁺ ⟨1, 0, 0, 0, 2 * (2 * k + 1), 3 * (2 * k + 1)⟩ := by
  -- Phase 1: R2+R3 chain (3k pairs)
  rw [show (3 : ℕ) * k = 0 + 3 * k from by ring]
  apply stepStar_stepPlus_stepPlus (r2r3_chain (3 * k) 0 (2 * k))
  simp only [Nat.zero_add]
  -- At (1, 0, 0, 3k, 5k, 0). One R2 step.
  step fm
  -- At (0, 0, 1, 3k+1, 5k+1, 0). 8 fixed steps.
  rw [show 3 * k + 1 = (3 * k) + 0 + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  -- At (0, 0, 0, 3k+1, 5k+3, 1). Phase 3: R4 chain (3k+1 steps).
  rw [show 3 * k + 0 + 1 = 0 + (3 * k + 1) from by ring]
  apply stepStar_trans (r4_chain (3 * k + 1) 0 1)
  simp only [Nat.zero_add]
  -- At (0, 3k+1, 0, 0, 5k+3, 6k+3). Phase 4: R5+R1 chain (k pairs) then final R5.
  rw [show 2 * k + 3 * k + 1 + 1 + 1 = (4 * k + 3) + k from by ring,
      show 1 + 2 * (3 * k + 1) = 6 * k + 3 from by ring]
  apply stepStar_trans (r5r1_chain k (4 * k + 3))
  -- At (0, 1, 0, 0, 4k+3, 6k+3). Final R5.
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 2, 3⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨1, 0, 0, 0, 2 * k, 3 * k⟩) 1
  intro k; exact ⟨2 * k + 1, main_trans k⟩
