import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1735: [8/15, 33/14, 5/2, 7/11, 66/5]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 1  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1735

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: move e to d.
theorem e_to_d : ∀ k, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

-- R3 chain: drain a into c.
theorem a_to_c : ∀ k c, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1))
    ring_nf; finish

-- R2+R1 interleaved chain. k rounds from a+2, consuming k from c and d, gaining 2k to a and k to e.
-- Universally quantify all free variables inside induction.
theorem r2_r1_chain : ∀ k, ∀ a c d e, ⟨a + 2, 0, c + k + 1, d + k + 1, e⟩ [fm]⊢* ⟨a + 2 * k + 4, 0, c, d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · step fm -- R2
    step fm -- R1
    ring_nf; finish
  · rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring,
        show d + (k + 1) + 1 = (d + k + 1) + 1 from by ring]
    step fm -- R2
    step fm -- R1
    rw [show a + 1 + 3 = (a + 2) + 2 from by omega]
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, c+e+3, 0, e+1) →⁺ (0, 0, c+2*e+6, 0, e+2)
theorem main_trans (c e : ℕ) : ⟨0, 0, c + e + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * e + 6, 0, e + 2⟩ := by
  -- Phase 1: R4 chain (e+1 steps)
  apply stepStar_stepPlus_stepPlus (e_to_d (e + 1) (c := c + e + 3) (d := 0))
  simp only [Nat.zero_add]
  -- Phase 2: R5 fires: c+e+3 = (c+e+2)+1
  step fm
  -- Phase 3: R1 fires: b=1, c+e+2 = (c+e+1)+1
  step fm
  -- Now at (4, 0, c+e+1, e+1, 1)
  -- Phase 4: R2+R1 chain × (e+1)
  -- We need: (4, 0, c+e+1, e+1, 1) matches (a+2, 0, c'+k+1, d'+k+1, e')
  -- with a=2, k=e, c'=c, d'=0, e'=1: c'+k+1 = c+e+1 ✓, d'+k+1 = e+1 ✓
  rw [show (4 : ℕ) = 2 + 2 from by ring,
      show c + e + 1 = c + e + 1 from rfl,
      show (e + 1 : ℕ) = 0 + e + 1 from by ring]
  apply stepStar_trans (r2_r1_chain e 2 c 0 1)
  -- Now at (2+2*e+4, 0, c, 0, 1+e+1) = (2*e+6, 0, c, 0, e+2)
  -- Phase 5: R3 chain: drain 2*e+6 from a into c
  rw [show 2 + 2 * e + 4 = 2 * e + 6 from by ring,
      show 1 + e + 1 = e + 2 from by ring]
  exact a_to_c (2 * e + 6) c (e := e + 2)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 1⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, e⟩ ↦ ⟨0, 0, c + e + 3, 0, e + 1⟩) ⟨0, 0⟩
  intro ⟨c, e⟩
  refine ⟨⟨c + e + 2, e + 1⟩, ?_⟩
  show ⟨0, 0, c + e + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, (c + e + 2) + (e + 1) + 3, 0, (e + 1) + 1⟩
  rw [show (c + e + 2) + (e + 1) + 3 = c + 2 * e + 6 from by ring,
      show (e + 1) + 1 = e + 2 from by ring]
  exact main_trans c e

end Sz22_2003_unofficial_1735
