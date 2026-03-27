import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #93: [1/30, 21/2, 12/77, 5/7, 242/5]

Vector representation:
```
-1 -1 -1  0  0
-1  1  0  1  0
 2  1  0 -1 -1
 0  0  1 -1  0
 1  0 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_93

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- R4 chain: transfer d to c
theorem d_to_c : ∀ k c, ⟨0, b, c, d + k, 0⟩ [fm]⊢* ⟨0, b, c + k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h (c + 1))
  ring_nf; finish

-- R5+R1 alternating chain, then final R5
theorem r5r1_chain : ∀ k m e, ⟨0, m + k, 2 * k + 1, 0, e⟩ [fm]⊢* ⟨1, m, 0, 0, e + 2 * k + 2⟩ := by
  intro k; induction' k with k h <;> intro m e
  · step fm; ring_nf; finish
  rw [show m + (k + 1) = (m + k) + 1 from by ring,
      show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (h m (e + 2))
  ring_nf; finish

-- R3, R2, R2 chain
theorem r3r2r2_chain : ∀ e d b, ⟨0, b, 0, d + 1, e + 1⟩ [fm]⊢* ⟨0, b + 3 * (e + 1), 0, d + e + 2, 0⟩ := by
  intro e; induction' e with e h <;> intro d b
  · step fm; step fm; step fm; ring_nf; finish
  step fm; step fm; step fm
  rw [show b + 1 + 1 + 1 = (b + 3) from by ring,
      show d + 1 + 1 = (d + 1) + 1 from by ring]
  apply stepStar_trans (h (d + 1) (b + 3))
  ring_nf; finish

-- Main transition: C(m,k) = (0, m+k, 0, 2k+1, 0) ->+ C(m+5k+6, k+1)
theorem main_trans (m k : ℕ) :
    ⟨0, m + k, 0, 2 * k + 1, 0⟩ [fm]⊢⁺ ⟨0, (m + 5 * k + 6) + (k + 1), 0, 2 * (k + 1) + 1, 0⟩ := by
  -- Phase 1: d_to_c
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (b := m + k) (d := 0) (2 * k + 1) 0)
  rw [Nat.zero_add]
  -- Phase 2: r5r1_chain
  apply stepStar_stepPlus_stepPlus (r5r1_chain k m 0)
  rw [show 0 + 2 * k + 2 = 2 * k + 2 from by ring]
  -- Phase 3: R2
  step fm
  -- Phase 4: r3r2r2_chain
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (2 * k + 1) 0 (m + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, k⟩ ↦ ⟨0, m + k, 0, 2 * k + 1, 0⟩) ⟨1, 0⟩
  intro ⟨m, k⟩; exact ⟨⟨m + 5 * k + 6, k + 1⟩, main_trans m k⟩

end Sz22_2003_unofficial_93
