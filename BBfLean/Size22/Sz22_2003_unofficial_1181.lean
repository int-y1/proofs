import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1181: [5/6, 49/2, 44/35, 9/11, 10/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  2  0  0 -1
 1  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1181

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 chain: (0, b, 0, d, e+k) →* (0, b+2*k, 0, d, e)
theorem r4_chain : ∀ k b d e, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

-- R3-R2-R2 chain: (0, 0, c+k, d+1, e) →* (0, 0, c, d+3*k+1, e+k)
theorem r3r2r2_chain : ∀ k c d e, ⟨(0 : ℕ), 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 3 * k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 2 + 2 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 1))
    ring_nf; finish

-- R3-R1-R1 chain: (0, b+2*k, c+1, d+k, e) →* (0, b, c+k+1, d, e+k)
theorem r3r1r1_chain : ∀ k b c d e, ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨0, b, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    ring_nf; finish

-- Main transition for e = 0: (0, 0, 0, d+1, 0) →⁺ (0, 0, 0, d+5, 1)
theorem trans_e0 : ⟨(0 : ℕ), 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 5, 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Main transition for e ≥ 1:
-- (0, 0, 0, d+e+2, e+1) →⁺ (0, 0, 0, d+3*e+8, 2*e+3)
theorem trans_epos : ⟨(0 : ℕ), 0, 0, d + e + 2, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 3 * e + 8, 2 * e + 3⟩ := by
  -- Phase 1: R4 chain, move e+1 to b
  apply stepStar_stepPlus_stepPlus
  · rw [show (e : ℕ) + 1 = 0 + (e + 1) from by ring]
    exact r4_chain (e + 1) 0 (d + e + 2) 0
  -- Now at (0, 0+2*(e+1), 0, d+e+2, 0)
  -- Phase 2: R5 + R1
  rw [show 0 + 2 * (e + 1) = (2 * e + 1) + 1 from by ring,
      show d + e + 2 = (d + e + 1) + 1 from by ring]
  step fm  -- R5: (1, (2*e+1)+1, 1, d+e+1, 0)
  -- Now R1 matches: a+1=1 so a=0, b+1=(2*e+1)+1 so b=2*e+1
  step fm  -- R1: (0, 2*e+1, 2, d+e+1, 0)
  -- State: (0, 2*e+1, 2, d+e+1, 0)
  -- Phase 3: R3-R1-R1 chain
  rw [show 2 * e + 1 = 1 + 2 * e from by ring,
      show d + e + 1 = (d + 1) + e from by ring]
  apply stepStar_trans
  · have h := r3r1r1_chain e 1 1 (d + 1) 0
    convert h using 2
  -- After chain: (0, 1, 1+e+1, d+1, 0+e)
  -- Phase 4: R3, R1, R2
  rw [show 1 + e + 1 = (e + 1) + 1 from by omega,
      show d + 1 = (d + 0) + 1 from by omega,
      show 0 + e = e from by omega]
  step fm  -- R3
  step fm  -- R1
  step fm  -- R2
  -- Phase 5: R3-R2-R2 chain
  rw [show d + 0 + 2 = (d + 1) + 1 from by omega,
      show e + 1 + 1 = 0 + (e + 2) from by omega]
  apply stepStar_trans
  · exact r3r2r2_chain (e + 2) 0 (d + 1) (e + 1)
  rw [show (d + 1) + 3 * (e + 2) + 1 = d + 3 * e + 8 from by ring,
      show (e + 1) + (e + 2) = 2 * e + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ e + 1)
  · intro c ⟨d, e, hq, hd⟩; subst hq
    rcases e with _ | e
    · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      exact ⟨⟨0, 0, 0, d' + 5, 1⟩, ⟨d' + 5, 1, rfl, by omega⟩, trans_e0⟩
    · obtain ⟨d', rfl⟩ : ∃ d', d = d' + e + 2 := ⟨d - e - 2, by omega⟩
      exact ⟨⟨0, 0, 0, d' + 3 * e + 8, 2 * e + 3⟩,
        ⟨d' + 3 * e + 8, 2 * e + 3, rfl, by omega⟩, trans_epos⟩
  · exact ⟨2, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1181
