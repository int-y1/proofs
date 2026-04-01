import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1173: [5/6, 49/2, 44/35, 27/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  3  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1173

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: drain e to b.
theorem e_to_b : ∀ k b, ⟨(0:ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + 3 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 3))
    ring_nf; finish

-- R3,R1,R1 interleave chain (even b).
theorem r311_chain : ∀ k c d e, ⟨(0:ℕ), 2 * k, c + 1, d + k, e⟩ [fm]⊢*
    ⟨0, 0, c + 1 + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- R3,R1,R2 chain for odd b remainder.
theorem r312_chain : ∀ k c d e, ⟨(0:ℕ), 2 * k + 1, c + 1, d + k + 1, e⟩ [fm]⊢*
    ⟨0, 0, c + k + 1, d + 2, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 from by ring,
        show d + (k + 1) + 1 = (d + k + 1) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- R3,R2,R2 drain chain.
theorem r322_chain : ∀ k d e, ⟨(0:ℕ), 0, k + 1, d + 1, e⟩ [fm]⊢*
    ⟨0, 0, 0, d + 3 * k + 4, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · step fm; step fm; step fm; ring_nf; finish
  · step fm
    step fm
    step fm
    apply stepStar_trans (ih (d + 3) (e + 1))
    ring_nf; finish

-- Even case: E = 2m.
theorem trans_even (d m : ℕ) : ⟨(0:ℕ), 0, 0, d + 3 * m + 2, 2 * m⟩ [fm]⊢⁺
    ⟨0, 0, 0, d + 9 * m + 4, 6 * m + 1⟩ := by
  -- Phase 1: R4 x 2m
  apply stepStar_stepPlus_stepPlus
  · rw [show (2 * m : ℕ) = 0 + 2 * m from by ring]
    exact e_to_b (2 * m) 0 (d := d + 3 * m + 2) (e := 0)
  -- After R4: (0, 6m, 0, d+3m+2, 0). R5 step.
  rw [show 0 + 3 * (2 * m) = 6 * m from by ring,
      show d + 3 * m + 2 = (d + 3 * m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 6 * m, 0, (d + 3 * m + 1) + 1, 0⟩ = some ⟨0, 6 * m, 1, d + 3 * m + 1, 0⟩
    simp [fm]
  -- Phase 3: r311_chain with k=3m
  rw [show d + 3 * m + 1 = (d + 1) + 3 * m from by ring,
      show 6 * m = 2 * (3 * m) from by ring]
  apply stepStar_trans (r311_chain (3 * m) 0 (d + 1) 0)
  -- Phase 4: r322_chain
  rw [show 0 + 1 + 3 * m = (3 * m) + 1 from by ring,
      show 0 + 3 * m = 3 * m from by ring]
  apply stepStar_trans (r322_chain (3 * m) d (3 * m))
  ring_nf; finish

-- Odd case: E = 2m+1.
theorem trans_odd (d m : ℕ) : ⟨(0:ℕ), 0, 0, d + 3 * m + 4, 2 * m + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, d + 9 * m + 9, 6 * m + 4⟩ := by
  -- Phase 1: R4 x (2m+1)
  apply stepStar_stepPlus_stepPlus
  · rw [show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by ring]
    exact e_to_b (2 * m + 1) 0 (d := d + 3 * m + 4) (e := 0)
  -- After R4: (0, 6m+3, 0, d+3m+4, 0). R5 step.
  rw [show 0 + 3 * (2 * m + 1) = 6 * m + 3 from by ring,
      show d + 3 * m + 4 = (d + 3 * m + 3) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 6 * m + 3, 0, (d + 3 * m + 3) + 1, 0⟩ = some ⟨0, 6 * m + 3, 1, d + 3 * m + 3, 0⟩
    simp [fm]
  -- Phase 3: r312_chain with k=3m+1, d_param=d+1
  rw [show 6 * m + 3 = 2 * (3 * m + 1) + 1 from by ring,
      show d + 3 * m + 3 = (d + 1) + (3 * m + 1) + 1 from by ring]
  apply stepStar_trans (r312_chain (3 * m + 1) 0 (d + 1) 0)
  -- After r312_chain: (0, 0, 0+(3m+1)+1, (d+1)+2, 0+(3m+1)+1)
  -- r322_chain needs (0, 0, k+1, d'+1, e) with k=3m+1, d'=d+2
  show ⟨(0:ℕ), 0, 0 + (3 * m + 1) + 1, (d + 1) + 2, 0 + (3 * m + 1) + 1⟩ [fm]⊢*
    ⟨0, 0, 0, d + 9 * m + 9, 6 * m + 4⟩
  rw [show 0 + (3 * m + 1) + 1 = (3 * m + 1) + 1 from by ring,
      show (d + 1) + 2 = (d + 2) + 1 from by ring]
  apply stepStar_trans (r322_chain (3 * m + 1) (d + 2) ((3 * m + 1) + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ 2 * D ≥ 3 * E + 4)
  · intro c ⟨D, E, hq, hinv⟩; subst hq
    rcases Nat.even_or_odd E with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      obtain ⟨d, rfl⟩ : ∃ d, D = d + 3 * m + 2 := ⟨D - (3 * m + 2), by omega⟩
      exact ⟨⟨0, 0, 0, d + 9 * m + 4, 6 * m + 1⟩,
        ⟨d + 9 * m + 4, 6 * m + 1, rfl, by omega⟩, trans_even d m⟩
    · subst hm
      obtain ⟨d, rfl⟩ : ∃ d, D = d + 3 * m + 4 := ⟨D - (3 * m + 4), by omega⟩
      exact ⟨⟨0, 0, 0, d + 9 * m + 9, 6 * m + 4⟩,
        ⟨d + 9 * m + 9, 6 * m + 4, rfl, by omega⟩, trans_odd d m⟩
  · exact ⟨2, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1173
