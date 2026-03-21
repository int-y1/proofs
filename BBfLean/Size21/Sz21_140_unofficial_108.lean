import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #108: [7/30, 9/2, 44/21, 5/11, 7/3]

Vector representation:
```
-1 -1 -1  1  0
-1  2  0  0  0
 2 -1  0 -1  1
 0  0  1  0 -1
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_108

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: e → c
theorem e_to_c : ∀ k, ∀ b c, ⟨0, b, c, 0, k⟩ [fm]⊢* ⟨0, b, c+k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; apply stepStar_trans (ih _ _); ring_nf; finish

-- R1,R1,R3 round
theorem r1r1r3_round : ⟨2, b+3, c+2, d, e⟩ [fm]⊢* ⟨2, b, c, d+1, e+1⟩ := by
  rw [show (2:ℕ) = 1+1 from by ring, show b+3 = (b+2)+1 from by ring,
      show c+2 = (c+1)+1 from by ring]
  step fm; step fm
  rw [show d+1+1 = (d+1)+1 from by ring]
  step fm; finish

-- Chain of k R1,R1,R3 rounds
theorem r1r1r3_chain : ∀ k, ∀ b c d e,
    ⟨2, b+3*k, c+2*k, d, e⟩ [fm]⊢* ⟨2, b, c, d+k, e+k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  apply stepStar_trans r1r1r3_round
  apply stepStar_trans (ih _ _ _ _); ring_nf; finish

-- R3,R2,R2 round
theorem r3r2r2_round : ⟨0, b+1, 0, d+1, e⟩ [fm]⊢* ⟨0, (b+3)+1, 0, d, e+1⟩ := by
  step fm
  rw [show (2:ℕ) = 1+1 from by ring]
  step fm; step fm; ring_nf; finish

-- Chain of k R3,R2,R2 rounds
theorem r3r2r2_chain : ∀ k, ∀ b d e,
    ⟨0, b+1, 0, d+k, e⟩ [fm]⊢* ⟨0, (b+3*k)+1, 0, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  apply stepStar_trans r3r2r2_round
  apply stepStar_trans (ih (b+3) d (e+1)); ring_nf; finish

-- R2,R2
theorem r2r2 : ⟨2, b, 0, d, e⟩ [fm]⊢* ⟨0, b+4, 0, d, e⟩ := by
  rw [show (2:ℕ) = 1+1 from by ring]
  step fm; step fm; ring_nf; finish

-- R1 then R2
theorem r1_r2 : ⟨2, b+1, 1, d, e⟩ [fm]⊢* ⟨0, b+2, 0, d+1, e⟩ := by
  rw [show (2:ℕ) = 1+1 from by ring, show (1:ℕ) = 0+1 from by ring]
  step fm; step fm; ring_nf; finish

-- Main transition for even case: n = 2*m
theorem main_even (m : ℕ) :
    ⟨0, 4*m+2, 0, 0, 2*m⟩ [fm]⊢⁺ ⟨0, 4*m+4, 0, 0, 2*m+1⟩ := by
  -- Phase 1: e → c
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 4*m+2, 2*m, 0, 0⟩)
  · have h := e_to_c (2*m) (4*m+2) 0
    rw [show 0 + 2 * m = 2 * m from by ring] at h; exact h
  -- Phase 2: R5
  rw [show 4*m+2 = (4*m+1)+1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, (4*m+1)+1, 2*m, 0, 0⟩ = some ⟨0, 4*m+1, 2*m, 1, 0⟩; simp [fm]
  -- Phase 3: R3
  apply stepStar_trans (c₂ := ⟨2, 4*m, 2*m, 0, 1⟩)
  · rw [show 4*m+1 = (4*m)+1 from by ring, show (1:ℕ) = 0+1 from by ring]
    step fm; finish
  -- Phase 4: R1,R1,R3 chain × m
  apply stepStar_trans (c₂ := ⟨2, m, 0, m, m+1⟩)
  · have h := r1r1r3_chain m m 0 0 1
    rw [show m + 3 * m = 4 * m from by ring,
        show 0 + 2 * m = 2 * m from by ring,
        show 0 + m = m from by ring,
        show 1 + m = m + 1 from by ring] at h; exact h
  -- Phase 5: R2,R2
  apply stepStar_trans (c₂ := ⟨0, m+4, 0, m, m+1⟩)
  · exact r2r2
  -- Phase 6: R3,R2,R2 chain × m
  rw [show m + 4 = (m + 3) + 1 from by ring]
  have h6 := r3r2r2_chain m (m+3) 0 (m+1)
  rw [show 0 + m = m from by ring] at h6
  refine stepStar_trans h6 ?_
  ring_nf; finish

-- Main transition for odd case: n = 2*m+1
theorem main_odd (m : ℕ) :
    ⟨0, 4*m+4, 0, 0, 2*m+1⟩ [fm]⊢⁺ ⟨0, 4*m+6, 0, 0, 2*m+2⟩ := by
  -- Phase 1: e → c
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 4*m+4, 2*m+1, 0, 0⟩)
  · have h := e_to_c (2*m+1) (4*m+4) 0
    rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring] at h; exact h
  -- Phase 2: R5
  rw [show 4*m+4 = (4*m+3)+1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, (4*m+3)+1, 2*m+1, 0, 0⟩ = some ⟨0, 4*m+3, 2*m+1, 1, 0⟩; simp [fm]
  -- Phase 3: R3
  apply stepStar_trans (c₂ := ⟨2, 4*m+2, 2*m+1, 0, 1⟩)
  · rw [show 4*m+3 = (4*m+2)+1 from by ring, show (1:ℕ) = 0+1 from by ring]
    step fm; finish
  -- Phase 4: R1,R1,R3 chain × m
  apply stepStar_trans (c₂ := ⟨2, m+2, 1, m, m+1⟩)
  · have h := r1r1r3_chain m (m+2) 1 0 1
    rw [show m + 2 + 3 * m = 4 * m + 2 from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring,
        show 0 + m = m from by ring,
        show 1 + m = m + 1 from by ring] at h; exact h
  -- Phase 5: R1,R2
  apply stepStar_trans (c₂ := ⟨0, m+3, 0, m+1, m+1⟩)
  · rw [show m + 2 = (m + 1) + 1 from by ring]
    have h := @r1_r2 (m+1) m (m+1)
    rw [show m + 1 + 2 = m + 3 from by ring] at h; exact h
  -- Phase 6: R3,R2,R2 chain × (m+1)
  rw [show m + 3 = (m + 2) + 1 from by ring]
  have h := r3r2r2_chain (m+1) (m+2) 0 (m+1)
  rw [show 0 + (m + 1) = m + 1 from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Main transition combining both parities
theorem main_trans (n : ℕ) :
    ⟨0, 2*n+2, 0, 0, n⟩ [fm]⊢⁺ ⟨0, 2*n+4, 0, 0, n+1⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    have h := main_even m
    rw [show 4 * m + 2 = 2 * (2 * m) + 2 from by ring,
        show 4 * m + 4 = 2 * (2 * m) + 4 from by ring,
        show (2 * m + 1 : ℕ) = 2 * m + 1 from rfl] at h; exact h
  · subst hm
    have h := main_odd m
    rw [show 4 * m + 4 = 2 * (2 * m + 1) + 2 from by ring,
        show 4 * m + 6 = 2 * (2 * m + 1) + 4 from by ring,
        show 2 * m + 2 = 2 * m + 1 + 1 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 4, 0, 0, 1⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 2*n+2, 0, 0, n⟩) 1
  intro n; exact ⟨n+1, main_trans n⟩
