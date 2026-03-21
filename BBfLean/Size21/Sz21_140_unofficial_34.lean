import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #34: [35/6, 143/2, 4/55, 3/7, 14/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_34

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

-- R4 repeated: d → b
theorem d_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d+k, E, F⟩ [fm]⊢* ⟨0, b+k, 0, d, E, F⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3,R2,R2 chain: from (0, 0, c+k, D, e+1, F) →* (0, 0, c, D, e+1+k, F+2*k)
theorem r3r2r2_chain : ∀ k, ∀ c e F, ⟨0, 0, c+k, D, e+1, F⟩ [fm]⊢* ⟨0, 0, c, D, e+1+k, F+2*k⟩ := by
  intro k; induction' k with k ih <;> intro c e F
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm  -- R3
  step fm  -- R2
  step fm  -- R2
  rw [show e + 2 = (e + 1) + 1 from by ring,
      show F + 1 + 1 = F + 2 from by ring]
  apply stepStar_trans (ih c (e + 1) (F + 2))
  ring_nf; finish

-- R1,R1,R3 chain for even b:
-- (2, 2k, C, D, E+k, F) →* (2, 0, C+k, D+2k, E, F)
theorem r1r1r3_chain : ∀ k, ∀ C D E, ⟨2, 2*k, C, D, E+k, F⟩ [fm]⊢* ⟨2, 0, C+k, D+2*k, E, F⟩ := by
  intro k; induction' k with k ih <;> intro C D E
  · exists 0
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm  -- R1
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm  -- R1
  rw [show E + k + 1 = (E + k) + 1 from by ring]
  step fm  -- R3
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Middle phase lemma:
-- (1, 2m, C, D, E+m, f) →* (0, 0, C+m, D+2m, E+1, f+1)
theorem mid_phase : ∀ m, ∀ C D E f, ⟨1, 2*m, C, D, E+m, f⟩ [fm]⊢* ⟨0, 0, C+m, D+2*m, E+1, f+1⟩ := by
  intro m; induction' m with m ih <;> intro C D E f
  · step fm; finish
  · rw [show 2 * (m + 1) = (2 * m + 1) + 1 from by ring,
        show E + (m + 1) = (E + m) + 1 from by ring]
    step fm  -- R1
    rw [show E + m + 1 = (E + m) + 1 from by ring]
    step fm  -- R3
    rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
    step fm  -- R1
    apply stepStar_trans (ih (C+1) (D+2) E f)
    ring_nf; finish

-- Main transition for d=0: (0,0,0,0,1,f+1) ⊢⁺ (0,0,0,1,2,f+1)
theorem main_trans_d0 : ∀ f, ⟨0, 0, 0, 0, 1, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, 2, f+1⟩ := by
  intro f; step fm; step fm; finish

-- Main transition for odd d = 2m+1:
theorem main_trans_odd (m : ℕ) : ∀ f, ⟨0, 0, 0, 2*m+1, 2*m+2, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+2, 2*m+3, f+2*m+2⟩ := by
  intro f
  -- Phase 1: R4 x (2m+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*m+1, 0, 0, 2*m+2, f+1⟩)
  · have := d_to_b (E := 2*m+2) (F := f+1) (2*m+1) 0 0
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R5
  apply step_stepStar_stepPlus (c₂ := ⟨1, 2*m+1, 0, 1, 2*m+2, f⟩)
  · show fm ⟨0, 2*m+1, 0, 0, 2*m+2, f+1⟩ = some ⟨1, 2*m+1, 0, 1, 2*m+2, f⟩; simp [fm]
  -- Phase 3: R1
  apply stepStar_trans (c₂ := ⟨0, 2*m, 1, 2, 2*m+2, f⟩)
  · rw [show 2 * m + 1 = (2 * m) + 1 from by ring]; step fm; finish
  -- Phase 4: R3
  apply stepStar_trans (c₂ := ⟨2, 2*m, 0, 2, 2*m+1, f⟩)
  · rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]; step fm; finish
  -- Phase 5: R1,R1,R3 chain x m
  apply stepStar_trans (c₂ := ⟨2, 0, m, 2*m+2, m+1, f⟩)
  · have h := r1r1r3_chain (F := f) m 0 2 (m+1)
    rw [show m + 1 + m = 2 * m + 1 from by ring,
        show 2 + 2 * m = 2 * m + 2 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- Phase 6: R2, R2
  apply stepStar_trans (c₂ := ⟨0, 0, m, 2*m+2, m+3, f+2⟩)
  · step fm; step fm; finish
  -- Phase 7: R3,R2,R2 chain x m
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 2*m+2, m+3+m, f+2+2*m⟩)
  · have h := r3r2r2_chain (D := 2*m+2) (F := f+2) m 0 (m+2)
    simp only [Nat.zero_add] at h; exact h
  ring_nf; finish

-- Main transition for even d = 2(k+1):
theorem main_trans_even (k : ℕ) : ∀ f, ⟨0, 0, 0, 2*k+2, 2*k+3, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*k+3, 2*k+4, f+2*k+3⟩ := by
  intro f
  -- Phase 1: R4 x (2k+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*k+2, 0, 0, 2*k+3, f+1⟩)
  · have := d_to_b (E := 2*k+3) (F := f+1) (2*k+2) 0 0
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R5
  apply step_stepStar_stepPlus (c₂ := ⟨1, 2*k+2, 0, 1, 2*k+3, f⟩)
  · show fm ⟨0, 2*k+2, 0, 0, 2*k+3, f+1⟩ = some ⟨1, 2*k+2, 0, 1, 2*k+3, f⟩; simp [fm]
  -- Phase 3: R1
  apply stepStar_trans (c₂ := ⟨0, 2*k+1, 1, 2, 2*k+3, f⟩)
  · rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]; step fm; finish
  -- Phase 4: R3
  apply stepStar_trans (c₂ := ⟨2, 2*k+1, 0, 2, 2*k+2, f⟩)
  · rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring]; step fm; finish
  -- Phase 5: R1 (peel off one from odd b=2k+1)
  apply stepStar_trans (c₂ := ⟨1, 2*k, 1, 3, 2*k+2, f⟩)
  · rw [show 2 * k + 1 = (2 * k) + 1 from by ring]; step fm; finish
  -- Phase 6: mid_phase(k, 1, 3, k+2, f)
  apply stepStar_trans (c₂ := ⟨0, 0, k+1, 2*k+3, k+3, f+1⟩)
  · have h := mid_phase k 1 3 (k+2) f
    rw [show k + 2 + k = 2 * k + 2 from by ring,
        show 1 + k = k + 1 from by ring,
        show 3 + 2 * k = 2 * k + 3 from by ring,
        show k + 2 + 1 = k + 3 from by ring] at h; exact h
  -- Phase 7: R3,R2,R2 chain x (k+1)
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 2*k+3, k+3+(k+1), f+1+2*(k+1)⟩)
  · have h := r3r2r2_chain (D := 2*k+3) (F := f+1) (k+1) 0 (k+2)
    rw [show 0 + (k + 1) = k + 1 from by ring,
        show k + 2 + 1 = k + 3 from by ring] at h; exact h
  ring_nf; finish

-- Main transition combining all cases
theorem main_trans : ∀ d f, ⟨0, 0, 0, d, d+1, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, d+1, d+2, f+d+1⟩ := by
  intro d f
  rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
  · subst hK
    rcases K with _ | k
    · exact main_trans_d0 f
    · have := main_trans_even k f
      convert this using 1; ring_nf
  · subst hK
    have := main_trans_odd K f
    convert this using 1

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, f⟩ ↦ ⟨0, 0, 0, d, d+1, f+1⟩) ⟨0, 0⟩
  intro ⟨d, f⟩
  refine ⟨⟨d+1, f+d⟩, ?_⟩
  have h := main_trans d f
  convert h using 1
