import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #36: [35/6, 143/2, 4/55, 3/7, 35/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 0  0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_36

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | _ => none

-- R4 repeated: d → b
theorem d_to_b : ∀ k b d, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- R3-R2-R2 chain: k rounds consuming c
theorem r3r2r2_chain : ∀ k c D e F, ⟨0, 0, c+k, D, e+1, F⟩ [fm]⊢* ⟨0, 0, c, D, e+1+k, F+2*k⟩ := by
  intro k; induction' k with k ih <;> intro c D e F
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show e + 2 = (e + 1) + 1 from by ring]
  apply stepStar_trans (ih c D (e + 1) (F + 2))
  ring_nf; finish

-- R3+R1+R1 chain: k rounds
theorem r3r1r1_chain : ∀ k B C D E F, ⟨0, B+2*k, C+1, D, E+k, F⟩ [fm]⊢* ⟨0, B, C+1+k, D+2*k, E, F⟩ := by
  intro k; induction' k with k ih <;> intro B C D E F
  · exists 0
  rw [show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show C + 2 = (C + 1) + 1 from by ring]
  apply stepStar_trans (ih B (C + 1) (D + 2) E F)
  ring_nf; finish

-- R3+R1+R2 ending (b=1)
theorem r3r1r2_end : ⟨0, 1, C+1, D, E+1, F⟩ [fm]⊢* ⟨0, 0, C+1, D+1, E+1, F+1⟩ := by
  step fm; step fm; step fm; finish

-- Main transition for even d=2K
theorem main_even (K f : ℕ) : ⟨0, 0, 0, 2*K, 2*K+1, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*K+1, 2*K+2, f+2*K+2⟩ := by
  -- R4
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*K, 0, 0, 2*K+1, f+1⟩)
  · have h := d_to_b (2*K) 0 0 (e := 2*K+1) (f := f+1)
    simp only [Nat.zero_add] at h; exact h
  -- R5
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*K, 1, 1, 2*K+1, f⟩)
  · show fm ⟨0, 2*K, 0, 0, 2*K+1, f+1⟩ = some ⟨0, 2*K, 1, 1, 2*K+1, f⟩; simp [fm]
  -- R3R1R1 chain
  apply stepStar_trans (c₂ := ⟨0, 0, K+1, 2*K+1, K+1, f⟩)
  · have h := r3r1r1_chain K 0 0 1 (K+1) f
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- R3R2R2 chain
  have h := r3r2r2_chain (K+1) 0 (2*K+1) K f
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Main transition for odd d=2K+1
theorem main_odd (K f : ℕ) : ⟨0, 0, 0, 2*K+1, 2*K+2, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*K+2, 2*K+3, f+2*K+3⟩ := by
  -- R4
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*K+1, 0, 0, 2*K+2, f+1⟩)
  · have h := d_to_b (2*K+1) 0 0 (e := 2*K+2) (f := f+1)
    simp only [Nat.zero_add] at h; exact h
  -- R5
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*K+1, 1, 1, 2*K+2, f⟩)
  · show fm ⟨0, 2*K+1, 0, 0, 2*K+2, f+1⟩ = some ⟨0, 2*K+1, 1, 1, 2*K+2, f⟩; simp [fm]
  -- R3R1R1 chain
  apply stepStar_trans (c₂ := ⟨0, 1, K+1, 2*K+1, K+2, f⟩)
  · have h := r3r1r1_chain K 1 0 1 (K+2) f
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- R3R1R2 ending
  apply stepStar_trans (c₂ := ⟨0, 0, K+1, 2*K+2, K+2, f+1⟩)
  · rw [show K + 2 = (K + 1) + 1 from by ring]
    have h := @r3r1r2_end K (2*K+1) (K+1) f
    rw [show 2 * K + 1 + 1 = 2 * K + 2 from by ring] at h
    exact h
  -- R3R2R2 chain
  have h := r3r2r2_chain (K+1) 0 (2*K+2) (K+1) (f+1)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Main transition
theorem main_trans (d f : ℕ) : ⟨0, 0, 0, d, d+1, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, d+1, d+2, f+d+2⟩ := by
  rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK; subst hK
    have h := main_even K f
    exact h
  · subst hK
    have h := main_odd K f
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, f⟩ ↦ ⟨0, 0, 0, d, d+1, f+1⟩) ⟨0, 0⟩
  intro ⟨d, f⟩
  exact ⟨⟨d+1, f+d+1⟩, by
    show ⟨0, 0, 0, d, d+1, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, d+1, (d+1)+1, (f+d+1)+1⟩
    rw [show (d + 1) + 1 = d + 2 from by ring,
        show (f + d + 1) + 1 = f + d + 2 from by ring]
    exact main_trans d f⟩
