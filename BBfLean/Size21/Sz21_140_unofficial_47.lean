import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #47: [35/6, 4/55, 143/2, 3/7, 15/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_47

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R3 repeated: a → e,f (when b=0, c=0)
theorem a_to_ef (d : ℕ) : ∀ k, ∀ a e f, ⟨a+k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e+k, f+k⟩ := by
  intro k; induction' k with k h <;> intro a e f
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 repeated: d → b (when a=0, c=0)
theorem d_to_b (e f : ℕ) : ∀ k, ∀ b d, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R2 repeated: c,e → a (when b=0)
theorem r2_chain (d f : ℕ) : ∀ k, ∀ a c, ⟨a, 0, c+k, d, k, f⟩ [fm]⊢* ⟨a+2*k, 0, c, d, 0, f⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show (k : ℕ) + 1 = k + 1 from rfl]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1R1R2 interleave: 3 steps per round
theorem r1r1r2_one (B C D E F : ℕ) : ⟨2, B+2, C, D, E+1, F⟩ [fm]⊢⁺ ⟨2, B, C+1, D+2, E, F⟩ := by
  rw [show B + 2 = (B + 1) + 1 from by ring]
  step fm
  step fm
  step fm
  finish

-- R1R1R2 rounds by induction
theorem r1r1r2_rounds (B F : ℕ) : ∀ k, ∀ C D E, ⟨2, B+2*k, C, D, E+k, F⟩ [fm]⊢* ⟨2, B, C+k, D+2*k, E, F⟩ := by
  intro k; induction' k with k h <;> intro C D E
  · exists 0
  rw [show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (r1r1r2_one (B + 2 * k) C D (E + k) F))
  have h2 := h (C + 1) (D + 2) E
  rw [show D + 2 + 2 * k = D + 2 * k + 2 from by ring] at h2
  refine stepStar_trans h2 ?_
  ring_nf; finish

-- For even n=2m: (2, 2m+1, 0, 0, 2m, F) →* (2m+1, 0, 1, 2m+1, 0, F)
theorem phase_even_n (m F : ℕ) : ⟨2, 2*m+1, 0, 0, 2*m, F⟩ [fm]⊢* ⟨2*m+1, 0, 1, 2*m+1, 0, F⟩ := by
  apply stepStar_trans (c₂ := ⟨2, 1, m, 2*m, m, F⟩)
  · have h := r1r1r2_rounds 1 F m 0 0 m
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * m = 2 * m + 1 from by ring,
        show m + m = 2 * m from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨1, 0, m+1, 2*m+1, m, F⟩)
  · apply step_stepStar
    show fm ⟨1+1, 0+1, m, 2*m, m, F⟩ = some ⟨1, 0, m+1, 2*m+1, m, F⟩
    simp [fm]
  have h := r2_chain (2*m+1) F m 1 1
  rw [show 1 + m = m + 1 from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- For odd n=2m+1: (2, 2m+2, 0, 0, 2m+1, F) →* (2m+2, 0, 1, 2m+2, 0, F)
theorem phase_odd_n (m F : ℕ) : ⟨2, 2*m+2, 0, 0, 2*m+1, F⟩ [fm]⊢* ⟨2*m+2, 0, 1, 2*m+2, 0, F⟩ := by
  apply stepStar_trans (c₂ := ⟨2, 0, m+1, 2*(m+1), m, F⟩)
  · have h := r1r1r2_rounds 0 F (m+1) 0 0 m
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  have h := r2_chain (2*(m+1)) F m 2 1
  rw [show 1 + m = m + 1 from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- R3+R2 tail: (n+1, 0, 1, d, 0, f) →* (n+2, 0, 0, d, 0, f+1)
theorem r3_r2_tail (n d f : ℕ) : ⟨n+1, 0, 1, d, 0, f⟩ [fm]⊢* ⟨n+2, 0, 0, d, 0, f+1⟩ := by
  apply stepStar_trans (c₂ := ⟨n, 0, 1, d, 1, f+1⟩)
  · apply step_stepStar
    simp [fm]
  apply step_stepStar
  simp [fm]

-- Main transition using two parameters (n, f):
-- (n+1, 0, 0, n, 0, f) →⁺ (n+2, 0, 0, n+1, 0, f+n+1)
theorem main_trans (n f : ℕ) : ⟨n+1, 0, 0, n, 0, f⟩ [fm]⊢⁺ ⟨n+2, 0, 0, n+1, 0, f+n+1⟩ := by
  -- Phase 1: R3 x (n+1) (at least 1 step)
  apply stepPlus_stepStar_stepPlus (c₂ := ⟨0, 0, 0, n, n+1, f+(n+1)⟩)
  · apply step_stepStar_stepPlus (c₂ := ⟨n, 0, 0, n, 1, f+1⟩)
    · simp [fm]
    have h := a_to_ef n n 0 1 (f+1)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  -- Phase 2: R4 x n
  apply stepStar_trans (c₂ := ⟨0, n, 0, 0, n+1, f+(n+1)⟩)
  · have h := d_to_b (n+1) (f+(n+1)) n 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R5
  apply stepStar_trans (c₂ := ⟨0, n+1, 1, 0, n+1, f+n⟩)
  · apply step_stepStar
    rw [show f + (n + 1) = (f + n) + 1 from by ring]
    simp [fm]
  -- R2
  apply stepStar_trans (c₂ := ⟨2, n+1, 0, 0, n, f+n⟩)
  · apply step_stepStar
    simp [fm]
  -- Phase 4: parity split
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = 2*m (even)
    rw [show m + m = 2 * m from by ring] at hm; subst hm
    apply stepStar_trans (c₂ := ⟨2*m+1, 0, 1, 2*m+1, 0, f+2*m⟩)
    · exact phase_even_n m (f + 2 * m)
    exact r3_r2_tail (2*m) (2*m+1) (f+2*m)
  · -- n = 2*m+1 (odd)
    subst hm
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring]
    apply stepStar_trans (c₂ := ⟨2*m+2, 0, 1, 2*m+2, 0, f+(2*m+1)⟩)
    · exact phase_odd_n m (f + (2*m+1))
    refine stepStar_trans (r3_r2_tail (2*m+1) (2*m+2) (f+(2*m+1))) ?_
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ) (fun ⟨n, f⟩ ↦ ⟨n+1, 0, 0, n, 0, f⟩) ⟨0, 0⟩
  intro ⟨n, f⟩; exact ⟨⟨n+1, f+n+1⟩, main_trans n f⟩
