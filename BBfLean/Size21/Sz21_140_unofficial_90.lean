import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz21_140_unofficial #90: [5/6, 77/2, 4/35, 9/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  1
 2  0 -1 -1  0
 0  2  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_90

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: drain d into b
theorem r4_drain : ∀ k, ∀ B D E, ⟨0, B, 0, D+k, E⟩ [fm]⊢* ⟨0, B+2*k, 0, D, E⟩ := by
  intro k; induction' k with k h <;> intro B D E
  · exists 0
  rw [show D + (k + 1) = (D + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R5,R1,R3,R1,R1 interleaving: b -= 3, c += 2, e -= 1
theorem round5 : ∀ k, ∀ B C E, ⟨0, B+3*k, C, 0, E+k⟩ [fm]⊢* ⟨0, B, C+2*k, 0, E⟩ := by
  intro k; induction' k with k h <;> intro B C E
  · exists 0
  rw [show B + 3 * (k + 1) = (B + 3 * k) + 3 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm
  rw [show B + 3 * k + 3 = (B + 3 * k + 2) + 1 from by ring]
  step fm
  step fm
  rw [show B + 3 * k + 2 = (B + 3 * k + 1) + 1 from by ring]
  step fm
  rw [show B + 3 * k + 1 = (B + 3 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3,R2,R2 drain: c -= 1, d += 1, e += 2
theorem r3r2r2_drain : ∀ k, ∀ C D E, ⟨0, 0, C+k, D+1, E⟩ [fm]⊢* ⟨0, 0, C, D+1+k, E+2*k⟩ := by
  intro k; induction' k with k h <;> intro C D E
  · exists 0
  rw [show C + (k + 1) = (C + k) + 1 from by ring]
  step fm
  step fm
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase B for a=0
theorem phaseB_a0 : ∀ C, ∀ F, ⟨0, 0, C, 0, F+1⟩ [fm]⊢* ⟨0, 0, 0, C+2, F+1+2*C⟩ := by
  intro C F
  step fm
  step fm
  have h := r3r2r2_drain C 0 1 (F + 1)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Phase B for a=1
theorem phaseB_a1 : ∀ C, ∀ F, ⟨1, 0, C+1, 0, F⟩ [fm]⊢* ⟨0, 0, 0, C+2, F+2*C+3⟩ := by
  intro C F
  step fm
  step fm
  step fm
  step fm
  have h := r3r2r2_drain C 0 1 (F + 3)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Phase B for a=2
theorem phaseB_a2 : ∀ C, ∀ F, ⟨2, 0, C, 0, F⟩ [fm]⊢* ⟨0, 0, 0, C+2, F+2*C+2⟩ := by
  intro C F
  step fm
  step fm
  have h := r3r2r2_drain C 0 1 (F + 2)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Tail for d ≡ 1 (mod 3)
theorem tail_mod1 : ∀ C E, ⟨0, 2, C, 0, E+1⟩ [fm]⊢* ⟨1, 0, C+1, 0, E⟩ := by
  intro C E
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  finish

-- Tail for d ≡ 2 (mod 3)
theorem tail_mod2 : ∀ C E, ⟨0, 4, C, 0, E+2⟩ [fm]⊢* ⟨2, 0, C+2, 0, E⟩ := by
  intro C E
  step fm
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  step fm
  step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  step fm
  finish

-- Transition for d ≡ 0 (mod 3): d = 3(m+1)
theorem trans_mod0 (m E : ℕ) : ⟨0, 0, 0, 3*m+3, E+2*m+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*m+6, E+8*m+9⟩ := by
  rw [show 3 * m + 3 = (3 * m + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, (3 * m + 2) + 1, E + 2 * m + 3⟩ = some ⟨0, 2, 0, 3 * m + 2, E + 2 * m + 3⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 6*m+6, 0, 0, E+2*m+3⟩)
  · rw [show 3 * m + 2 = 0 + (3 * m + 2) from by ring,
        show 6 * m + 6 = 2 + 2 * (3 * m + 2) from by ring]
    exact r4_drain (3*m+2) 2 0 (E+2*m+3)
  apply stepStar_trans (c₂ := ⟨0, 0, 4*m+4, 0, E+1⟩)
  · rw [show 6 * m + 6 = 0 + 3 * (2 * m + 2) from by ring,
        show E + 2 * m + 3 = E + 1 + (2 * m + 2) from by ring,
        show 4 * m + 4 = 0 + 2 * (2 * m + 2) from by ring]
    exact round5 (2*m+2) 0 0 (E+1)
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 4*m+4+2, E+1+2*(4*m+4)⟩)
  · rw [show E + 1 = E + 1 from rfl]
    exact phaseB_a0 (4*m+4) E
  ring_nf; finish

-- Transition for d ≡ 1 (mod 3): d = 3m+1
theorem trans_mod1 (m E : ℕ) : ⟨0, 0, 0, 3*m+1, E+2*m+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*m+2, E+8*m+3⟩ := by
  rw [show 3 * m + 1 = (3 * m) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 3 * m + 1, E + 2 * m + 1⟩ = some ⟨0, 2, 0, 3 * m, E + 2 * m + 1⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 6*m+2, 0, 0, E+2*m+1⟩)
  · rw [show 3 * m = 0 + 3 * m from by ring,
        show 6 * m + 2 = 2 + 2 * (3 * m) from by ring]
    exact r4_drain (3*m) 2 0 (E+2*m+1)
  apply stepStar_trans (c₂ := ⟨0, 2, 4*m, 0, E+1⟩)
  · rw [show 6 * m + 2 = 2 + 3 * (2 * m) from by ring,
        show E + 2 * m + 1 = E + 1 + 2 * m from by ring,
        show 4 * m = 0 + 2 * (2 * m) from by ring]
    exact round5 (2*m) 2 0 (E+1)
  apply stepStar_trans (c₂ := ⟨1, 0, 4*m+1, 0, E⟩)
  · rw [show E + 1 = E + 1 from rfl]
    exact tail_mod1 (4*m) E
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 4*m+2, E+2*(4*m)+3⟩)
  · rw [show 4 * m + 1 = 4 * m + 1 from rfl]
    exact phaseB_a1 (4*m) E
  ring_nf; finish

-- Transition for d ≡ 2 (mod 3): d = 3m+2
theorem trans_mod2 (m E : ℕ) : ⟨0, 0, 0, 3*m+2, E+2*m+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*m+4, E+8*m+6⟩ := by
  rw [show 3 * m + 2 = (3 * m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, (3 * m + 1) + 1, E + 2 * m + 2⟩ = some ⟨0, 2, 0, 3 * m + 1, E + 2 * m + 2⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 6*m+4, 0, 0, E+2*m+2⟩)
  · rw [show 3 * m + 1 = 0 + (3 * m + 1) from by ring,
        show 6 * m + 4 = 2 + 2 * (3 * m + 1) from by ring]
    exact r4_drain (3*m+1) 2 0 (E+2*m+2)
  apply stepStar_trans (c₂ := ⟨0, 4, 4*m, 0, E+2⟩)
  · rw [show 6 * m + 4 = 4 + 3 * (2 * m) from by ring,
        show E + 2 * m + 2 = E + 2 + 2 * m from by ring,
        show 4 * m = 0 + 2 * (2 * m) from by ring]
    exact round5 (2*m) 4 0 (E+2)
  apply stepStar_trans (c₂ := ⟨2, 0, 4*m+2, 0, E⟩)
  · exact tail_mod2 (4*m) E
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 4*m+2+2, E+2*(4*m+2)+2⟩)
  · exact phaseB_a2 (4*m+2) E
  ring_nf; finish

-- Unified transition using mod 3 case split
theorem main_trans (d : ℕ) (hd : d ≥ 1) (e : ℕ) (he : e ≥ d) :
    ∃ d' e', d' ≥ 1 ∧ e' ≥ d' ∧ ⟨0, 0, 0, d, e⟩ [fm]⊢⁺ ⟨0, 0, 0, d', e'⟩ := by
  have hmod := Nat.div_add_mod d 3
  set q := d / 3
  set r := d % 3
  have hr : r < 3 := Nat.mod_lt d (by omega)
  interval_cases r
  · rcases q with _ | k
    · omega
    obtain ⟨E, hE⟩ : ∃ E, e = E + (2 * k + 3) := ⟨e - (2*k+3), by omega⟩
    rw [show d = 3 * k + 3 from by omega, hE]
    exact ⟨4*k+6, E+8*k+9, by omega, by omega, trans_mod0 k E⟩
  · obtain ⟨E, hE⟩ : ∃ E, e = E + (2 * q + 1) := ⟨e - (2*q+1), by omega⟩
    rw [show d = 3 * q + 1 from by omega, hE]
    exact ⟨4*q+2, E+8*q+3, by omega, by omega, trans_mod1 q E⟩
  · obtain ⟨E, hE⟩ : ∃ E, e = E + (2 * q + 2) := ⟨e - (2*q+2), by omega⟩
    rw [show d = 3 * q + 2 from by omega, hE]
    exact ⟨4*q+4, E+8*q+6, by omega, by omega, trans_mod2 q E⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 3⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 1 ∧ e ≥ d)
  · intro c ⟨d, e, hq, hd, he⟩; subst hq
    obtain ⟨d', e', hd', he', htrans⟩ := main_trans d hd e he
    exact ⟨⟨0, 0, 0, d', e'⟩, ⟨d', e', rfl, hd', he'⟩, htrans⟩
  · exact ⟨2, 3, rfl, by omega, by omega⟩
