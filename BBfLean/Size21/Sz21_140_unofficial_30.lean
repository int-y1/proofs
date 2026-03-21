import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #30: [35/6, 121/2, 4/55, 3/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_30

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: d → b
theorem d_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3,R2,R2 drain: c,e → e
theorem r3r2r2_drain : ∀ k, ∀ D E, ⟨0, 0, k, D, E + k⟩ [fm]⊢* ⟨0, 0, 0, D, E + 4 * k⟩ := by
  intro k; induction' k with k h <;> intro D E
  · exists 0
  rw [show E + (k + 1) = (E + k) + 1 from by ring]
  step fm
  step fm
  step fm
  rw [show E + k + 2 + 2 = (E + 4) + k from by ring]
  apply stepStar_trans (h D (E + 4))
  ring_nf; finish

-- R3,R1,R1 rounds: b,e → c,d
theorem r3r1r1_rounds : ∀ k, ∀ B C D E, ⟨0, 2 * k + B, C + 1, D, E + k⟩ [fm]⊢* ⟨0, B, C + k + 1, D + 2 * k, E⟩ := by
  intro k; induction' k with k h <;> intro B C D E
  · simp; exists 0
  rw [show 2 * (k + 1) + B = (2 * k + B) + 2 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm
  step fm
  step fm
  rw [show C + 1 + 1 = (C + 1) + 1 from by ring,
      show D + 1 + 1 = (D + 2) from by ring]
  apply stepStar_trans (h B (C + 1) (D + 2) E)
  ring_nf; finish

-- R3,R1,R2 tail
theorem r3r1r2_tail : ∀ C D E, ⟨0, 1, C + 1, D, E + 1⟩ [fm]⊢* ⟨0, 0, C + 1, D + 1, E + 2⟩ := by
  intro C D E
  step fm
  step fm
  step fm
  finish

-- Even case: d = 2*m
theorem main_trans_even (m E : ℕ) : ⟨0, 0, 0, 2 * m + 1, 2 * m + 2 + E⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * m + 2, 4 * m + 4 + E⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2 * m + 1, 0, 0, 2 * m + 2 + E⟩)
  · have h := d_to_b (2 * m + 1) 0 0 (2 * m + 2 + E)
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨1, 2 * m + 1, 0, 1, 2 * m + 1 + E⟩)
  · rw [show 2 * m + 2 + E = (2 * m + 1 + E) + 1 from by ring]
    show fm ⟨0, 2 * m + 1, 0, 0, (2 * m + 1 + E) + 1⟩ = some ⟨1, 2 * m + 1, 0, 1, 2 * m + 1 + E⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 2 * m, 1, 2, 2 * m + 1 + E⟩)
  · rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
    have : fm ⟨0 + 1, (2 * m) + 1, 0, 1, 2 * m + 1 + E⟩ = some ⟨0, 2 * m, 0 + 1, 1 + 1, 2 * m + 1 + E⟩ := by
      simp [fm]
    exact step_stepStar this
  -- R3R1R1 rounds
  apply stepStar_trans (c₂ := ⟨0, 0, m + 1, 2 + 2 * m, m + 1 + E⟩)
  · rw [show 2 * m = 2 * m + 0 from by ring,
        show 2 * m + 1 + E = (m + 1 + E) + m from by ring]
    have h := r3r1r1_rounds m 0 0 2 (m + 1 + E)
    simp only [Nat.zero_add] at h; exact h
  -- R3R2R2 drain
  rw [show m + 1 + E = E + (m + 1) from by ring]
  apply stepStar_trans (r3r2r2_drain (m + 1) (2 + 2 * m) E)
  ring_nf; finish

-- Odd case: d = 2*m+1
theorem main_trans_odd (m E : ℕ) : ⟨0, 0, 0, 2 * m + 2, 2 * m + 3 + E⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * m + 3, 4 * m + 6 + E⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2 * m + 2, 0, 0, 2 * m + 3 + E⟩)
  · have h := d_to_b (2 * m + 2) 0 0 (2 * m + 3 + E)
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨1, 2 * m + 2, 0, 1, 2 * m + 2 + E⟩)
  · rw [show 2 * m + 3 + E = (2 * m + 2 + E) + 1 from by ring]
    show fm ⟨0, 2 * m + 2, 0, 0, (2 * m + 2 + E) + 1⟩ = some ⟨1, 2 * m + 2, 0, 1, 2 * m + 2 + E⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 2 * m + 1, 1, 2, 2 * m + 2 + E⟩)
  · rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
    have : fm ⟨0 + 1, (2 * m + 1) + 1, 0, 1, 2 * m + 2 + E⟩ = some ⟨0, 2 * m + 1, 0 + 1, 1 + 1, 2 * m + 2 + E⟩ := by
      simp [fm]
    exact step_stepStar this
  -- R3R1R1 rounds
  apply stepStar_trans (c₂ := ⟨0, 1, m + 1, 2 + 2 * m, m + 2 + E⟩)
  · rw [show 2 * m + 1 = 2 * m + 1 from rfl,
        show 2 * m + 2 + E = (m + 2 + E) + m from by ring]
    have h := r3r1r1_rounds m 1 0 2 (m + 2 + E)
    simp only [Nat.zero_add] at h; exact h
  -- R3R1R2 tail
  apply stepStar_trans (c₂ := ⟨0, 0, m + 1, 2 * m + 3, m + 3 + E⟩)
  · rw [show m + 2 + E = (m + 1 + E) + 1 from by ring]
    have h := r3r1r2_tail m (2 + 2 * m) (m + 1 + E)
    rw [show (2 + 2 * m) + 1 = 2 * m + 3 from by ring,
        show m + 1 + E + 2 = m + 3 + E from by ring] at h
    exact h
  -- R3R2R2 drain
  rw [show m + 3 + E = (E + 2) + (m + 1) from by ring]
  apply stepStar_trans (r3r2r2_drain (m + 1) (2 * m + 3) (E + 2))
  ring_nf; finish

-- Combined main transition using parity split
theorem main_trans (d E : ℕ) : ⟨0, 0, 0, d + 1, d + 2 + E⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2, 2 * d + 4 + E⟩ := by
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have h := main_trans_even m E
    convert h using 2; ring_nf
  · subst hm
    have h := main_trans_odd m E
    convert h using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, E⟩ ↦ ⟨0, 0, 0, d + 1, d + 2 + E⟩) ⟨0, 1⟩
  intro ⟨d, E⟩
  exact ⟨⟨d + 1, d + 1 + E⟩, by convert main_trans d E using 2; ring_nf⟩

end Sz21_140_unofficial_30
