import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #35: [35/6, 143/2, 4/55, 3/7, 15/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_35

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R4 repeated: d → b
theorem d_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Interleaved R1R1R3 rounds
theorem r1r1r3_rounds : ∀ k, ∀ B C D E Φ,
    ⟨2, B+2*k, C, D, E+k, Φ⟩ [fm]⊢* ⟨2, B, C+k, D+2*k, E, Φ⟩ := by
  intro k; induction' k with k h <;> intro B C D E Φ
  · exists 0
  rw [show B + 2 * (k + 1) = (B + 2 * k) + 1 + 1 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm
  rw [show B + 2 * k + 1 = (B + 2 * k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _ _ _ _)
  ring_nf; finish

-- Drain phase: c → e,f
theorem drain : ∀ k, ∀ c d e f,
    ⟨2, 0, c+k, d, e, f⟩ [fm]⊢* ⟨2, 0, c, d, e+k, f+2*k⟩ := by
  intro k; induction' k with k h <;> intro c d e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  step fm
  rw [show e + 1 + 1 = (e + 1) + 1 from by ring,
      show f + 1 + 1 = f + 2 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Even transition
theorem main_trans_even (m : ℕ) :
    ⟨0, 0, 0, 2*m, 2*m+1, (2*m+1)*(m+1)⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*m+1, 2*m+2, (m+1)*(2*m+3)⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*m, 0, 0, 2*m+1, (2*m+1)*(m+1)⟩)
  · have h := d_to_b (2*m) 0 0 (e := 2*m+1) (f := (2*m+1)*(m+1))
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*m+1, 1, 0, 2*m+1, m*(2*m+3)⟩)
  · show fm ⟨0, 2*m, 0, 0, 2*m+1, (2*m+1)*(m+1)⟩ = some ⟨0, 2*m+1, 1, 0, 2*m+1, m*(2*m+3)⟩
    simp [fm]
    ring_nf
  apply stepStar_trans (c₂ := ⟨2, 2*m+1, 0, 0, 2*m, m*(2*m+3)⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨2, 1, m, 2*m, m, m*(2*m+3)⟩)
  · have h := r1r1r3_rounds m 1 0 0 m (m*(2*m+3))
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨1, 0, m+1, 2*m+1, m, m*(2*m+3)⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨0, 0, m+1, 2*m+1, m+1, (2*m+1)*(m+1)⟩)
  · have hstep : fm ⟨0+1, 0, m+1, 2*m+1, m, m*(2*m+3)⟩ =
      some ⟨0, 0, m+1, 2*m+1, m+1, m*(2*m+3)+1⟩ := by simp [fm]
    have : m*(2*m+3)+1 = (2*m+1)*(m+1) := by ring
    rw [this] at hstep
    exact step_stepStar hstep
  apply stepStar_trans (c₂ := ⟨2, 0, m, 2*m+1, m, (2*m+1)*(m+1)⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨2, 0, 0, 2*m+1, 2*m, (2*m+1)*(m+1)+2*m⟩)
  · have h := drain m 0 (2*m+1) m ((2*m+1)*(m+1))
    simp only [Nat.zero_add] at h; convert h using 2; ring_nf
  step fm; step fm
  have : (2*m+1)*(m+1)+2*m+1+1 = (m+1)*(2*m+3) := by ring
  rw [this]; finish

-- Odd transition
theorem main_trans_odd (m : ℕ) :
    ⟨0, 0, 0, 2*m+1, 2*m+2, (m+1)*(2*m+3)⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*m+2, 2*m+3, (2*m+3)*(m+2)⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*m+1, 0, 0, 2*m+2, (m+1)*(2*m+3)⟩)
  · have h := d_to_b (2*m+1) 0 0 (e := 2*m+2) (f := (m+1)*(2*m+3))
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*m+2, 1, 0, 2*m+2, (2*m+1)*(m+2)⟩)
  · show fm ⟨0, 2*m+1, 0, 0, 2*m+2, (m+1)*(2*m+3)⟩ = some ⟨0, 2*m+2, 1, 0, 2*m+2, (2*m+1)*(m+2)⟩
    simp [fm]
    ring_nf
  apply stepStar_trans (c₂ := ⟨2, 2*m+2, 0, 0, 2*m+1, (2*m+1)*(m+2)⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨2, 0, m+1, 2*(m+1), m, (2*m+1)*(m+2)⟩)
  · have h := r1r1r3_rounds (m+1) 0 0 0 m ((2*m+1)*(m+2))
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨2, 0, 0, 2*(m+1), 2*m+1, (2*m+1)*(m+2)+2*(m+1)⟩)
  · have h := drain (m+1) 0 (2*(m+1)) m ((2*m+1)*(m+2))
    simp only [Nat.zero_add] at h; convert h using 2; ring_nf
  step fm; step fm
  have : (2*m+1)*(m+2)+2*(m+1)+1+1 = (2*m+3)*(m+2) := by ring
  rw [show 2*(m+1) = 2*m+2 from by ring] at this ⊢
  rw [this]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2, 3⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ (∃ m, q = ⟨0, 0, 0, 2*m, 2*m+1, (2*m+1)*(m+1)⟩ ∧ m ≥ 1) ∨
                   (∃ m, q = ⟨0, 0, 0, 2*m+1, 2*m+2, (m+1)*(2*m+3)⟩))
  · intro c hc
    rcases hc with ⟨m, hq, hm⟩ | ⟨m, hq⟩
    · subst hq
      exact ⟨⟨0, 0, 0, 2*m+1, 2*m+2, (m+1)*(2*m+3)⟩,
             Or.inr ⟨m, rfl⟩,
             main_trans_even m⟩
    · subst hq
      refine ⟨⟨0, 0, 0, 2*(m+1), 2*(m+1)+1, (2*(m+1)+1)*((m+1)+1)⟩,
             Or.inl ⟨m+1, ?_, by omega⟩,
             ?_⟩
      · congr 1
      · have h := main_trans_odd m
        convert h using 2
  · exact Or.inr ⟨0, by norm_num⟩

end Sz21_140_unofficial_35
