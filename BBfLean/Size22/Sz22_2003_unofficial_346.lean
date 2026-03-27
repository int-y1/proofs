import BBfLean.FM
import Mathlib.Tactic.Ring

set_option linter.unnecessarySeqFocus false

/-!
# sz22_2003_unofficial #346: [2/15, 1/154, 3087/2, 11/3, 10/7]

Vector representation:
```
 1 -1 -1  0  0
-1  0  0 -1 -1
-1  2  0  3  0
 0 -1  0  0  1
 1  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_346

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+3, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem b_to_e : ∀ j b d e, ⟨(0 : ℕ), b + j, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + j⟩ := by
  intro j; induction j with
  | zero => intro b d e; exists 0
  | succ j ih =>
    intro b d e
    rw [show b + (j + 1) = (b + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b d (e + 1))
    ring_nf; finish

theorem r5r2_chain : ∀ j c d, ⟨(0 : ℕ), 0, c, d + 2 * j + 1, j⟩ [fm]⊢* ⟨1, 0, c + j + 1, d, 0⟩ := by
  intro j; induction j with
  | zero => intro c d; step fm; finish
  | succ j ih =>
    intro c d
    rw [show d + 2 * (j + 1) + 1 = (d + 2 * j + 1) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

theorem r3r1r1_round : ⟨a + 1, 0, c + 2, d, (0 : ℕ)⟩ [fm]⊢⁺ ⟨a + 2, 0, c, d + 3, 0⟩ := by
  execute fm 3

theorem r3r1r1_iter : ∀ j a c d,
    ⟨a + 1, 0, c + 2 * j, d, (0 : ℕ)⟩ [fm]⊢* ⟨a + 1 + j, 0, c, d + 3 * j, 0⟩ := by
  intro j; induction j with
  | zero => intro a c d; simp; exists 0
  | succ j ih =>
    intro a c d
    rw [show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring]
    apply stepStar_trans (stepPlus_stepStar r3r1r1_round)
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c (d + 3))
    ring_nf; finish

theorem tail_odd : ⟨a + 1, 0, 1, d, (0 : ℕ)⟩ [fm]⊢⁺ ⟨a, 3, 0, d + 6, 0⟩ := by
  execute fm 3

theorem a_expand : ∀ j a b d,
    ⟨a + j, b, 0, d, (0 : ℕ)⟩ [fm]⊢* ⟨a, b + 2 * j, 0, d + 3 * j, 0⟩ := by
  intro j; induction j with
  | zero => intro a b d; simp; exists 0
  | succ j ih =>
    intro a b d
    rw [show a + (j + 1) = (a + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2) (d + 3))
    ring_nf; finish

theorem main_trans_even (m d : ℕ) :
    ⟨(0 : ℕ), 2 * m + 5, 0, d + 4 * m + 12, 0⟩ [fm]⊢⁺
    ⟨0, 2 * m + 8, 0, d + 6 * m + 22, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * m + 5, 0, d + 4 * m + 12, 0⟩ = some ⟨0, 2 * m + 4, 0, d + 4 * m + 12, 1⟩
    rfl
  apply stepStar_trans
  · show ⟨0, 2 * m + 4, 0, d + 4 * m + 12, 1⟩ [fm]⊢* ⟨0, 0, 0, d + 4 * m + 12, 2 * m + 5⟩
    have h := b_to_e (2 * m + 4) 0 (d + 4 * m + 12) 1
    simp only [Nat.zero_add] at h
    convert h using 2 <;> ring_nf
  apply stepStar_trans
  · show ⟨0, 0, 0, d + 4 * m + 12, 2 * m + 5⟩ [fm]⊢* ⟨1, 0, 2 * m + 6, d + 1, 0⟩
    have h := r5r2_chain (2 * m + 5) 0 (d + 1)
    simp only [Nat.zero_add] at h
    convert h using 2 <;> ring_nf
  apply stepStar_trans
  · show ⟨1, 0, 2 * m + 6, d + 1, 0⟩ [fm]⊢* ⟨m + 4, 0, 0, d + 3 * m + 10, 0⟩
    have h := r3r1r1_iter (m + 3) 0 0 (d + 1)
    simp only [Nat.zero_add] at h
    convert h using 2 <;> ring_nf
  have h := a_expand (m + 4) 0 0 (d + 3 * m + 10)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

theorem main_trans_odd (m d : ℕ) :
    ⟨(0 : ℕ), 2 * m + 6, 0, d + 4 * m + 14, 0⟩ [fm]⊢⁺
    ⟨0, 2 * m + 9, 0, d + 6 * m + 25, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * m + 6, 0, d + 4 * m + 14, 0⟩ = some ⟨0, 2 * m + 5, 0, d + 4 * m + 14, 1⟩
    rfl
  apply stepStar_trans
  · show ⟨0, 2 * m + 5, 0, d + 4 * m + 14, 1⟩ [fm]⊢* ⟨0, 0, 0, d + 4 * m + 14, 2 * m + 6⟩
    have h := b_to_e (2 * m + 5) 0 (d + 4 * m + 14) 1
    simp only [Nat.zero_add] at h
    convert h using 2 <;> ring_nf
  apply stepStar_trans
  · show ⟨0, 0, 0, d + 4 * m + 14, 2 * m + 6⟩ [fm]⊢* ⟨1, 0, 2 * m + 7, d + 1, 0⟩
    have h := r5r2_chain (2 * m + 6) 0 (d + 1)
    simp only [Nat.zero_add] at h
    convert h using 2 <;> ring_nf
  apply stepStar_trans
  · show ⟨1, 0, 2 * m + 7, d + 1, 0⟩ [fm]⊢* ⟨m + 4, 0, 1, d + 3 * m + 10, 0⟩
    have h := r3r1r1_iter (m + 3) 0 1 (d + 1)
    simp only [Nat.zero_add] at h
    convert h using 2 <;> ring_nf
  apply stepStar_trans
  · show ⟨m + 4, 0, 1, d + 3 * m + 10, 0⟩ [fm]⊢* ⟨m + 3, 3, 0, d + 3 * m + 16, 0⟩
    exact stepPlus_stepStar tail_odd
  have h := a_expand (m + 3) 0 3 (d + 3 * m + 16)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 5, 0, 12, 0⟩)
  · execute fm 25
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b d : ℕ, q = (⟨0, b + 5, 0, d + 2 * b + 12, 0⟩ : Q))
  · intro q ⟨b, d, hq⟩; subst hq
    rcases Nat.even_or_odd b with ⟨m, hb⟩ | ⟨m, hb⟩
    · subst hb
      refine ⟨⟨0, 2 * m + 8, 0, d + 6 * m + 22, 0⟩,
              ⟨2 * m + 3, d + 2 * m + 4, ?_⟩, ?_⟩
      · congr 1; ring_nf
      · have h := main_trans_even m d
        convert h using 2 <;> ring_nf
    · subst hb
      refine ⟨⟨0, 2 * m + 9, 0, d + 6 * m + 25, 0⟩,
              ⟨2 * m + 4, d + 2 * m + 5, ?_⟩, ?_⟩
      · congr 1; ring_nf
      · have h := main_trans_odd m d
        convert h using 2 <;> ring_nf
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_346
