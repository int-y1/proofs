import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #821: [35/6, 8/55, 121/2, 3/7, 35/11]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_821

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem r1_chain : ∀ k, ⟨a + k, b + k, c, d, e⟩ [fm]⊢* ⟨a, b, c + k, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing a b c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1) (d := d + 1))
    ring_nf; finish

theorem r2_chain : ∀ k, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl,
        show e + (k + 1) = e + k + 1 from by ring]
    show ⟨a, 0, k + 1, d, (e + k) + 1⟩ [fm]⊢* _
    step fm
    apply stepStar_trans (ih (a := a + 3))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 2))
    ring_nf; finish

theorem r2_r3_drain : ∀ C, ⟨A, 0, C, D, E + C⟩ [fm]⊢* ⟨0, 0, 0, D, E + 2 * A + 6 * C⟩ := by
  intro C
  rw [show (A : ℕ) = 0 + A from by ring]
  apply stepStar_trans (r2_chain C (a := 0 + A) (d := D) (e := E))
  rw [show 0 + A + 3 * C = 0 + (A + 3 * C) from by ring]
  apply stepStar_trans (r3_chain (A + 3 * C) (a := 0) (d := D) (e := E))
  ring_nf; finish

theorem core : ∀ B, ∀ C D E,
    ⟨0, B, C + 1, D, E + B + C + 1⟩ [fm]⊢* ⟨0, 0, 0, D + B, E + 6 * C + 4 * B + 6⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih
  rcases B with _ | _ | _ | B
  · -- B = 0
    intro C D E
    rw [show E + 0 + C + 1 = E + (C + 1) from by ring]
    apply stepStar_trans (r2_r3_drain (C + 1) (A := 0) (D := D) (E := E))
    ring_nf; finish
  · -- B = 1
    intro C D E
    rw [show E + 1 + C + 1 = (E + C + 1) + 1 from by ring]
    show ⟨0, 1, C + 1, D, (E + C + 1) + 1⟩ [fm]⊢* _
    step fm  -- R2: (3, 1, C, D, E+C+1)
    step fm  -- R1: (2, 0, C+1, D+1, E+C+1)
    rw [show E + C + 1 = E + (C + 1) from by ring]
    apply stepStar_trans (r2_r3_drain (C + 1) (A := 2) (D := D + 1) (E := E))
    ring_nf; finish
  · -- B = 2
    intro C D E
    rw [show E + 2 + C + 1 = (E + C + 2) + 1 from by ring]
    show ⟨0, 2, C + 1, D, (E + C + 2) + 1⟩ [fm]⊢* _
    step fm  -- R2: (3, 2, C, D, E+C+2)
    step fm  -- R1: (2, 1, C+1, D+1, E+C+2)
    step fm  -- R1: (1, 0, C+2, D+2, E+C+2)
    rw [show E + C + 2 = E + (C + 1 + 1) from by ring]
    apply stepStar_trans (r2_r3_drain (C + 1 + 1) (A := 1) (D := D + 1 + 1) (E := E))
    ring_nf; finish
  · -- B = B + 3
    intro C D E
    have hB : B < B + 3 := by omega
    rw [show E + (B + 3) + C + 1 = (E + B + C + 3) + 1 from by ring]
    show ⟨0, B + 3, C + 1, D, (E + B + C + 3) + 1⟩ [fm]⊢* _
    step fm  -- R2: (3, B+3, C, D, E+B+C+3)
    rw [show (3 : ℕ) = 0 + 3 from by ring,
        show B + 1 + 1 + 1 = 0 + (B + 3) from by ring]
    apply stepStar_trans (r1_chain 3 (a := 0) (b := 0 + B) (c := C) (d := D)
      (e := E + B + C + 3))
    rw [show C + 3 = (C + 2) + 1 from by ring,
        show 0 + B = B from by ring,
        show E + B + C + 3 = E + B + (C + 2) + 1 from by ring]
    apply stepStar_trans (ih B hB (C + 2) (D + 3) E)
    ring_nf; finish

theorem trans_d0 : ⟨0, 0, 0, 1, e + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2, e + 10⟩ := by
  show ⟨0, 0, 0, 0 + 1, e + 3⟩ [fm]⊢⁺ _
  step fm  -- R4: (0, 1, 0, 0, e+3)
  rw [show e + 3 = (e + 2) + 1 from by ring]
  step fm  -- R5: (0, 1, 1, 1, e+2)
  rw [show e + 2 = (e + 1) + 1 from by ring]
  show ⟨0, 1, 1, 1, (e + 1) + 1⟩ [fm]⊢* _
  step fm  -- R2: (3, 1, 0, 1, e+1)
  step fm  -- R1: (2, 0, 1, 2, e+1)
  apply stepStar_trans (r2_r3_drain 1 (A := 2) (D := 2) (E := e))
  ring_nf; finish

theorem trans_d1 : ⟨0, 0, 0, 2, e + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, 3, e + 14⟩ := by
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain 2 (b := 0) (d := 0) (e := e + 4))
  rw [show (0 : ℕ) + 2 = 2 from by ring,
      show e + 4 = (e + 3) + 1 from by ring]
  step fm  -- R5: (0, 2, 1, 1, e+3)
  rw [show e + 3 = (e + 2) + 1 from by ring]
  show ⟨0, 2, 1, 1, (e + 2) + 1⟩ [fm]⊢* _
  step fm  -- R2: (3, 2, 0, 1, e+2)
  step fm  -- R1: (2, 1, 1, 2, e+2)
  step fm  -- R1: (1, 0, 2, 3, e+2)
  apply stepStar_trans (r2_r3_drain 2 (A := 1) (D := 3) (E := e))
  ring_nf; finish

theorem trans_ge2 : ⟨0, 0, 0, d + 3, e + d + 5⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 4, e + 4 * d + 18⟩ := by
  rw [show d + 3 = 0 + (d + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (d + 3) (b := 0) (d := 0) (e := e + d + 5))
  rw [show (0 : ℕ) + (d + 3) = d + 3 from by ring,
      show e + d + 5 = (e + d + 4) + 1 from by ring]
  step fm  -- R5: (0, d+3, 1, 1, e+d+4)
  rw [show e + d + 4 = (e + d + 3) + 1 from by ring]
  show ⟨0, d + 3, 1, 1, (e + d + 3) + 1⟩ [fm]⊢* _
  step fm  -- R2: (3, d+3, 0, 1, e+d+3)
  rw [show (3 : ℕ) = 0 + 3 from by ring,
      show d + 3 = 0 + (d + 3) from by ring]
  apply stepStar_trans (r1_chain 3 (a := 0) (b := 0 + d) (c := 0) (d := 1)
    (e := e + d + 3))
  rw [show (0 : ℕ) + d = d from by ring,
      show (0 : ℕ) + 3 = 3 from by ring,
      show (1 : ℕ) + 3 = 4 from by ring,
      show (3 : ℕ) = 2 + 1 from by ring,
      show e + d + 3 = e + d + 2 + 1 from by ring]
  apply stepStar_trans (core d 2 4 e)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 6⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e⟩ ∧ e ≥ d + 3)
  · intro c ⟨d, e, hq, he⟩; subst hq
    rcases d with _ | _ | d
    · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 3 := ⟨e - 3, by omega⟩
      exact ⟨⟨0, 0, 0, 2, e' + 10⟩, ⟨1, e' + 10, rfl, by omega⟩, trans_d0⟩
    · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 4 := ⟨e - 4, by omega⟩
      exact ⟨⟨0, 0, 0, 3, e' + 14⟩, ⟨2, e' + 14, rfl, by omega⟩, trans_d1⟩
    · obtain ⟨e', rfl⟩ : ∃ e', e = e' + d + 5 := ⟨e - d - 5, by omega⟩
      exact ⟨⟨0, 0, 0, d + 4, e' + 4 * d + 18⟩,
        ⟨d + 3, e' + 4 * d + 18, rfl, by omega⟩, trans_ge2⟩
  · exact ⟨0, 6, rfl, by omega⟩
