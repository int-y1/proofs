import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #652: [35/6, 143/2, 8/55, 3/7, 35/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 3  0 -1  0 -1  0
 0  1  0 -1  0  0
 0  0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_652

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | _ => none

-- R4 repeated: move d to b.
theorem r4_loop : ∀ k b d, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (b + 1) d); ring_nf; finish

-- R2 repeated: drain a, incrementing e and f. b must be 0.
theorem r2_drain : ∀ k a e f, ⟨a + k, 0, c, d, e, f⟩ [fm]⊢* ⟨a, 0, c, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih a (e + 1) (f + 1)); ring_nf; finish

-- R1/R3 core loop: each round is R1,R1,R1,R3.
theorem r1r3_core : ∀ m b c d e f,
    ⟨3, 3 * m + b, c, d, e + m, f⟩ [fm]⊢* ⟨3, b, c + 2 * m, d + 3 * m, e, f⟩ := by
  intro m; induction' m with m ih <;> intro b c d e f
  · simp; exists 0
  · rw [show 3 * (m + 1) + b = (3 * m + b) + 1 + 1 + 1 from by ring,
        show e + (m + 1) = (e + m) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 2) (d + 3) e f); ring_nf; finish

-- R3/R2x3 loop: each round is R3,R2,R2,R2.
theorem r3r2x3 : ∀ k c e f,
    ⟨0, 0, k + c, d, e + 1, f⟩ [fm]⊢* ⟨0, 0, c, d, e + 2 * k + 1, f + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · ring_nf; finish
  · rw [show k + 1 + c = (k + c) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show e + 1 + 1 + 1 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih c (e + 2) (f + 3)); ring_nf; finish

-- Phase for D%3 = 0.
theorem phase_r0 (q E F : ℕ) :
    ⟨3, 3 * q, 0, 1, E + q, F⟩ [fm]⊢* ⟨0, 0, 0, 3 * q + 1, E + 4 * q + 3, F + 6 * q + 3⟩ := by
  apply stepStar_trans (r1r3_core q 0 0 1 E F)
  show ⟨3, 0, 0 + 2 * q, 1 + 3 * q, E, F⟩ [fm]⊢* _
  rw [show (0 : ℕ) + 2 * q = 2 * q from by ring, show 1 + 3 * q = 3 * q + 1 from by ring]
  apply stepStar_trans (r2_drain 3 0 E F (c := 2 * q) (d := 3 * q + 1))
  rw [show E + 3 = (E + 2) + 1 from by ring, show (2 * q : ℕ) = 2 * q + 0 from by ring]
  apply stepStar_trans (r3r2x3 (2 * q) 0 (E + 2) (F + 3) (d := 3 * q + 1))
  ring_nf; finish

-- Phase for D%3 = 1.
theorem phase_r1 (q E F : ℕ) :
    ⟨3, 3 * q + 1, 0, 1, E + q, F⟩ [fm]⊢*
    ⟨0, 0, 0, 3 * q + 2, E + 4 * q + 4, F + 6 * q + 5⟩ := by
  apply stepStar_trans (r1r3_core q 1 0 1 E F)
  show ⟨3, 1, 0 + 2 * q, 1 + 3 * q, E, F⟩ [fm]⊢* _
  rw [show (0 : ℕ) + 2 * q = 2 * q from by ring, show 1 + 3 * q = 3 * q + 1 from by ring]
  step fm
  apply stepStar_trans (r2_drain 2 0 E F (c := 2 * q + 1) (d := 3 * q + 2))
  rw [show E + 2 = (E + 1) + 1 from by ring, show (2 * q + 1 : ℕ) = (2 * q + 1) + 0 from by ring]
  apply stepStar_trans (r3r2x3 (2 * q + 1) 0 (E + 1) (F + 2) (d := 3 * q + 2))
  ring_nf; finish

-- Phase for D%3 = 2.
theorem phase_r2 (q E F : ℕ) :
    ⟨3, 3 * q + 2, 0, 1, E + q, F⟩ [fm]⊢*
    ⟨0, 0, 0, 3 * q + 3, E + 4 * q + 5, F + 6 * q + 7⟩ := by
  apply stepStar_trans (r1r3_core q 2 0 1 E F)
  show ⟨3, 2, 0 + 2 * q, 1 + 3 * q, E, F⟩ [fm]⊢* _
  rw [show (0 : ℕ) + 2 * q = 2 * q from by ring, show 1 + 3 * q = 3 * q + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (r2_drain 1 0 E F (c := 2 * q + 2) (d := 3 * q + 3))
  rw [show E + 1 = (E + 0) + 1 from by ring, show (2 * q + 2 : ℕ) = (2 * q + 2) + 0 from by ring]
  apply stepStar_trans (r3r2x3 (2 * q + 2) 0 (E + 0) (F + 1) (d := 3 * q + 3))
  ring_nf; finish

-- Opening: R4 loop + R5 + R3.
theorem opening (D E F : ℕ) :
    ⟨0, 0, 0, D + 1, E + 1, F + 1⟩ [fm]⊢⁺ ⟨3, D + 1, 0, 1, E, F⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show D + 1 = 0 + (D + 1) from by ring]
    exact r4_loop (D + 1) 0 0 (e := E + 1) (f := F + 1)
  simp only [Nat.zero_add]
  step fm; step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3, 3⟩)
  · execute fm 6
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e f, q = ⟨0, 0, 0, d, e, f⟩ ∧ d ≥ 1 ∧ f ≥ 1 ∧ e ≥ d + 1)
  · intro c ⟨d, e, f, hq, hd, hf, he⟩; subst hq
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    obtain ⟨E, rfl⟩ : ∃ E, e = E + 1 := ⟨e - 1, by omega⟩
    obtain ⟨q, hq⟩ : ∃ q, d' + 1 = 3 * q ∨ d' + 1 = 3 * q + 1 ∨ d' + 1 = 3 * q + 2 :=
      ⟨(d' + 1) / 3, by omega⟩
    obtain ⟨E', rfl⟩ : ∃ E', E = E' + q := ⟨E - q, by omega⟩
    rcases hq with hd1 | hd1 | hd1
    · -- d'+1 = 3*q, so q >= 1
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      refine ⟨⟨0, 0, 0, 3 * (q' + 1) + 1, E' + 4 * (q' + 1) + 3, f' + 6 * (q' + 1) + 3⟩,
        ⟨3 * (q' + 1) + 1, E' + 4 * (q' + 1) + 3, f' + 6 * (q' + 1) + 3, rfl,
         by omega, by omega, by omega⟩, ?_⟩
      rw [show d' + 1 = 3 * (q' + 1) from hd1]
      rw [show (3 * (q' + 1) : ℕ) = 3 * q' + 2 + 1 from by ring]
      apply stepPlus_stepStar_stepPlus (opening (3 * q' + 2) (E' + (q' + 1)) f')
      · rw [show 3 * q' + 2 + 1 = 3 * (q' + 1) from by ring]
        exact phase_r0 (q' + 1) E' f'
    · -- d'+1 = 3*q+1
      refine ⟨⟨0, 0, 0, 3 * q + 2, E' + 4 * q + 4, f' + 6 * q + 5⟩,
        ⟨3 * q + 2, E' + 4 * q + 4, f' + 6 * q + 5, rfl, by omega, by omega, by omega⟩, ?_⟩
      rw [show d' + 1 = 3 * q + 1 from hd1]
      apply stepPlus_stepStar_stepPlus (opening (3 * q) (E' + q) f')
      · exact phase_r1 q E' f'
    · -- d'+1 = 3*q+2
      refine ⟨⟨0, 0, 0, 3 * q + 3, E' + 4 * q + 5, f' + 6 * q + 7⟩,
        ⟨3 * q + 3, E' + 4 * q + 5, f' + 6 * q + 7, rfl, by omega, by omega, by omega⟩, ?_⟩
      rw [show d' + 1 = 3 * q + 2 from hd1]
      rw [show (3 * q + 2 : ℕ) = 3 * q + 1 + 1 from by ring]
      apply stepPlus_stepStar_stepPlus (opening (3 * q + 1) (E' + q) f')
      · rw [show 3 * q + 1 + 1 = 3 * q + 2 from by ring]
        exact phase_r2 q E' f'
  · exact ⟨1, 3, 3, rfl, by omega, by omega, by omega⟩
