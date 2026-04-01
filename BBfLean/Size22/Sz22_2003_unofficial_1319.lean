import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1319: [63/10, 143/2, 4/33, 5/7, 21/13]

Vector representation:
```
-1  2 -1  1  0  0
-1  0  0  0  1  1
 2 -1  0  0 -1  0
 0  0  1 -1  0  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1319

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- R4 chain: move d to c
theorem d_to_c : ∀ k, ∀ C d, ⟨0, 0, C, d + k, e, f⟩ [fm]⊢* ⟨0, 0, C + k, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro C d
  · exists 0
  · rw [show d + (k + 1) = d + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (C + 1) d)
    ring_nf; finish

-- R3R2R2 chain: drain b
theorem r3r2r2 : ∀ b, ∀ E F, ⟨0, b, 0, D, E + 1, F⟩ [fm]⊢* ⟨0, 0, 0, D, E + 1 + b, F + 2 * b⟩ := by
  intro b; induction' b with b ih <;> intro E F
  · exists 0
  · step fm; step fm; step fm
    apply stepStar_trans (ih (E + 1) (F + 2))
    ring_nf; finish

-- R1R1R3 chain (even c = 2*k)
theorem r1_even : ∀ k, ∀ b D, ⟨2, b, 2 * k, D, E + k + 1, F⟩ [fm]⊢*
    ⟨0, b + 3 * k, 0, D + 2 * k, E + 3, F + 2⟩ := by
  intro k; induction' k with k ih <;> intro b D
  · step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show E + (k + 1) + 1 = (E + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) (D + 2))
    ring_nf; finish

-- R1R1R3 chain (odd c = 2*k+1)
theorem r1_odd : ∀ k, ∀ b D, ⟨2, b, 2 * k + 1, D, E + k + 1, F⟩ [fm]⊢*
    ⟨0, b + 3 * k + 2, 0, D + 2 * k + 1, E + 2, F + 1⟩ := by
  intro k; induction' k with k ih <;> intro b D
  · step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 from by ring,
        show E + (k + 1) + 1 = (E + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) (D + 2))
    ring_nf; finish

-- Transition for d = 0
theorem trans_d0 : ⟨0, 0, 0, 0, E + 1, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, E + 2, f + 2⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Full transition for even d = 2*(k+1):
theorem trans_even (k : ℕ) :
    ⟨0, 0, 0, 2 * (k + 1), E + k + 3, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * k + 3, E + 3 * k + 6, f + 6 * k + 8⟩ := by
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
  step fm
  rw [show (2 * k + 1 : ℕ) = 0 + (2 * k + 1) from by ring]
  apply stepStar_trans (d_to_c (e := E + k + 3) (f := f + 1) (2 * k + 1) 1 0)
  rw [show 1 + (2 * k + 1) = 2 * k + 2 from by ring]
  step fm; step fm
  rw [show E + k + 2 = E + (k + 1) + 1 from by ring,
      show 2 * k + 2 = 2 * (k + 1) from by ring]
  apply stepStar_trans (r1_even (E := E) (F := f) (k + 1) 0 1)
  rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring,
      show 1 + 2 * (k + 1) = 2 * k + 3 from by ring,
      show E + 3 = (E + 2) + 1 from by ring]
  apply stepStar_trans (r3r2r2 (D := 2 * k + 3) (3 * k + 3) (E + 2) (f + 2))
  ring_nf; finish

-- Full transition for odd d = 2*k+1:
theorem trans_odd (k : ℕ) :
    ⟨0, 0, 0, 2 * k + 1, E + k + 2, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * k + 2, E + 3 * k + 4, f + 6 * k + 5⟩ := by
  rw [show 2 * k + 1 = 2 * k + 0 + 1 from by ring]
  step fm
  rw [show (2 * k : ℕ) = 0 + 2 * k from by ring]
  apply stepStar_trans (d_to_c (e := E + k + 2) (f := f + 1) (2 * k) 1 0)
  rw [show 1 + 2 * k = 2 * k + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (r1_odd (E := E) (F := f) k 0 1)
  rw [show 0 + 3 * k + 2 = 3 * k + 2 from by ring,
      show 1 + 2 * k + 1 = 2 * k + 2 from by ring,
      show E + 2 = (E + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2 (D := 2 * k + 2) (3 * k + 2) (E + 1) (f + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 4, 6⟩) (by execute fm 16)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d E f, q = ⟨0, 0, 0, d, E + 1, f + 1⟩ ∧ 2 * E ≥ d + 4)
  · intro c ⟨d, E, f, hq, hinv⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      rcases K with _ | k
      · exact ⟨⟨0, 0, 0, 1, E + 2, f + 2⟩,
          ⟨1, E + 1, f + 1, rfl, by omega⟩,
          trans_d0⟩
      · obtain ⟨E', rfl⟩ : ∃ E', E = E' + k + 2 := ⟨E - k - 2, by omega⟩
        rw [show E' + k + 2 + 1 = E' + k + 3 from by ring]
        refine ⟨⟨0, 0, 0, 2 * k + 3, E' + 3 * k + 6, f + 6 * k + 8⟩,
          ⟨2 * k + 3, E' + 3 * k + 5, f + 6 * k + 7, ?_, by omega⟩,
          trans_even k⟩
        ring_nf
    · subst hK
      obtain ⟨E', rfl⟩ : ∃ E', E = E' + K + 1 := ⟨E - K - 1, by omega⟩
      rw [show E' + K + 1 + 1 = E' + K + 2 from by ring]
      refine ⟨⟨0, 0, 0, 2 * K + 2, E' + 3 * K + 4, f + 6 * K + 5⟩,
        ⟨2 * K + 2, E' + 3 * K + 3, f + 6 * K + 4, ?_, by omega⟩,
        trans_odd K⟩
      ring_nf
  · exact ⟨2, 3, 5, by ring_nf, by omega⟩

end Sz22_2003_unofficial_1319
