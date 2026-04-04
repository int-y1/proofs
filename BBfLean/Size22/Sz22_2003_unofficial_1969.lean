import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1969: [99/35, 2/5, 25/6, 7/11, 175/2]

Vector representation:
```
 0  2 -1 -1  1
 1  0 -1  0  0
-1 -1  2  0  0
 0  0  0  1 -1
-1  0  2  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1969

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | _ => none

-- R4 repeated: (a, 0, 0, d, e+k) →* (a, 0, 0, d+k, e)
theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1)); ring_nf; finish

-- R4 chain + R5: (a+1, 0, 0, 0, n) →⁺ (a, 0, 2, n+1, 0)
theorem e_drain_R5 : ∀ n, ⟨a + 1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨a, 0, 2, n + 1, 0⟩ := by
  intro n
  apply stepStar_step_stepPlus
  · rw [show (0 : ℕ) = 0 + 0 from by ring, show n = 0 + n from by ring]
    apply stepStar_trans (e_to_d n 0 (a := a + 1) (e := 0))
    simp only [Nat.zero_add]; finish
  · simp [fm]

-- Opening round: R1+R1+R3 repeated k times
theorem opening_round : ∀ k, ∀ b d e, ⟨a + k + 1, b, 2, d + 2 * k, e⟩ [fm]⊢*
    ⟨a + 1, b + 3 * k, 2, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 1 + 1 from by ring,
        show a + (k + 1) + 1 = a + k + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) d (e + 2)); ring_nf; finish

-- R3+R2+R2 drain
theorem drain : ∀ k, ∀ a b e, ⟨a + 1, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) b e); ring_nf; finish

-- Opening + base0 + drain for even D=2k:
-- (a+k+1, 0, 2, 2k, 0) →* (a+3k+3, 0, 0, 0, 2k)
theorem phase_even : ⟨a + k + 1, 0, 2, 2 * k, 0⟩ [fm]⊢* ⟨a + 3 * k + 3, 0, 0, 0, 2 * k⟩ := by
  rw [show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_trans (opening_round k 0 0 0)
  step fm; step fm
  rw [show a + 1 + 1 + 1 = (a + 2) + 1 from by ring,
      show 0 + 3 * k = 0 + (3 * k) from by ring,
      show 0 + 2 * k = 2 * k from by ring]
  apply stepStar_trans (drain (3 * k) (a + 2) 0 (2 * k))
  ring_nf; finish

-- Opening + base1 + drain for odd D=2k+1:
-- (a+k+1, 0, 2, 2k+1, 0) →* (a+3k+4, 0, 0, 0, 2k+1)
theorem phase_odd : ⟨a + k + 1, 0, 2, 2 * k + 1, 0⟩ [fm]⊢* ⟨a + 3 * k + 4, 0, 0, 0, 2 * k + 1⟩ := by
  rw [show 2 * k + 1 = 1 + 2 * k from by ring]
  apply stepStar_trans (opening_round k 0 1 0)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm
  rw [show a + 1 + 1 = (a + 1) + 1 from by ring,
      show 0 + 3 * k + 2 = 0 + (3 * k + 2) from by ring,
      show 0 + 2 * k + 1 = 2 * k + 1 from by ring]
  apply stepStar_trans (drain (3 * k + 2) (a + 1) 0 (2 * k + 1))
  ring_nf; finish

-- Main transition for even n=2k:
-- (f+k+1, 0, 0, 0, 2k) →⁺ (f+3k+3, 0, 0, 0, 2k+1)
theorem main_even (hf : f ≥ 1) :
    ⟨f + k + 1, 0, 0, 0, 2 * k⟩ [fm]⊢⁺ ⟨f + 3 * k + 3, 0, 0, 0, 2 * k + 1⟩ := by
  rw [show f + k + 1 = (f + k) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (e_drain_R5 (2 * k) (a := f + k))
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  show ⟨f' + 1 + k, 0, 2, 2 * k + 1, 0⟩ [fm]⊢* _
  rw [show f' + 1 + k = f' + k + 1 from by ring]
  apply stepStar_trans (phase_odd (a := f') (k := k))
  ring_nf; finish

-- Main transition for odd n=2k+1:
-- (f+k+2, 0, 0, 0, 2k+1) →⁺ (f+3k+5, 0, 0, 0, 2k+2)
theorem main_odd (hf : f ≥ 1) :
    ⟨f + k + 2, 0, 0, 0, 2 * k + 1⟩ [fm]⊢⁺ ⟨f + 3 * k + 5, 0, 0, 0, 2 * k + 2⟩ := by
  rw [show f + k + 2 = (f + k + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (e_drain_R5 (2 * k + 1) (a := f + k + 1))
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  show ⟨f' + 1 + k + 1, 0, 2, 2 * k + 1 + 1, 0⟩ [fm]⊢* _
  rw [show f' + 1 + k + 1 = f' + (k + 1) + 1 from by ring,
      show 2 * k + 1 + 1 = 2 * (k + 1) from by ring]
  apply stepStar_trans (phase_even (a := f') (k := k + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a n, q = ⟨a, 0, 0, 0, n⟩ ∧ 2 * a ≥ n + 4)
  · intro c ⟨a, n, hq, ha⟩; subst hq
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- n even: n = k + k = 2k
      rw [show k + k = 2 * k from by ring] at hk; subst hk
      obtain ⟨f, hf⟩ : ∃ f, a = f + k + 1 := ⟨a - k - 1, by omega⟩
      subst hf
      refine ⟨⟨f + 3 * k + 3, 0, 0, 0, 2 * k + 1⟩,
        ⟨f + 3 * k + 3, 2 * k + 1, rfl, by omega⟩, main_even (by omega)⟩
    · -- n odd: n = 2k + 1
      subst hk
      obtain ⟨f, hf⟩ : ∃ f, a = f + k + 2 := ⟨a - k - 2, by omega⟩
      subst hf
      refine ⟨⟨f + 3 * k + 5, 0, 0, 0, 2 * k + 2⟩,
        ⟨f + 3 * k + 5, 2 * k + 2, rfl, by omega⟩, main_odd (by omega)⟩
  · exact ⟨3, 1, rfl, by omega⟩
