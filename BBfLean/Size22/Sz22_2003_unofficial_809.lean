import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #809: [35/6, 6655/2, 4/77, 3/5, 7/3]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  3
 2  0  0 -1 -1
 0  1 -1  0  0
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_809

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+3⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: (0, b, c+k, 0, e) →* (0, b+k, c, 0, e)
theorem c_to_b : ∀ k b, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

-- R5 + R3 opening: (0, c+1, 0, 0, e+1) →⁺ (2, c, 0, 0, e)
theorem opening : ⟨0, c + 1, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨2, c, 0, 0, e⟩ := by
  step fm; step fm; finish

-- R1/R1/R3 chain: (2, b+2k, C, D, E+k) →* (2, b, C+2k, D+k, E)
theorem r1r1r3_chain : ∀ k b C D E, ⟨2, b + 2 * k, C, D, E + k⟩ [fm]⊢* ⟨2, b, C + 2 * k, D + k, E⟩ := by
  intro k; induction' k with k ih <;> intro b C D E
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (C + 2) (D + 1) E)
    ring_nf; finish

-- R2/R2 base (b=0): (2, 0, C, D, E) →* (0, 0, C+2, D, E+6)
theorem base_b0 : ⟨2, 0, C, D, E⟩ [fm]⊢* ⟨0, 0, C + 2, D, E + 6⟩ := by
  step fm; step fm; finish

-- R1/R2 base (b=1): (2, 1, C, D, E) →* (0, 0, C+2, D+1, E+3)
theorem base_b1 : ⟨2, 1, C, D, E⟩ [fm]⊢* ⟨0, 0, C + 2, D + 1, E + 3⟩ := by
  step fm; step fm; finish

-- R3/R2/R2 drain: (0, 0, C, k, E+1) →* (0, 0, C+2k, 0, E+5k+1)
theorem drain : ∀ k C E, ⟨0, 0, C, k, E + 1⟩ [fm]⊢* ⟨0, 0, C + 2 * k, 0, E + 5 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro C E
  · exists 0
  · step fm; step fm; step fm
    rw [show E + 3 + 3 = (E + 5) + 1 from by ring]
    apply stepStar_trans (ih (C + 2) (E + 5))
    ring_nf; finish

-- Odd c transition: (0, 0, 2k+1, 0, k+1+E) ⊢⁺ (0, 0, 4k+2, 0, 5k+6+E)
theorem main_odd_c (k E : ℕ) :
    ⟨0, 0, 2 * k + 1, 0, k + 1 + E⟩ [fm]⊢⁺ ⟨0, 0, 4 * k + 2, 0, 5 * k + 6 + E⟩ := by
  -- Phase 1: c_to_b. Rewrite 2*k+1 = 0 + (2*k+1)
  rw [show (2 * k + 1 : ℕ) = 0 + (2 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (c_to_b (2 * k + 1) 0)
  -- Now at (0, 2*k+1, 0, 0, k+1+E)
  -- Phase 2: opening. Rewrite for pattern.
  rw [show (0 : ℕ) + (2 * k + 1) = 2 * k + 1 from by ring,
      show k + 1 + E = (k + E) + 1 from by ring,
      show 2 * k + 1 = (2 * k) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening)
  -- Now at (2, 2*k, 0, 0, k+E)
  -- Phase 3: r1r1r3_chain b=0
  rw [show k + E = E + k from by ring,
      show (2 * k : ℕ) = 0 + 2 * k from by ring]
  apply stepStar_trans (r1r1r3_chain k 0 0 0 E)
  -- Now at (2, 0, 2*k, k, E)
  -- Phase 4: base_b0
  apply stepStar_trans (base_b0)
  -- Now at (0, 0, 2*k+2, k, E+6)
  -- Phase 5: drain k rounds
  rw [show E + 6 = (E + 5) + 1 from by ring,
      show (0 : ℕ) + 2 * k + 2 = 2 * k + 2 from by ring,
      show (0 : ℕ) + k = k from by ring]
  apply stepStar_trans (drain k (2 * k + 2) (E + 5))
  ring_nf; finish

-- Even c transition: (0, 0, 2k+2, 0, k+2+E) ⊢⁺ (0, 0, 4k+4, 0, 5k+9+E)
theorem main_even_c (k E : ℕ) :
    ⟨0, 0, 2 * k + 2, 0, k + 2 + E⟩ [fm]⊢⁺ ⟨0, 0, 4 * k + 4, 0, 5 * k + 9 + E⟩ := by
  -- Phase 1: c_to_b
  rw [show (2 * k + 2 : ℕ) = 0 + (2 * k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (c_to_b (2 * k + 2) 0)
  -- Now at (0, 2*k+2, 0, 0, k+2+E)
  -- Phase 2: opening
  rw [show (0 : ℕ) + (2 * k + 2) = (2 * k + 1) + 1 from by ring,
      show k + 2 + E = (k + 1 + E) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening)
  -- Now at (2, 2*k+1, 0, 0, k+1+E)
  -- Phase 3: r1r1r3_chain b=1
  rw [show k + 1 + E = (E + 1) + k from by ring,
      show 2 * k + 1 = 1 + 2 * k from by ring]
  apply stepStar_trans (r1r1r3_chain k 1 0 0 (E + 1))
  -- Now at (2, 1, 2*k, k, E+1)
  -- Phase 4: base_b1
  apply stepStar_trans (base_b1)
  -- Now at (0, 0, 2*k+2, k+1, E+1+3) = (0, 0, 2*k+2, k+1, E+4)
  -- Phase 5: drain k+1 rounds
  rw [show E + 1 + 3 = (E + 3) + 1 from by ring,
      show (0 : ℕ) + 2 * k + 2 = 2 * k + 2 from by ring,
      show (0 : ℕ) + k + 1 = k + 1 from by ring]
  apply stepStar_trans (drain (k + 1) (2 * k + 2) (E + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 3⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c, 0, e⟩ ∧ c ≥ 1 ∧ e ≥ c)
  · intro q ⟨c, e, hq, hc, he⟩; subst hq
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rcases Nat.even_or_odd c' with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- c' = 2k, c = 2k+1 (odd)
      subst hk; rw [show k + k + 1 = 2 * k + 1 from by ring] at *
      obtain ⟨E, rfl⟩ : ∃ E, e = k + 1 + E := ⟨e - (k + 1), by omega⟩
      exact ⟨⟨0, 0, 4 * k + 2, 0, 5 * k + 6 + E⟩,
        ⟨4 * k + 2, 5 * k + 6 + E, rfl, by omega, by omega⟩, main_odd_c k E⟩
    · -- c' = 2k+1, c = 2k+2 (even)
      subst hk; rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring] at *
      obtain ⟨E, rfl⟩ : ∃ E, e = k + 2 + E := ⟨e - (k + 2), by omega⟩
      exact ⟨⟨0, 0, 4 * k + 4, 0, 5 * k + 9 + E⟩,
        ⟨4 * k + 4, 5 * k + 9 + E, rfl, by omega, by omega⟩, main_even_c k E⟩
  · exact ⟨1, 3, rfl, by omega, by omega⟩
