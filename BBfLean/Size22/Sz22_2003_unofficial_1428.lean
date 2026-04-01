import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1428: [7/15, 22/3, 27/77, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  1
 0  3  0 -1 -1
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1428

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- Drain c by 4 per round: (a+k, 0, c+4k, d, 0) ⊢* (a, 0, c, d+3k, 0)
theorem drain_chain : ∀ k c d, ⟨a + k, 0, c + 4 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 4 * (k + 1) = (c + 4 * k) + 4 from by ring]
    step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih c (d + 3)); ring_nf; finish

-- Handle c=2: (a+1, 0, 2, d, 0) ⊢* (a+2, 0, 0, d+1, 2)
theorem c2_step : ⟨a + 1, 0, 2, d, 0⟩ [fm]⊢* ⟨a + 2, 0, 0, d + 1, 2⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

-- R5+R2: (a+1, 0, 0, d, 0) ⊢* (a+1, 0, 0, d, 2)
theorem r5r2 : ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢* ⟨a + 1, 0, 0, d, 2⟩ := by
  step fm; step fm; ring_nf; finish

-- R3+R2*3 chain, universally quantifying all variables for the induction.
theorem r3r2_chain : ∀ k A D E, ⟨A, 0, 0, D + k, E + 1⟩ [fm]⊢* ⟨A + 3 * k, 0, 0, D, E + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · exists 0
  · rw [show D + (k + 1) = (D + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show E + 1 + 1 + 1 = (E + 2) + 1 from by ring]
    apply stepStar_trans (ih (A + 3) D (E + 2))
    ring_nf; finish

-- Convert e to c: (a, 0, c, 0, e+k) ⊢* (a, 0, c+k, 0, e)
theorem e_to_c : ∀ k c, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1)); ring_nf; finish

-- Case c ≡ 0 mod 4: (a, 0, 4k, 0, 0) ⊢⁺ (a+8k, 0, 6k+2, 0, 0) when a ≥ k+1
theorem main_c0mod4 (k : ℕ) (ha : a ≥ k + 1) :
    ⟨a, 0, 4 * k, 0, 0⟩ [fm]⊢⁺ ⟨a + 8 * k, 0, 6 * k + 2, 0, 0⟩ := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + (k + 1) := ⟨a - (k + 1), by omega⟩
  rw [show a' + (k + 1) = (a' + 1) + k from by ring,
      show (4 * k : ℕ) = 0 + 4 * k from by ring]
  apply stepStar_stepPlus_stepPlus (drain_chain k 0 0 (a := a' + 1))
  rw [show (0 + 3 * k : ℕ) = 3 * k from by ring]
  -- R5+R2
  apply stepStar_stepPlus_stepPlus (r5r2 (a := a') (d := 3 * k))
  -- R3+R2 chain: 3k rounds
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show (3 * k : ℕ) = 0 + 3 * k from by ring]
  apply stepStar_stepPlus_stepPlus (r3r2_chain (3 * k) (a' + 1) 0 1)
  -- Now at (a'+1+9k, 0, 0, 0, 1+6k+1) = (a'+9k+1, 0, 0, 0, 6k+2)
  rw [show 1 + 2 * (3 * k) + 1 = 0 + (6 * k + 2) from by ring,
      show a' + 1 + 3 * (3 * k) = a' + 9 * k + 1 from by ring]
  -- e_to_c
  apply stepPlus_stepStar_stepPlus
  · step fm
    apply stepStar_trans (e_to_c (6 * k + 1) 1 (a := a' + 9 * k + 1) (e := 0))
    ring_nf; finish
  · ring_nf; finish

-- Case c ≡ 2 mod 4: (a, 0, 4k+2, 0, 0) ⊢⁺ (a+8k+4, 0, 6k+4, 0, 0) when a ≥ k+1
theorem main_c2mod4 (k : ℕ) (ha : a ≥ k + 1) :
    ⟨a, 0, 4 * k + 2, 0, 0⟩ [fm]⊢⁺ ⟨a + 8 * k + 4, 0, 6 * k + 4, 0, 0⟩ := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + (k + 1) := ⟨a - (k + 1), by omega⟩
  rw [show a' + (k + 1) = (a' + 1) + k from by ring,
      show (4 * k + 2 : ℕ) = 2 + 4 * k from by ring]
  apply stepStar_stepPlus_stepPlus (drain_chain k 2 0 (a := a' + 1))
  rw [show (0 + 3 * k : ℕ) = 3 * k from by ring]
  -- c2_step
  apply stepStar_stepPlus_stepPlus (c2_step (a := a') (d := 3 * k))
  -- R3+R2 chain: 3k+1 rounds
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show 3 * k + 1 = 0 + (3 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r3r2_chain (3 * k + 1) (a' + 2) 0 1)
  -- Now at (a'+2+9k+3, 0, 0, 0, 1+6k+2+1) = (a'+9k+5, 0, 0, 0, 6k+4)
  rw [show 1 + 2 * (3 * k + 1) + 1 = 0 + (6 * k + 4) from by ring,
      show a' + 2 + 3 * (3 * k + 1) = a' + 9 * k + 5 from by ring]
  -- e_to_c
  apply stepPlus_stepStar_stepPlus
  · step fm
    apply stepStar_trans (e_to_c (6 * k + 3) 1 (a := a' + 9 * k + 5) (e := 0))
    ring_nf; finish
  · ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 2, 0, 0⟩)
  · execute fm 4
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a m, q = ⟨a, 0, 2 * m + 2, 0, 0⟩ ∧ a ≥ m + 1)
  · intro q ⟨a, m, hq, ha⟩; subst hq
    rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- m = 2j (even), so 2m+2 = 4j+2
      subst hj
      exact ⟨⟨a + 8 * j + 4, 0, 2 * (3 * j + 1) + 2, 0, 0⟩,
        ⟨a + 8 * j + 4, 3 * j + 1, rfl, by omega⟩,
        by rw [show 2 * (j + j) + 2 = 4 * j + 2 from by ring,
               show 2 * (3 * j + 1) + 2 = 6 * j + 4 from by ring]
           exact main_c2mod4 j (by omega)⟩
    · -- m = 2j+1 (odd), so 2m+2 = 4j+4 = 4*(j+1)
      subst hj
      exact ⟨⟨a + 8 * (j + 1), 0, 2 * (3 * j + 3) + 2, 0, 0⟩,
        ⟨a + 8 * (j + 1), 3 * j + 3, rfl, by omega⟩,
        by rw [show 2 * (2 * j + 1) + 2 = 4 * (j + 1) from by ring,
               show 2 * (3 * j + 3) + 2 = 6 * (j + 1) + 2 from by ring]
           exact main_c0mod4 (j + 1) (by omega)⟩
  · exact ⟨1, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1428
