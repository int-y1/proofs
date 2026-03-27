import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #622: [35/6, 1331/2, 4/55, 3/7, 15/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  3
 2  0 -1  0 -1
 0  1  0 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_622

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, n + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, n, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, n + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, n, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- Interleaved chain for even B: (2, 2k, c, d, e+k) →* (2, 0, c+k, d+2k, e)
theorem interleaved_even :
    ∀ k, ∀ c d e, ⟨2, 2 * k, c, d, e + k⟩ [fm]⊢* ⟨(2 : ℕ), 0, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
  rw [show e + (k + 1) = e + k + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (c + 1) (d + 2) e)
  ring_nf; finish

-- Interleaved chain for odd B: (2, 2k+1, c, d, e+k) →* (2, 0, c+k, d+2k+1, e+2)
theorem interleaved_odd :
    ∀ k, ∀ c d e, ⟨2, 2 * k + 1, c, d, e + k⟩ [fm]⊢* ⟨(2 : ℕ), 0, c + k, d + 2 * k + 1, e + 2⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · -- B=1: R1, R2, R3
    step fm; step fm; step fm
    ring_nf; finish
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
  rw [show e + (k + 1) = e + k + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (c + 1) (d + 2) e)
  ring_nf; finish

-- R2R2R3 drain: (2, 0, c+k, d, e) →* (2, 0, c, d, e+5k)
theorem r2r2r3_drain : ⟨2, 0, c + k, d, e⟩ [fm]⊢* ⟨(2 : ℕ), 0, c, d, e + 5 * k⟩ := by
  have many_step : ∀ k c e, ⟨2, 0, c + k, d, e⟩ [fm]⊢* ⟨(2 : ℕ), 0, c, d, e + 5 * k⟩ := by
    intro k; induction' k with k h <;> intro c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c e

-- Main transition even n=2k: (0,0,0,2k,4k²+10k+3) →⁺ (0,0,0,2k+1,4k²+14k+9)
theorem main_trans_even (k : ℕ) :
    ⟨0, 0, 0, 2 * k, 4 * k * k + 10 * k + 3⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 2 * k + 1, 4 * k * k + 14 * k + 9⟩ := by
  -- Phase 1: R4 chain
  rw [show (2 * k : ℕ) = 0 + 2 * k from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (n := 0) (k := 2 * k))
  simp only [Nat.zero_add]
  -- Phase 2: R5 + R3
  rw [show 4 * k * k + 10 * k + 3 = (4 * k * k + 10 * k + 1) + 1 + 1 from by ring]
  step fm; step fm
  -- At (2, 2k+1, 0, 0, 4k²+10k+1)
  -- Phase 3: Interleaved odd B=2k+1
  rw [show 4 * k * k + 10 * k + 1 = (4 * k * k + 9 * k + 1) + k from by ring]
  apply stepStar_trans (interleaved_odd k 0 0 (4 * k * k + 9 * k + 1))
  simp only [Nat.zero_add]
  -- At (2, 0, k, 2k+1, 4k²+9k+3)
  -- Phase 4: R2R2R3 drain k times
  rw [show (4 * k * k + 9 * k + 1 + 2 : ℕ) = (4 * k * k + 9 * k + 3) from by ring]
  have hdrain := @r2r2r3_drain 0 k (2 * k + 1) (4 * k * k + 9 * k + 3)
  simp only [Nat.zero_add] at hdrain
  apply stepStar_trans hdrain
  -- At (2, 0, 0, 2k+1, 4k²+14k+3)
  -- Phase 5: R2, R2
  step fm; step fm
  ring_nf; finish

-- Main transition odd n=2k+1: (0,0,0,2k+1,4k²+14k+9) →⁺ (0,0,0,2k+2,4k²+18k+17)
theorem main_trans_odd (k : ℕ) :
    ⟨0, 0, 0, 2 * k + 1, 4 * k * k + 14 * k + 9⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 2 * k + 2, 4 * k * k + 18 * k + 17⟩ := by
  -- Phase 1: R4 chain
  rw [show (2 * k + 1 : ℕ) = 0 + (2 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (n := 0) (k := 2 * k + 1))
  simp only [Nat.zero_add]
  -- Phase 2: R5 + R3
  rw [show 4 * k * k + 14 * k + 9 = (4 * k * k + 14 * k + 7) + 1 + 1 from by ring]
  step fm; step fm
  -- At (2, 2k+2, 0, 0, 4k²+14k+7) = (2, 2(k+1), 0, 0, 4k²+14k+7)
  -- Phase 3: Interleaved even B=2(k+1)
  rw [show 4 * k * k + 14 * k + 7 = (4 * k * k + 13 * k + 6) + (k + 1) from by ring]
  apply stepStar_trans (interleaved_even (k + 1) 0 0 (4 * k * k + 13 * k + 6))
  simp only [Nat.zero_add]
  -- At (2, 0, k+1, 2k+2, 4k²+13k+6)
  -- Phase 4: R2R2R3 drain (k+1) times
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
  have hdrain := @r2r2r3_drain 0 (k + 1) (2 * k + 2) (4 * k * k + 13 * k + 6)
  simp only [Nat.zero_add] at hdrain
  apply stepStar_trans hdrain
  -- At (2, 0, 0, 2k+2, 4k²+18k+11)
  -- Phase 5: R2, R2
  step fm; step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 3⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k, q = ⟨0, 0, 0, 2 * k, 4 * k * k + 10 * k + 3⟩ ∨
                        q = ⟨0, 0, 0, 2 * k + 1, 4 * k * k + 14 * k + 9⟩)
  · intro c ⟨k, hq⟩
    rcases hq with rfl | rfl
    · exact ⟨_, ⟨k, Or.inr rfl⟩, main_trans_even k⟩
    · exact ⟨_, ⟨k + 1, Or.inl (by ring_nf)⟩, main_trans_odd k⟩
  · exact ⟨0, Or.inl (by ring_nf)⟩
