import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1509: [7/15, 9/77, 50/7, 11/5, 245/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 1  0  2 -1  0
 0  0 -1  0  1
-1  0  1  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1509

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+2, e⟩
  | _ => none

-- R4 chain: transfer c to e (b=0, d=0, e=0)
theorem c_to_e : ∀ k, ∀ a e, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih a (e + 1)); ring_nf; finish

-- R3 chain: d steps, each adding 1 to a and 2 to c (b=0, e=0)
theorem r3_chain : ∀ k, ∀ A C, ⟨A, 0, C, k, 0⟩ [fm]⊢* ⟨A + k, 0, C + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · step fm
    apply stepStar_trans (ih (A + 1) (C + 2)); ring_nf; finish

-- One 5-step round when B = 0: R5, R2, R1, R2, R2
theorem round_b0 (a e : ℕ) : ⟨a + 1, 0, 0, 0, e + 3⟩ [fm]⊢* ⟨a, 5, 0, 0, e⟩ := by
  rw [show e + 3 = (e + 1) + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; finish

-- One 5-step round when B >= 1: R5, R1, R2, R2, R2
theorem round_bpos (a B e : ℕ) : ⟨a + 1, B + 1, 0, 0, e + 3⟩ [fm]⊢* ⟨a, B + 6, 0, 0, e⟩ := by
  rw [show e + 3 = (e + 1) + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; ring_nf; finish

-- K rounds starting with B >= 1
theorem rounds_bpos : ∀ K, ∀ a B e, ⟨a + K, B + 1, 0, 0, e + 3 * K⟩ [fm]⊢* ⟨a, B + 5 * K + 1, 0, 0, e⟩ := by
  intro K; induction' K with K ih <;> intro a B e
  · exists 0
  · rw [show a + (K + 1) = (a + K) + 1 from by ring,
        show e + 3 * (K + 1) = (e + 3 * K) + 3 from by ring]
    apply stepStar_trans (round_bpos (a + K) B (e + 3 * K))
    apply stepStar_trans (ih a (B + 5) e)
    ring_nf; finish

-- Combined: (a+K+1, 0, 0, 0, e+3K+3) ⊢* (a, 5K+5, 0, 0, e)
theorem rounds (K a e : ℕ) : ⟨a + K + 1, 0, 0, 0, e + 3 * K + 3⟩ [fm]⊢* ⟨a, 5 * K + 5, 0, 0, e⟩ := by
  rw [show a + K + 1 = (a + K) + 1 from by ring,
      show e + 3 * K + 3 = (e + 3 * K) + 3 from by ring]
  apply stepStar_trans (round_b0 (a + K) (e + 3 * K))
  rw [show (5 : ℕ) = 4 + 1 from by ring]
  apply stepStar_trans (rounds_bpos K a 4 e)
  ring_nf; finish

-- Chain lemma: (A, B, 0, D+1, 0) ⊢* (A+B+D+1, 0, 2*D+B+2, 0, 0)
-- B=0: R3 chain
-- B=1: R3, R1, then R3 chain for remaining d+1
-- B>=2: R3, R1, R1, then recurse with B-2
theorem abd_chain : ∀ B, ∀ A D, ⟨A, B, 0, D + 1, 0⟩ [fm]⊢* ⟨A + B + D + 1, 0, 2 * D + B + 2, 0, 0⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro A D
  rcases B with _ | _ | B
  · -- B=0: just R3 chain
    have := r3_chain (D + 1) A 0
    rw [show 0 + 2 * (D + 1) = 2 * D + 2 from by ring,
        show A + (D + 1) = A + 0 + D + 1 from by ring] at this
    exact this
  · -- B=1: R3, R1, then R3 chain
    step fm; step fm
    have := r3_chain (D + 1) (A + 1) 1
    rw [show 1 + 2 * (D + 1) = 2 * D + 1 + 2 from by ring,
        show A + 1 + (D + 1) = A + 1 + D + 1 from by ring] at this
    exact this
  · -- B >= 2: R3, R1, R1, then IH with B (< B+2)
    step fm; step fm; step fm
    rw [show D + 1 + 1 = (D + 1) + 1 from by ring]
    have := ih B (by omega) (A + 1) (D + 1)
    rw [show A + 1 + B + (D + 1) + 1 = A + (B + 2) + D + 1 from by ring,
        show 2 * (D + 1) + B + 2 = 2 * D + (B + 2) + 2 from by ring] at this
    exact this

-- Tail r=0: (F+1, 5K+5, 0, 0, 0) -> R5,R1 -> (F, 5K+4, 0, 3, 0)
-- Then abd_chain(5K+4, F, 2)
theorem tail_r0 (K F : ℕ) :
    ⟨F + 1, 5 * K + 5, 0, 0, 0⟩ [fm]⊢⁺ ⟨F + 5 * K + 7, 0, 5 * K + 10, 0, 0⟩ := by
  rw [show 5 * K + 5 = (5 * K + 4) + 1 from by ring]
  step fm  -- R5: (F, 5K+5, 1, 2, 0)
  step fm  -- R1: (F, 5K+4, 0, 3, 0)
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (abd_chain (5 * K + 4) F 2)
  ring_nf; finish

-- Tail r=1: (F+1, 5K+5, 0, 0, 1) -> R5,R1,R2 -> (F, 5K+6, 0, 2, 0)
-- Then abd_chain(5K+6, F, 1)
theorem tail_r1 (K F : ℕ) :
    ⟨F + 1, 5 * K + 5, 0, 0, 1⟩ [fm]⊢⁺ ⟨F + 5 * K + 8, 0, 5 * K + 10, 0, 0⟩ := by
  rw [show 5 * K + 5 = (5 * K + 4) + 1 from by ring]
  step fm  -- R5: (F, 5K+5, 1, 2, 1)
  step fm  -- R1: (F, 5K+4, 0, 3, 1)
  step fm  -- R2: (F, 5K+6, 0, 2, 0)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (abd_chain (5 * K + 6) F 1)
  ring_nf; finish

-- Tail r=2: (F+1, 5K+5, 0, 0, 2) -> R5,R1,R2,R2 -> (F, 5K+8, 0, 1, 0)
-- Then abd_chain(5K+8, F, 0)
theorem tail_r2 (K F : ℕ) :
    ⟨F + 1, 5 * K + 5, 0, 0, 2⟩ [fm]⊢⁺ ⟨F + 5 * K + 9, 0, 5 * K + 10, 0, 0⟩ := by
  rw [show 5 * K + 5 = (5 * K + 4) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm  -- R5: (F, 5K+5, 1, 2, 2)
  step fm  -- R1: (F, 5K+4, 0, 3, 2)
  step fm  -- R2: (F, 5K+6, 0, 2, 1)
  step fm  -- R2: (F, 5K+8, 0, 1, 0)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (abd_chain (5 * K + 8) F 0)
  ring_nf; finish

-- Main transition r=0: c = 3(K+1), a = K+F+2
theorem main_r0 (K F : ℕ) :
    ⟨K + F + 2, 0, 3 * K + 3, 0, 0⟩ [fm]⊢⁺ ⟨F + 5 * K + 7, 0, 5 * K + 10, 0, 0⟩ := by
  have h1 : ⟨K + F + 2, 0, 3 * K + 3, 0, 0⟩ [fm]⊢* ⟨K + F + 2, 0, 0, 0, 3 * K + 3⟩ := by
    have := c_to_e (3 * K + 3) (K + F + 2) 0
    simpa using this
  have h2 : ⟨K + F + 2, 0, 0, 0, 3 * K + 3⟩ [fm]⊢* ⟨F + 1, 5 * K + 5, 0, 0, 0⟩ := by
    rw [show K + F + 2 = (F + 1) + K + 1 from by ring,
        show 3 * K + 3 = 0 + 3 * K + 3 from by ring]
    exact rounds K (F + 1) 0
  exact stepStar_stepPlus_stepPlus (stepStar_trans h1 h2) (tail_r0 K F)

-- Main transition r=1: c = 3K+4, a = K+F+2
theorem main_r1 (K F : ℕ) :
    ⟨K + F + 2, 0, 3 * K + 4, 0, 0⟩ [fm]⊢⁺ ⟨F + 5 * K + 8, 0, 5 * K + 10, 0, 0⟩ := by
  have h1 : ⟨K + F + 2, 0, 3 * K + 4, 0, 0⟩ [fm]⊢* ⟨K + F + 2, 0, 0, 0, 3 * K + 4⟩ := by
    have := c_to_e (3 * K + 4) (K + F + 2) 0
    simpa using this
  have h2 : ⟨K + F + 2, 0, 0, 0, 3 * K + 4⟩ [fm]⊢* ⟨F + 1, 5 * K + 5, 0, 0, 1⟩ := by
    rw [show K + F + 2 = (F + 1) + K + 1 from by ring,
        show 3 * K + 4 = 1 + 3 * K + 3 from by ring]
    exact rounds K (F + 1) 1
  exact stepStar_stepPlus_stepPlus (stepStar_trans h1 h2) (tail_r1 K F)

-- Main transition r=2: c = 3K+5, a = K+F+2
theorem main_r2 (K F : ℕ) :
    ⟨K + F + 2, 0, 3 * K + 5, 0, 0⟩ [fm]⊢⁺ ⟨F + 5 * K + 9, 0, 5 * K + 10, 0, 0⟩ := by
  have h1 : ⟨K + F + 2, 0, 3 * K + 5, 0, 0⟩ [fm]⊢* ⟨K + F + 2, 0, 0, 0, 3 * K + 5⟩ := by
    have := c_to_e (3 * K + 5) (K + F + 2) 0
    simpa using this
  have h2 : ⟨K + F + 2, 0, 0, 0, 3 * K + 5⟩ [fm]⊢* ⟨F + 1, 5 * K + 5, 0, 0, 2⟩ := by
    rw [show K + F + 2 = (F + 1) + K + 1 from by ring,
        show 3 * K + 5 = 2 + 3 * K + 3 from by ring]
    exact rounds K (F + 1) 2
  exact stepStar_stepPlus_stepPlus (stepStar_trans h1 h2) (tail_r2 K F)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 5, 0, 0⟩)
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a, 0, c, 0, 0⟩ ∧ a ≥ 1 ∧ c ≥ 5 ∧ 3 * a > c)
  · intro q ⟨a, c, hq, ha, hc5, hca⟩; subst hq
    have h3 : c % 3 < 3 := Nat.mod_lt _ (by omega)
    obtain ⟨k, hk⟩ : ∃ k, c = 3 * k + c % 3 := ⟨c / 3, by omega⟩
    interval_cases (c % 3)
    · -- c ≡ 0 (mod 3)
      rw [Nat.add_zero] at hk; subst hk
      obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, a = K + F + 2 := ⟨a - K - 2, by omega⟩
      exact ⟨⟨F + 5 * K + 7, 0, 5 * K + 10, 0, 0⟩,
        ⟨F + 5 * K + 7, 5 * K + 10, rfl, by omega, by omega, by omega⟩,
        main_r0 K F⟩
    · -- c ≡ 1 (mod 3)
      subst hk
      obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, a = K + F + 2 := ⟨a - K - 2, by omega⟩
      rw [show 3 * (K + 1) + 1 = 3 * K + 4 from by ring]
      exact ⟨⟨F + 5 * K + 8, 0, 5 * K + 10, 0, 0⟩,
        ⟨F + 5 * K + 8, 5 * K + 10, rfl, by omega, by omega, by omega⟩,
        main_r1 K F⟩
    · -- c ≡ 2 (mod 3)
      subst hk
      obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, a = K + F + 2 := ⟨a - K - 2, by omega⟩
      rw [show 3 * (K + 1) + 2 = 3 * K + 5 from by ring]
      exact ⟨⟨F + 5 * K + 9, 0, 5 * K + 10, 0, 0⟩,
        ⟨F + 5 * K + 9, 5 * K + 10, rfl, by omega, by omega, by omega⟩,
        main_r2 K F⟩
  · exact ⟨2, 5, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_1509
