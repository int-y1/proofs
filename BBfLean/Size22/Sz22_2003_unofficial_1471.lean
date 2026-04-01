import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1471: [7/15, 36/77, 11/3, 5/11, 63/2]

Vector representation:
```
 0 -1 -1  1  0
 2  2  0 -1 -1
 0 -1  0  0  1
 0  0  1  0 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1471

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R5/R1/R1 chain: each round drains 1 from a and 2 from c, adds 3 to d.
theorem r5r1r1_chain : ∀ k, ∀ a c d,
    ⟨a + k, (0 : ℕ), c + 2 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; exists 0
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 3))
    ring_nf; finish

-- R3/R2 interleave: drains d while growing a and b.
theorem r3r2_interleave : ∀ k, ∀ a b d,
    ⟨a, b + 1, (0 : ℕ), d + k, 0⟩ [fm]⊢* ⟨a + 2 * k, b + 1 + k, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; simp; exists 0
  | succ k ih =>
    intro a b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 2) (b + 1) d)
    ring_nf; finish

-- R3 chain: drains b to e.
theorem r3_chain : ∀ k, ∀ a b e,
    ⟨a, b + k, (0 : ℕ), 0, e⟩ [fm]⊢* ⟨a, b, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a b e; simp; exists 0
  | succ k ih =>
    intro a b e
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (e + 1))
    ring_nf; finish

-- R4 chain: drains e to c.
theorem r4_chain : ∀ k, ∀ a c e,
    ⟨a, (0 : ℕ), c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c e; simp; exists 0
  | succ k ih =>
    intro a c e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

-- Phase 2+3+4+5: from (a, 2, 0, D, 0) to (a+2D, 0, D+2, 0, 0)
theorem phase2345 : ∀ a D,
    ⟨a, (2 : ℕ), 0, D, 0⟩ [fm]⊢* ⟨a + 2 * D, 0, D + 2, 0, 0⟩ := by
  intro a D
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show D = 0 + D from by ring]
  apply stepStar_trans (r3r2_interleave D a 1 0)
  rw [show 1 + 1 + D = 0 + (D + 2) from by ring,
      show a + 2 * D = a + 2 * D from rfl]
  apply stepStar_trans (r3_chain (D + 2) (a + 2 * D) 0 0)
  rw [show 0 + (D + 2) = D + 2 from by ring,
      show (D + 2 : ℕ) = 0 + (D + 2) from by ring]
  apply stepStar_trans (r4_chain (D + 2) (a + 2 * D) 0 0)
  ring_nf; finish

-- Even transition: (a+k+2, 0, 2k+2, 0, 0) ⊢⁺ (a+6k+8, 0, 3k+6, 0, 0)
theorem main_even (k : ℕ) : ∀ a,
    ⟨a + k + 2, (0 : ℕ), 2 * k + 2, 0, 0⟩ [fm]⊢⁺
    ⟨a + 6 * k + 8, 0, 3 * k + 6, 0, 0⟩ := by
  intro a
  rw [show a + k + 2 = (a + 1) + (k + 1) from by ring,
      show 2 * k + 2 = 0 + 2 * (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1r1_chain (k + 1) (a + 1) 0 0)
  rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring]
  step fm
  apply stepStar_trans (phase2345 a (3 * k + 4))
  ring_nf; finish

-- Odd transition base case k=0: (a+1, 0, 1, 0, 0) ⊢⁺ (a+4, 0, 3, 0, 0)
theorem main_odd_base : ∀ a,
    ⟨a + 1, (0 : ℕ), 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 4, 0, 3, 0, 0⟩ := by
  intro a
  step fm; step fm; step fm; step fm
  -- At (a+2, 2, 0, 1, 0). Apply phase2345.
  apply stepStar_trans (phase2345 (a + 2) 1)
  ring_nf; finish

-- Odd transition k+1: (a+k+2, 0, 2k+3, 0, 0) ⊢⁺ (a+6k+10, 0, 3k+6, 0, 0)
theorem main_odd_succ (k : ℕ) : ∀ a,
    ⟨a + k + 2, (0 : ℕ), 2 * k + 3, 0, 0⟩ [fm]⊢⁺
    ⟨a + 6 * k + 10, 0, 3 * k + 6, 0, 0⟩ := by
  intro a
  rw [show a + k + 2 = (a + 1) + (k + 1) from by ring,
      show 2 * k + 3 = 1 + 2 * (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1r1_chain (k + 1) (a + 1) 1 0)
  rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring]
  -- At (a+1, 0, 1, 3k+3, 0). Now 3k+3 >= 1 so R5,R1,R3,R2.
  step fm; step fm; step fm; step fm
  -- At (a+2, 2, 0, 3k+4, 0). Apply phase2345.
  apply stepStar_trans (phase2345 (a + 2) (3 * k + 4))
  ring_nf; finish

-- Combined odd transition: (a+k+1, 0, 2k+1, 0, 0) ⊢⁺ (a+6k+4, 0, 3k+3, 0, 0)
theorem main_odd (k : ℕ) : ∀ a,
    ⟨a + k + 1, (0 : ℕ), 2 * k + 1, 0, 0⟩ [fm]⊢⁺
    ⟨a + 6 * k + 4, 0, 3 * k + 3, 0, 0⟩ := by
  rcases k with _ | k
  · simp; exact main_odd_base
  · intro a
    rw [show a + (k + 1) + 1 = a + k + 2 from by ring,
        show 2 * (k + 1) + 1 = 2 * k + 3 from by ring,
        show a + 6 * (k + 1) + 4 = a + 6 * k + 10 from by ring,
        show 3 * (k + 1) + 3 = 3 * k + 6 from by ring]
    exact main_odd_succ k a

-- Nonhalt proof.
theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 3, 0, 0⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a, (0 : ℕ), c, 0, 0⟩ ∧ 2 * a ≥ c + 1 ∧ c ≥ 3)
  · intro q ⟨A, C, hq, hinv, hc⟩
    subst hq
    rcases Nat.even_or_odd C with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- C even: C = 2K
      rcases K with _ | K
      · omega
      · -- C = 2(K+1) = 2K+2. Need A >= K+2. From 2A >= C+1 = 2K+3, so A >= K+2.
        subst hK
        have hA : A = (A - K - 2) + K + 2 := by omega
        rw [hA, show (K + 1) + (K + 1) = 2 * K + 2 from by ring]
        exact ⟨⟨(A - K - 2) + 6 * K + 8, 0, 3 * K + 6, 0, 0⟩,
               ⟨(A - K - 2) + 6 * K + 8, 3 * K + 6, rfl, by omega, by omega⟩,
               main_even K (A - K - 2)⟩
    · -- C odd: C = 2K+1. Need A >= K+1. From 2A >= C+1 = 2K+2, so A >= K+1.
      subst hK
      have hA : A = (A - K - 1) + K + 1 := by omega
      rw [hA]
      exact ⟨⟨(A - K - 1) + 6 * K + 4, 0, 3 * K + 3, 0, 0⟩,
             ⟨(A - K - 1) + 6 * K + 4, 3 * K + 3, rfl, by omega, by omega⟩,
             main_odd K (A - K - 1)⟩
  · exact ⟨2, 3, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1471
