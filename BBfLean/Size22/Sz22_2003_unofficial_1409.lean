import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1409: [7/15, 11/3, 36/77, 5/11, 63/2]

Vector representation:
```
 0 -1 -1  1  0
 0 -1  0  0  1
 2  2  0 -1 -1
 0  0  1  0 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1409

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- Drain c by 2, increase d by 3 (R5+R1+R1 repeated).
theorem drain_c : ∀ k a c d, ⟨a + k, 0, 2 * k + c, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) + c = (2 * k + c) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 3)); ring_nf; finish

-- R4 drain: e to c.
theorem e_to_c : ∀ k c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- R3+R2+R2 chain.
theorem r3r2r2_chain : ∀ k a d e, ⟨a, 0, 0, d + k, e + 1⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e + 1 + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 2) d (e + 1)); ring_nf; finish

-- R5+R2+R2+R3chain+R4: (A+1, 0, 0, d, 0) ⊢⁺ (A+2d+2, 0, d+3, 0, 0).
theorem r5_chain_r4 (A d : ℕ) :
    ⟨A + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨A + 2 * d + 2, 0, d + 3, 0, 0⟩ := by
  step fm  -- R5: (A, 2, 0, d+1, 0)
  step fm  -- R2: (A, 1, 0, d+1, 1)
  step fm  -- R2: (A, 0, 0, d+1, 2)
  rw [show d + 1 = 0 + (d + 1) from by ring,
      show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (d + 1) A 0 1)
  rw [show A + 2 * (d + 1) = A + 2 * d + 2 from by ring,
      show 1 + 1 + (d + 1) = 0 + (d + 3) from by ring]
  apply stepStar_trans (e_to_c (d + 3) 0 0)
  ring_nf; finish

-- R5+R1+R2+R3chain+R4: (A+1, 0, 1, d, 0) ⊢⁺ (A+2d+4, 0, d+3, 0, 0).
theorem r5_r1_chain_r4 (A d : ℕ) :
    ⟨A + 1, 0, 1, d, 0⟩ [fm]⊢⁺ ⟨A + 2 * d + 4, 0, d + 3, 0, 0⟩ := by
  step fm  -- R5: (A, 2, 1, d+1, 0)
  step fm  -- R1: (A, 1, 0, d+2, 0)
  step fm  -- R2: (A, 0, 0, d+2, 1)
  rw [show d + 2 = 0 + (d + 2) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (d + 2) A 0 0)
  rw [show A + 2 * (d + 2) = A + 2 * d + 4 from by ring,
      show 0 + 1 + (d + 2) = 0 + (d + 3) from by ring]
  apply stepStar_trans (e_to_c (d + 3) 0 0)
  ring_nf; finish

-- Even transition: (A+K+2, 0, 2K+2, 0, 0) ⊢⁺ (A+6K+8, 0, 3K+6, 0, 0).
theorem main_even (A K : ℕ) :
    ⟨A + K + 2, 0, 2 * K + 2, 0, 0⟩ [fm]⊢⁺ ⟨A + 6 * K + 8, 0, 3 * K + 6, 0, 0⟩ := by
  rw [show A + K + 2 = (A + 1) + (K + 1) from by ring,
      show 2 * K + 2 = 2 * (K + 1) + 0 from by ring]
  apply stepStar_stepPlus_stepPlus (drain_c (K + 1) (A + 1) 0 0)
  rw [show 0 + 3 * (K + 1) = 3 * K + 3 from by ring,
      show A + 6 * K + 8 = A + 2 * (3 * K + 3) + 2 from by ring,
      show 3 * K + 6 = (3 * K + 3) + 3 from by ring]
  exact r5_chain_r4 A (3 * K + 3)

-- Odd transition: (A+K+2, 0, 2K+3, 0, 0) ⊢⁺ (A+6K+10, 0, 3K+6, 0, 0).
theorem main_odd (A K : ℕ) :
    ⟨A + K + 2, 0, 2 * K + 3, 0, 0⟩ [fm]⊢⁺ ⟨A + 6 * K + 10, 0, 3 * K + 6, 0, 0⟩ := by
  rw [show A + K + 2 = (A + 1) + (K + 1) from by ring,
      show 2 * K + 3 = 2 * (K + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (drain_c (K + 1) (A + 1) 1 0)
  rw [show 0 + 3 * (K + 1) = 3 * K + 3 from by ring,
      show A + 6 * K + 10 = A + 2 * (3 * K + 3) + 4 from by ring,
      show 3 * K + 6 = (3 * K + 3) + 3 from by ring]
  exact r5_r1_chain_r4 A (3 * K + 3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 3, 0, 0⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A K, q = ⟨A + K + 2, 0, 2 * K + 2, 0, 0⟩ ∨
                          q = ⟨A + K + 2, 0, 2 * K + 3, 0, 0⟩)
  · intro q ⟨A, K, hq⟩
    rcases hq with hq | hq <;> subst hq <;>
      rcases Nat.even_or_odd K with ⟨M, hM⟩ | ⟨M, hM⟩ <;> subst hM
    · -- Even c, K=2M: target (A+6(2M)+8, 0, 3(2M)+6, 0, 0) = (A+12M+8, 0, 6M+6, 0, 0)
      refine ⟨⟨A + 9 * M + 4 + (3 * M + 2) + 2, 0, 2 * (3 * M + 2) + 2, 0, 0⟩,
        ⟨A + 9 * M + 4, 3 * M + 2, Or.inl rfl⟩, ?_⟩
      rw [show A + 9 * M + 4 + (3 * M + 2) + 2 = A + 12 * M + 8 from by ring,
          show 2 * (3 * M + 2) + 2 = 6 * M + 6 from by ring,
          show A + (M + M) + 2 = A + 2 * M + 2 from by ring,
          show 2 * (M + M) + 2 = 4 * M + 2 from by ring,
          show A + 12 * M + 8 = A + 6 * (2 * M) + 8 from by ring,
          show 6 * M + 6 = 3 * (2 * M) + 6 from by ring,
          show 4 * M + 2 = 2 * (2 * M) + 2 from by ring,
          show A + 2 * M + 2 = A + (2 * M) + 2 from by ring]
      exact main_even A (2 * M)
    · -- Even c, K=2M+1
      refine ⟨⟨A + 9 * M + 9 + (3 * M + 3) + 2, 0, 2 * (3 * M + 3) + 3, 0, 0⟩,
        ⟨A + 9 * M + 9, 3 * M + 3, Or.inr rfl⟩, ?_⟩
      rw [show A + 9 * M + 9 + (3 * M + 3) + 2 = A + 12 * M + 14 from by ring,
          show 2 * (3 * M + 3) + 3 = 6 * M + 9 from by ring,
          show A + 12 * M + 14 = A + 6 * (2 * M + 1) + 8 from by ring,
          show 6 * M + 9 = 3 * (2 * M + 1) + 6 from by ring]
      exact main_even A (2 * M + 1)
    · -- Odd c, K=2M
      refine ⟨⟨A + 9 * M + 6 + (3 * M + 2) + 2, 0, 2 * (3 * M + 2) + 2, 0, 0⟩,
        ⟨A + 9 * M + 6, 3 * M + 2, Or.inl rfl⟩, ?_⟩
      rw [show A + 9 * M + 6 + (3 * M + 2) + 2 = A + 12 * M + 10 from by ring,
          show 2 * (3 * M + 2) + 2 = 6 * M + 6 from by ring,
          show A + (M + M) + 2 = A + 2 * M + 2 from by ring,
          show 2 * (M + M) + 3 = 4 * M + 3 from by ring,
          show A + 12 * M + 10 = A + 6 * (2 * M) + 10 from by ring,
          show 6 * M + 6 = 3 * (2 * M) + 6 from by ring,
          show 4 * M + 3 = 2 * (2 * M) + 3 from by ring,
          show A + 2 * M + 2 = A + (2 * M) + 2 from by ring]
      exact main_odd A (2 * M)
    · -- Odd c, K=2M+1
      refine ⟨⟨A + 9 * M + 11 + (3 * M + 3) + 2, 0, 2 * (3 * M + 3) + 3, 0, 0⟩,
        ⟨A + 9 * M + 11, 3 * M + 3, Or.inr rfl⟩, ?_⟩
      rw [show A + 9 * M + 11 + (3 * M + 3) + 2 = A + 12 * M + 16 from by ring,
          show 2 * (3 * M + 3) + 3 = 6 * M + 9 from by ring,
          show A + 12 * M + 16 = A + 6 * (2 * M + 1) + 10 from by ring,
          show 6 * M + 9 = 3 * (2 * M + 1) + 6 from by ring]
      exact main_odd A (2 * M + 1)
  · exact ⟨0, 0, Or.inr rfl⟩

end Sz22_2003_unofficial_1409
