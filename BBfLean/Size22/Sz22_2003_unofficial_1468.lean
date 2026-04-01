import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1468: [7/15, 3/847, 50/7, 11/5, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -2
 1  0  2 -1  0
 0  0 -1  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1468

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4: drain c to e
theorem r4_chain : ∀ k a e, (⟨a, 0, k, 0, e⟩ : Q) [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; ring_nf; finish
  | succ k ih =>
    intro a e; step fm
    apply stepStar_trans (ih a (e + 1)); ring_nf; finish

-- R3: drain d, accumulate a and c (e=0)
theorem r3_chain_e0 : ∀ k a c, (⟨a, 0, c, k, 0⟩ : Q) [fm]⊢* ⟨a + k, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; ring_nf; finish
  | succ k ih =>
    intro a c; step fm
    apply stepStar_trans (ih (a + 1) (c + 2)); ring_nf; finish

-- R3: drain d, accumulate a and c (e=1)
theorem r3_chain_e1 : ∀ k a c, (⟨a, 0, c, k, 1⟩ : Q) [fm]⊢* ⟨a + k, 0, c + 2 * k, 0, 1⟩ := by
  intro k; induction k with
  | zero => intro a c; ring_nf; finish
  | succ k ih =>
    intro a c; step fm
    apply stepStar_trans (ih (a + 1) (c + 2)); ring_nf; finish

-- R5/R2 pairs (odd e): (a+k+1, b, 0, 0, 2k+1) ⊢* (a, b+2k+1, 0, 1, 1)
-- k pairs of R5/R2, then one final R5
theorem r5r2_odd : ∀ k a b, (⟨a + k + 1, b, 0, 0, 2 * k + 1⟩ : Q) [fm]⊢*
    ⟨a, b + 2 * k + 1, 0, 1, 1⟩ := by
  intro k; induction k with
  | zero => intro a b; step fm; ring_nf; finish
  | succ k ih =>
    intro a b
    rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
        show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (b + 2)); ring_nf; finish

-- R5/R2 pairs (even e): (a+k+1, b, 0, 0, 2k+2) ⊢* (a, b+2k+2, 0, 0, 0)
theorem r5r2_even : ∀ k a b, (⟨a + k + 1, b, 0, 0, 2 * (k + 1)⟩ : Q) [fm]⊢*
    ⟨a, b + 2 * (k + 1), 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; step fm; step fm; ring_nf; finish
  | succ k ih =>
    intro a b
    rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
        show 2 * (k + 1 + 1) = 2 * (k + 1) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (b + 2)); ring_nf; finish

-- R3/R1 round chain with e=1: each round (A, B+2, 0, D+1, 1) -R3R1R1-> (A+1, B, 0, D+2, 1)
theorem r3r1_chain_e1 : ∀ k A B D,
    (⟨A, B + 2 * k, 0, D + 1, 1⟩ : Q) [fm]⊢* ⟨A + k, B, 0, D + k + 1, 1⟩ := by
  intro k; induction k with
  | zero => intro A B D; ring_nf; finish
  | succ k ih =>
    intro A B D
    rw [show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 1) B (D + 1)); ring_nf; finish

-- R3/R1 round chain with e=0
theorem r3r1_chain_e0 : ∀ k A B D,
    (⟨A, B + 2 * k, 0, D + 1, 0⟩ : Q) [fm]⊢* ⟨A + k, B, 0, D + k + 1, 0⟩ := by
  intro k; induction k with
  | zero => intro A B D; ring_nf; finish
  | succ k ih =>
    intro A B D
    rw [show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 1) B (D + 1)); ring_nf; finish

-- Main transition: (3k²+3k+2, 0, 6k+3, 0, 0) ⊢⁺ (3k²+9k+8, 0, 6k+9, 0, 0)
theorem main_trans (k : ℕ) :
    (⟨3 * k ^ 2 + 3 * k + 2, 0, 6 * k + 3, 0, 0⟩ : Q) [fm]⊢⁺
    ⟨3 * k ^ 2 + 9 * k + 8, 0, 6 * k + 9, 0, 0⟩ := by
  -- Phase 1: R4 drain c to e
  have p1 : (⟨3 * k ^ 2 + 3 * k + 2, 0, 6 * k + 3, 0, 0⟩ : Q) [fm]⊢⁺
      ⟨3 * k ^ 2 + 3 * k + 2, 0, 0, 0, 6 * k + 3⟩ := by
    rw [show (6 * k + 3 : ℕ) = (6 * k + 2) + 1 from by ring]
    step fm
    have := r4_chain (6 * k + 2) (3 * k ^ 2 + 3 * k + 2) 1
    rw [show 1 + (6 * k + 2) = 6 * k + 3 from by ring] at this; exact this
  -- Phase 2: R5/R2 odd drain
  -- e = 6k+3 = 2*(3k+1)+1, with K=3k+1
  -- (3k²+3k+2, 0, 0, 0, 6k+3) -> (3k², 6k+3, 0, 1, 1)
  have p2 : (⟨3 * k ^ 2 + 3 * k + 2, 0, 0, 0, 6 * k + 3⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2, 6 * k + 3, 0, 1, 1⟩ := by
    rw [show 3 * k ^ 2 + 3 * k + 2 = 3 * k ^ 2 + (3 * k + 1) + 1 from by ring,
        show (6 * k + 3 : ℕ) = 2 * (3 * k + 1) + 1 from by ring]
    have := r5r2_odd (3 * k + 1) (3 * k ^ 2) 0
    simp only [Nat.zero_add] at this; exact this
  -- Phase 3: R3/R1 chain with e=1
  -- (3k², 6k+3, 0, 1, 1) -> (3k²+3k+1, 1, 0, 3k+2, 1)
  -- B=6k+3=1+2*(3k+1), rounds=3k+1
  have p3 : (⟨3 * k ^ 2, 6 * k + 3, 0, 1, 1⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 3 * k + 1, 1, 0, 3 * k + 2, 1⟩ := by
    rw [show (6 * k + 3 : ℕ) = 1 + 2 * (3 * k + 1) from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    have := r3r1_chain_e1 (3 * k + 1) (3 * k ^ 2) 1 0
    simp only [Nat.zero_add] at this
    rw [show 3 * k ^ 2 + (3 * k + 1) = 3 * k ^ 2 + 3 * k + 1 from by ring] at this; exact this
  -- Phase 4: tail B=1 with e=1
  -- (3k²+3k+1, 1, 0, 3k+2, 1) -> (3k²+3k+2, 0, 1, 3k+2, 1)
  have p4 : (⟨3 * k ^ 2 + 3 * k + 1, 1, 0, 3 * k + 2, 1⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 3 * k + 2, 0, 1, 3 * k + 2, 1⟩ := by
    rw [show (3 * k + 2 : ℕ) = (3 * k + 1) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 5: R3 chain to drain d
  -- (3k²+3k+2, 0, 1, 3k+2, 1) -> (3k²+6k+4, 0, 6k+5, 0, 1)
  have p5 : (⟨3 * k ^ 2 + 3 * k + 2, 0, 1, 3 * k + 2, 1⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 6 * k + 4, 0, 6 * k + 5, 0, 1⟩ := by
    have := r3_chain_e1 (3 * k + 2) (3 * k ^ 2 + 3 * k + 2) 1
    rw [show 3 * k ^ 2 + 3 * k + 2 + (3 * k + 2) = 3 * k ^ 2 + 6 * k + 4 from by ring,
        show 1 + 2 * (3 * k + 2) = 6 * k + 5 from by ring] at this; exact this
  -- Phase 6: R4 drain c to e
  -- (3k²+6k+4, 0, 6k+5, 0, 1) -> (3k²+6k+4, 0, 0, 0, 6k+6)
  have p6 : (⟨3 * k ^ 2 + 6 * k + 4, 0, 6 * k + 5, 0, 1⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 6 * k + 4, 0, 0, 0, 6 * k + 6⟩ := by
    have := r4_chain (6 * k + 5) (3 * k ^ 2 + 6 * k + 4) 1
    rw [show 1 + (6 * k + 5) = 6 * k + 6 from by ring] at this; exact this
  -- Phase 7: R5/R2 even drain
  -- e = 6k+6 = 2*(3k+3), with K=3k+2
  -- (3k²+6k+4, 0, 0, 0, 6k+6) -> (3k²+3k+1, 6k+6, 0, 0, 0)
  -- r5r2_even K a b: (a+K+1, b, 0, 0, 2*(K+1)) ⊢* (a, b+2*(K+1), 0, 0, 0)
  -- 2*(K+1) = 6k+6, K+1 = 3k+3, K = 3k+2
  -- a+K+1 = a+3k+3 = 3k²+6k+4, so a = 3k²+3k+1
  have p7 : (⟨3 * k ^ 2 + 6 * k + 4, 0, 0, 0, 6 * k + 6⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 3 * k + 1, 6 * k + 6, 0, 0, 0⟩ := by
    rw [show 3 * k ^ 2 + 6 * k + 4 = 3 * k ^ 2 + 3 * k + 1 + (3 * k + 2) + 1 from by ring,
        show (6 * k + 6 : ℕ) = 2 * ((3 * k + 2) + 1) from by ring]
    have := r5r2_even (3 * k + 2) (3 * k ^ 2 + 3 * k + 1) 0
    simp only [Nat.zero_add] at this; exact this
  -- Phase 8: R5 + R3 to start the interleaved phase
  -- (3k²+3k+1, 6k+6, 0, 0, 0) -> via R5 -> (3k²+3k, 6k+7, 0, 1, 0) -> via R3 -> (3k²+3k+1, 6k+7, 2, 0, 0)
  have p8 : (⟨3 * k ^ 2 + 3 * k + 1, 6 * k + 6, 0, 0, 0⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 3 * k + 1, 6 * k + 7, 2, 0, 0⟩ := by
    rw [show 3 * k ^ 2 + 3 * k + 1 = (3 * k ^ 2 + 3 * k) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 9: R1 pair to open
  -- (3k²+3k+1, 6k+7, 2, 0, 0) -> (3k²+3k+1, 6k+5, 0, 2, 0)
  have p9 : (⟨3 * k ^ 2 + 3 * k + 1, 6 * k + 7, 2, 0, 0⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 3 * k + 1, 6 * k + 5, 0, 2, 0⟩ := by
    rw [show (6 * k + 7 : ℕ) = (6 * k + 5) + 2 from by ring]
    step fm; step fm; finish
  -- Phase 10: R3/R1 chain with e=0
  -- (3k²+3k+1, 6k+5, 0, 2, 0) -> (3k²+6k+3, 1, 0, 3k+4, 0)
  -- B = 6k+5 = 1 + 2*(3k+2), rounds = 3k+2
  -- D+1 = 2, D = 1
  have p10 : (⟨3 * k ^ 2 + 3 * k + 1, 6 * k + 5, 0, 2, 0⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 6 * k + 3, 1, 0, 3 * k + 4, 0⟩ := by
    rw [show (6 * k + 5 : ℕ) = 1 + 2 * (3 * k + 2) from by ring,
        show (2 : ℕ) = 1 + 1 from rfl]
    have := r3r1_chain_e0 (3 * k + 2) (3 * k ^ 2 + 3 * k + 1) 1 1
    rw [show 3 * k ^ 2 + 3 * k + 1 + (3 * k + 2) = 3 * k ^ 2 + 6 * k + 3 from by ring] at this
    rw [show 1 + (3 * k + 2) + 1 = 3 * k + 4 from by ring] at this; exact this
  -- Phase 11: tail B=1 with e=0
  -- (3k²+6k+3, 1, 0, 3k+4, 0) -> (3k²+6k+4, 0, 1, 3k+4, 0)
  have p11 : (⟨3 * k ^ 2 + 6 * k + 3, 1, 0, 3 * k + 4, 0⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 6 * k + 4, 0, 1, 3 * k + 4, 0⟩ := by
    rw [show (3 * k + 4 : ℕ) = (3 * k + 3) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 12: R3 chain to drain d
  -- (3k²+6k+4, 0, 1, 3k+4, 0) -> (3k²+9k+8, 0, 6k+9, 0, 0)
  have p12 : (⟨3 * k ^ 2 + 6 * k + 4, 0, 1, 3 * k + 4, 0⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 9 * k + 8, 0, 6 * k + 9, 0, 0⟩ := by
    have := r3_chain_e0 (3 * k + 4) (3 * k ^ 2 + 6 * k + 4) 1
    rw [show 3 * k ^ 2 + 6 * k + 4 + (3 * k + 4) = 3 * k ^ 2 + 9 * k + 8 from by ring,
        show 1 + 2 * (3 * k + 4) = 6 * k + 9 from by ring] at this; exact this
  -- Chain everything together
  exact stepPlus_stepStar_stepPlus p1
    (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4
      (stepStar_trans p5 (stepStar_trans p6 (stepStar_trans p7
        (stepStar_trans p8 (stepStar_trans p9 (stepStar_trans p10
          (stepStar_trans p11 p12))))))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨3 * 0 ^ 2 + 3 * 0 + 2, 0, 6 * 0 + 3, 0, 0⟩ : Q))
    (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨3 * k ^ 2 + 3 * k + 2, 0, 6 * k + 3, 0, 0⟩) 0
  intro k; exact ⟨k + 1, by
    rw [show 3 * (k + 1) ^ 2 + 3 * (k + 1) + 2 = 3 * k ^ 2 + 9 * k + 8 from by ring,
        show 6 * (k + 1) + 3 = 6 * k + 9 from by ring]
    exact main_trans k⟩

end Sz22_2003_unofficial_1468
