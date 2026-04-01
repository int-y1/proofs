import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1542: [7/30, 33/2, 8/35, 5/11, 35/3]

Vector representation:
```
-1 -1 -1  1  0
-1  1  0  0  1
 3  0 -1 -1  0
 0  0  1  0 -1
 0 -1  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1542

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 chain: transfer e to c.
theorem e_to_c : ∀ k, ∀ b c, ⟨0, b, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro b c; exists 0
  · intro b c; rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1)); ring_nf; finish

-- R2 chain: drain a, building b and e.
theorem r2_chain : ∀ k, ∀ b d e, ⟨a + k, b, 0, d, e⟩ [fm]⊢* ⟨a, b + k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro b d e; exists 0
  · intro b d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d (e + 1)); ring_nf; finish

-- R1/R3 full cycle: one round of R1×3 + R3.
-- (3, b+3, c+4, d, 0) -> (3, b, c, d+2, 0)
theorem r1r3_round : ∀ k, ∀ b c d, ⟨3, b + 3 * k, c + 4 * k, d, 0⟩ [fm]⊢*
    ⟨3, b, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih
  · intro b c d; simp; exists 0
  · intro b c d
    rw [show b + 3 * (k + 1) = (b + 3 * k) + 1 + 1 + 1 from by ring,
        show c + 4 * (k + 1) = (c + 4 * k) + 1 + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih b c (d + 2)); ring_nf; finish

-- Micro-cycle: (0, b, 0, d+1, e+1) ⊢* (0, b+3*(d+1), 0, 0, e+2*d+3).
-- Each round: R4, R3, R2×3.
theorem micro_cycle : ∀ d, ∀ b e, ⟨0, b, 0, d + 1, e + 1⟩ [fm]⊢*
    ⟨0, b + 3 * (d + 1), 0, 0, e + 2 * d + 3⟩ := by
  intro d; induction' d with d ih
  · intro b e; simp
    step fm; step fm; step fm; step fm; step fm
    ring_nf; finish
  · intro b e
    rw [show (d + 1) + 1 = d + 2 from by ring,
        show e + 1 = (e + 1) from rfl]
    step fm; step fm; step fm; step fm; step fm
    rw [show b + 3 = (b + 3) from rfl,
        show e + 3 = (e + 2) + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    apply stepStar_trans (ih (b + 3) (e + 2)); ring_nf; finish

-- Type A transition: e ≡ 1 mod 4.
-- (0, F+3K+2, 0, 0, 4K+1) ⊢⁺ (0, (F+3K+1)+3K+4, 0, 0, 4K+4)
-- i.e., (0, F+3K+2, 0, 0, 4K+1) ⊢⁺ (0, F+6K+5, 0, 0, 4K+4)
-- Phase: R4 × (4K+1), R5, R3, R1/R3 drain × K rounds, then R1×1, R2×2, micro × (2K+1)
theorem trans_A (K F : ℕ) :
    ⟨0, F + 3 * K + 2, 0, 0, 4 * K + 1⟩ [fm]⊢⁺
    ⟨0, F + 6 * K + 5, 0, 0, 4 * K + 4⟩ := by
  -- R4 chain: (0, F+3K+2, 0, 0, 4K+1) -> (0, F+3K+2, 4K+1, 0, 0)
  rw [show (4 * K + 1 : ℕ) = 0 + (4 * K + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (4 * K + 1) (F + 3 * K + 2) 0 (e := 0))
  rw [show 0 + (4 * K + 1) = 4 * K + 1 from by ring]
  -- R5: (0, F+3K+2, 4K+1, 0, 0) -> (0, F+3K+1, 4K+2, 1, 0)
  rw [show F + 3 * K + 2 = (F + 3 * K + 1) + 1 from by ring,
      show 4 * K + 1 = (4 * K + 1) from rfl]
  step fm
  -- R3: (0, F+3K+1, 4K+2, 1, 0) -> (3, F+3K+1, 4K+1, 0, 0)
  rw [show 4 * K + 2 = (4 * K + 1) + 1 from by ring]
  step fm
  -- R1/R3 drain × K rounds: (3, F+3K+1, 4K+1, 0, 0) -> (3, F+1, 1, 2K, 0)
  rw [show F + 3 * K + 1 = (F + 1) + 3 * K from by ring,
      show 4 * K + 1 = 1 + 4 * K from by ring]
  apply stepStar_trans (r1r3_round K (F + 1) 1 0)
  rw [show 0 + 2 * K = 2 * K from by ring]
  -- R1: (3, F+1, 1, 2K, 0) -> (2, F, 0, 2K+1, 0)
  rw [show (F + 1 : ℕ) = F + 1 from rfl]
  step fm
  -- R2×2: (2, F, 0, 2K+1, 0) -> (0, F+2, 0, 2K+1, 2)
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (r2_chain 2 F (2 * K + 1) 0 (a := 0))
  rw [show 0 + 2 = 2 from by ring,
      show F + 2 = F + 2 from rfl]
  -- micro × (2K+1): (0, F+2, 0, 2K+1, 2) -> (0, F+2+3(2K+1), 0, 0, 2+2*2K+3)
  rw [show (2 * K + 1 : ℕ) = 2 * K + 1 from rfl,
      show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (micro_cycle (2 * K) (F + 2) 1)
  ring_nf; finish

-- Type B transition: e ≡ 0 mod 4.
-- (0, G+3K+4, 0, 0, 4K+4) ⊢⁺ (0, G+6K+9, 0, 0, 4K+7)
-- Phase: R4 × (4K+4), R5, R3, R1/R3 drain × (K+1), then R2×3, micro × (2K+2)
theorem trans_B (K G : ℕ) :
    ⟨0, G + 3 * K + 4, 0, 0, 4 * K + 4⟩ [fm]⊢⁺
    ⟨0, G + 6 * K + 9, 0, 0, 4 * K + 7⟩ := by
  -- R4 chain
  rw [show (4 * K + 4 : ℕ) = 0 + (4 * K + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (4 * K + 4) (G + 3 * K + 4) 0 (e := 0))
  rw [show 0 + (4 * K + 4) = 4 * K + 4 from by ring]
  -- R5
  rw [show G + 3 * K + 4 = (G + 3 * K + 3) + 1 from by ring,
      show 4 * K + 4 = (4 * K + 4) from rfl]
  step fm
  -- R3
  rw [show 4 * K + 5 = (4 * K + 4) + 1 from by ring]
  step fm
  -- R1/R3 drain × (K+1): (3, G+3K+3, 4K+4, 0, 0) -> (3, G, 0, 2K+2, 0)
  rw [show G + 3 * K + 3 = G + 3 * (K + 1) from by ring,
      show 4 * K + 4 = 0 + 4 * (K + 1) from by ring]
  apply stepStar_trans (r1r3_round (K + 1) G 0 0)
  rw [show 0 + 2 * (K + 1) = 2 * K + 2 from by ring]
  -- R2×3: (3, G, 0, 2K+2, 0) -> (0, G+3, 0, 2K+2, 3)
  rw [show (3 : ℕ) = 0 + 3 from by ring]
  apply stepStar_trans (r2_chain 3 G (2 * K + 2) 0 (a := 0))
  rw [show 0 + 3 = 3 from by ring,
      show G + 3 = G + 3 from rfl]
  -- micro × (2K+2): (0, G+3, 0, 2K+2, 3) -> (0, G+3+3(2K+2), 0, 0, 3+2(2K+1)+3)
  rw [show (2 * K + 2 : ℕ) = (2 * K + 1) + 1 from by ring,
      show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (micro_cycle (2 * K + 1) (G + 3) 2)
  ring_nf; finish

-- Type C transition: e ≡ 3 mod 4.
-- (0, H+3K+8, 0, 0, 4K+7) ⊢⁺ (0, H+6K+18, 0, 0, 4K+13)
-- Phase: R4 × (4K+7), R5, R3, R1/R3 drain × (K+1), then R1×3, R5, R3, R2×3, micro × (2K+3)
theorem trans_C (K H : ℕ) :
    ⟨0, H + 3 * K + 8, 0, 0, 4 * K + 7⟩ [fm]⊢⁺
    ⟨0, H + 6 * K + 18, 0, 0, 4 * K + 13⟩ := by
  -- R4 chain
  rw [show (4 * K + 7 : ℕ) = 0 + (4 * K + 7) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (4 * K + 7) (H + 3 * K + 8) 0 (e := 0))
  rw [show 0 + (4 * K + 7) = 4 * K + 7 from by ring]
  -- R5
  rw [show H + 3 * K + 8 = (H + 3 * K + 7) + 1 from by ring,
      show 4 * K + 7 = (4 * K + 7) from rfl]
  step fm
  -- R3
  rw [show 4 * K + 8 = (4 * K + 7) + 1 from by ring]
  step fm
  -- R1/R3 drain × (K+1): (3, H+3K+7, 4K+7, 0, 0) -> (3, H+4, 3, 2K+2, 0)
  rw [show H + 3 * K + 7 = (H + 4) + 3 * (K + 1) from by ring,
      show 4 * K + 7 = 3 + 4 * (K + 1) from by ring]
  apply stepStar_trans (r1r3_round (K + 1) (H + 4) 3 0)
  rw [show 0 + 2 * (K + 1) = 2 * K + 2 from by ring]
  -- R1×3: (3, H+4, 3, 2K+2, 0) -> (0, H+1, 0, 2K+5, 0)
  rw [show (H + 4 : ℕ) = (H + 1) + 1 + 1 + 1 from by ring,
      show (3 : ℕ) = 0 + 1 + 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show 2 * K + 2 + 1 + 1 + 1 = 2 * K + 5 from by ring]
  -- R5: (0, H+1, 0, 2K+5, 0) -> (0, H, 1, 2K+6, 0)
  rw [show H + 1 = H + 1 from rfl]
  step fm
  -- R3: (0, H, 1, 2K+6, 0) -> (3, H, 0, 2K+5, 0)
  step fm
  -- R2×3: (3, H, 0, 2K+5, 0) -> (0, H+3, 0, 2K+5, 3)
  rw [show (3 : ℕ) = 0 + 3 from by ring]
  apply stepStar_trans (r2_chain 3 H (2 * K + 5) 0 (a := 0))
  rw [show 0 + 3 = 3 from by ring,
      show H + 3 = H + 3 from rfl]
  -- micro × (2K+5): (0, H+3, 0, 2K+5, 3) -> (0, H+3+3(2K+5), 0, 0, 3+2(2K+4)+3)
  rw [show (2 * K + 5 : ℕ) = (2 * K + 4) + 1 from by ring,
      show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (micro_cycle (2 * K + 4) (H + 3) 2)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0 + 3 * 0 + 4, 0, 0, 4 * 0 + 4⟩)
  · execute fm 12
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦
      (∃ K F, q = ⟨0, F + 3 * K + 2, 0, 0, 4 * K + 1⟩) ∨
      (∃ K G, q = ⟨0, G + 3 * K + 4, 0, 0, 4 * K + 4⟩) ∨
      (∃ K H, q = ⟨0, H + 3 * K + 8, 0, 0, 4 * K + 7⟩))
  · intro q hq
    rcases hq with ⟨K, F, rfl⟩ | ⟨K, G, rfl⟩ | ⟨K, H, rfl⟩
    · -- P1 -> P2
      refine ⟨⟨0, F + 6 * K + 5, 0, 0, 4 * K + 4⟩,
        Or.inr (Or.inl ⟨K, F + 3 * K + 1, by ring_nf⟩), ?_⟩
      exact trans_A K F
    · -- P2 -> P3
      refine ⟨⟨0, G + 6 * K + 9, 0, 0, 4 * K + 7⟩,
        Or.inr (Or.inr ⟨K, G + 3 * K + 1, by ring_nf⟩), ?_⟩
      exact trans_B K G
    · -- P3 -> P1
      refine ⟨⟨0, H + 6 * K + 18, 0, 0, 4 * K + 13⟩,
        Or.inl ⟨K + 3, H + 3 * K + 7, by ring_nf⟩, ?_⟩
      exact trans_C K H
  · exact Or.inr (Or.inl ⟨0, 0, by ring_nf⟩)

end Sz22_2003_unofficial_1542
