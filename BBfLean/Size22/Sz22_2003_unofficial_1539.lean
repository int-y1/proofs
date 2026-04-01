import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1539: [7/30, 3/77, 605/3, 2/11, 63/2]

Vector representation:
```
-1 -1 -1  1  0
 0  1  0 -1 -1
 0 -1  1  0  2
 1  0  0  0 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1539

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- Phase 1a: complete phase for a ≡ 1 (mod 3).
-- (3k+1, 0, f+2k, d, 0) ⊢⁺ (0, 2, f, d+3k+1, 0).
-- By induction on k: base k=0 is one R5 step; step case is R5,R1,R1 then IH.
theorem phase1a : ∀ k, ∀ f d, ⟨3 * k + 1, 0, f + 2 * k, d, 0⟩ [fm]⊢⁺
    ⟨0, 2, f, d + 3 * k + 1, 0⟩ := by
  intro k; induction' k with k ih
  · intro f d; simp; step fm; ring_nf; finish
  · intro f d
    rw [show 3 * (k + 1) + 1 = (3 * k + 1) + 1 + 1 + 1 from by ring,
        show f + 2 * (k + 1) = (f + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 + 1 = d + 3 from by ring,
        show d + 3 * (k + 1) + 1 = (d + 3) + 3 * k + 1 from by ring]
    exact stepPlus_stepStar (ih f (d + 3))

-- Phase 1b: complete phase for a ≡ 2 (mod 3).
-- (3k+2, 0, g+2k+1, d, 0) ⊢⁺ (0, 1, g, d+3k+2, 0).
theorem phase1b : ∀ k, ∀ g d, ⟨3 * k + 2, 0, g + 2 * k + 1, d, 0⟩ [fm]⊢⁺
    ⟨0, 1, g, d + 3 * k + 2, 0⟩ := by
  intro k; induction' k with k ih
  · intro g d; simp; step fm; step fm; ring_nf; finish
  · intro g d
    rw [show 3 * (k + 1) + 2 = (3 * k + 2) + 1 + 1 + 1 from by ring,
        show g + 2 * (k + 1) + 1 = (g + 2 * k + 1) + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 + 1 = d + 3 from by ring,
        show d + 3 * (k + 1) + 2 = (d + 3) + 3 * k + 2 from by ring]
    exact stepPlus_stepStar (ih g (d + 3))

-- R4 chain: transfers e to a.
theorem r4_chain : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a + k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c e; simp; exists 0
  · intro a c e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c e); ring_nf; finish

-- R3 chain with arbitrary e.
theorem r3_chain : ∀ k, ∀ c e, ⟨0, k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro c e; simp; exists 0
  · intro c e
    step fm
    apply stepStar_trans (ih (c + 1) (e + 2)); ring_nf; finish

-- Phase 2: interleaved drain of d via R3,R2,R2 rounds, then R3 chain.
-- (0, b+1, C, D, 0) ⊢* (0, 0, C+b+1+D, 0, 2*(b+1)+D).
theorem phase2 : ∀ D, ∀ b C, ⟨0, b + 1, C, D, 0⟩ [fm]⊢*
    ⟨0, 0, C + (b + 1) + D, 0, 2 * (b + 1) + D⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih
  rcases D with _ | _ | D
  · intro b C
    rw [show C + (b + 1) + 0 = C + (b + 1) from by ring,
        show 2 * (b + 1) + 0 = 0 + 2 * (b + 1) from by ring]
    exact r3_chain (b + 1) C 0
  · intro b C
    step fm; step fm
    rw [show C + (b + 1) + 1 = C + 1 + (b + 1) from by ring,
        show 2 * (b + 1) + 1 = 1 + 2 * (b + 1) from by ring]
    exact r3_chain (b + 1) (C + 1) 1
  · intro b C
    rw [show (D + 2 : ℕ) = D + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih D (by omega) (b + 1) (C + 1)); ring_nf; finish

-- Type A transition: a ≡ 1 (mod 3).
-- (3k+1, 0, f+2k, 0, 0) ⊢⁺ (3k+5, 0, f+3k+3, 0, 0)
theorem trans_mod1 (k f : ℕ) :
    ⟨3 * k + 1, 0, f + 2 * k, 0, 0⟩ [fm]⊢⁺ ⟨3 * k + 5, 0, f + 3 * k + 3, 0, 0⟩ := by
  -- Phase 1a: ⊢⁺ (0, 2, f, 3k+1, 0)
  apply stepPlus_stepStar_stepPlus (phase1a k f 0)
  rw [show 0 + 3 * k + 1 = 3 * k + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from rfl]
  -- Phase 2: ⊢* (0, 0, f+3k+3, 0, 3k+5)
  apply stepStar_trans (phase2 (3 * k + 1) 1 f)
  rw [show f + (1 + 1) + (3 * k + 1) = f + 3 * k + 3 from by ring,
      show 2 * (1 + 1) + (3 * k + 1) = 0 + (3 * k + 5) from by ring]
  -- Phase 3: R4 chain ⊢* (3k+5, 0, f+3k+3, 0, 0)
  apply stepStar_trans (r4_chain (3 * k + 5) 0 (f + 3 * k + 3) 0)
  ring_nf; finish

-- Type B transition: a ≡ 2 (mod 3).
-- (3k+2, 0, g+2k+1, 0, 0) ⊢⁺ (3k+4, 0, g+3k+3, 0, 0)
theorem trans_mod2 (k g : ℕ) :
    ⟨3 * k + 2, 0, g + 2 * k + 1, 0, 0⟩ [fm]⊢⁺ ⟨3 * k + 4, 0, g + 3 * k + 3, 0, 0⟩ := by
  -- Phase 1b: ⊢⁺ (0, 1, g, 3k+2, 0)
  apply stepPlus_stepStar_stepPlus (phase1b k g 0)
  rw [show 0 + 3 * k + 2 = 3 * k + 2 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  -- Phase 2: ⊢* (0, 0, g+3k+3, 0, 3k+4)
  apply stepStar_trans (phase2 (3 * k + 2) 0 g)
  rw [show g + (0 + 1) + (3 * k + 2) = g + 3 * k + 3 from by ring,
      show 2 * (0 + 1) + (3 * k + 2) = 0 + (3 * k + 4) from by ring]
  -- Phase 3: R4 chain
  apply stepStar_trans (r4_chain (3 * k + 4) 0 (g + 3 * k + 3) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3 * 1 + 2, 0, 0 + 2 * 1 + 1, 0, 0⟩)
  · execute fm 10
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ (∃ k f, q = ⟨3 * k + 1, 0, f + 2 * k, 0, 0⟩) ∨
                   (∃ k g, q = ⟨3 * k + 2, 0, g + 2 * k + 1, 0, 0⟩))
  · intro q hq
    rcases hq with ⟨k, f, rfl⟩ | ⟨k, g, rfl⟩
    · refine ⟨⟨3 * (k + 1) + 2, 0, (f + k) + 2 * (k + 1) + 1, 0, 0⟩,
        Or.inr ⟨k + 1, f + k, ?_⟩, ?_⟩
      · ring_nf
      · rw [show 3 * (k + 1) + 2 = 3 * k + 5 from by ring,
             show (f + k) + 2 * (k + 1) + 1 = f + 3 * k + 3 from by ring]
        exact trans_mod1 k f
    · refine ⟨⟨3 * (k + 1) + 1, 0, (g + k + 1) + 2 * (k + 1), 0, 0⟩,
        Or.inl ⟨k + 1, g + k + 1, ?_⟩, ?_⟩
      · ring_nf
      · rw [show 3 * (k + 1) + 1 = 3 * k + 4 from by ring,
             show (g + k + 1) + 2 * (k + 1) = g + 3 * k + 3 from by ring]
        exact trans_mod2 k g
  · exact Or.inr ⟨1, 0, by ring_nf⟩

end Sz22_2003_unofficial_1539
