import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1308: [63/10, 121/2, 4/77, 5/3, 21/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 2  0  0 -1 -1
 0 -1  1  0  0
 0  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1308

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R1R1R3 chain: each round processes 2 from c.
theorem r1r1r3_chain : ∀ k, ∀ c b d e,
    ⟨2, b, c + 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 4 * k, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c b d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih c (b + 4) (d + 1) e)
    ring_nf; finish

-- R3R2R2 drain: each round decreases d by 1, increases e by 3.
theorem r3r2r2_drain : ∀ k, ∀ b d e,
    ⟨0, b, 0, d + k, e + k⟩ [fm]⊢* ⟨0, b, 0, d, e + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + k + 4 = (e + 4) + k from by ring]
    apply stepStar_trans (ih b d (e + 4))
    ring_nf; finish

-- R4 chain: moves b to c.
theorem r4_chain : ∀ b, ∀ c e,
    ⟨0, b, c, 0, e⟩ [fm]⊢* ⟨0, 0, b + c, 0, e⟩ := by
  intro b; induction' b with b ih <;> intro c e
  · ring_nf; exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

-- Odd c transition: (0, 0, 2m+1, 0, f+2m+3) →⁺ (0, 0, 4m+3, 0, f+4m+6)
theorem odd_trans : ∀ m f,
    ⟨0, 0, 2 * m + 1, 0, f + 2 * m + 3⟩ [fm]⊢⁺
    ⟨0, 0, 4 * m + 3, 0, f + 4 * m + 6⟩ := by
  intro m f
  -- Rewrite e so that R5 can fire: e = X + 1 where X = f + 2m + 2
  rw [show f + 2 * m + 3 = f + 2 * m + 2 + 1 from by ring]
  step fm  -- R5: (0, 1, 2m+1, 1, f+2m+2)
  -- For R3: need d+1 and e+1 pattern. d=1 already matches. e = f+2m+2, need it as X+1.
  rw [show f + 2 * m + 2 = f + 2 * m + 1 + 1 from by ring]
  step fm  -- R3: (2, 1, 2m+1, 0, f+2m+1)
  -- Now apply R1R1R3 chain: (2, 1, 1+2m, 0, (f+m+1)+m)
  rw [show 2 * m + 1 = 1 + 2 * m from by ring,
      show f + 2 * m + 1 = (f + m + 1) + m from by ring]
  apply stepStar_trans (r1r1r3_chain m 1 1 0 (f + m + 1))
  -- Now at (2, 4m+1, 1, m, f+m+1)
  rw [show 1 + 4 * m = 4 * m + 1 from by ring,
      show 0 + m = m from by ring]
  -- R1 (c=1): need c+1 pattern. c=1 = 0+1. ✓
  step fm  -- R1: (1, 4m+3, 0, m+1, f+m+1)
  -- R2 (a=1, c=0): ✓
  step fm  -- R2: (0, 4m+3, 0, m+1, f+m+3)
  -- Drain: (0, 4m+3, 0, 0+(m+1), (f+2)+(m+1))
  rw [show 4 * m + 1 + 2 = 4 * m + 3 from by ring,
      show m + 1 = 0 + (m + 1) from by ring,
      show f + m + 1 + 2 = (f + 2) + (m + 1) from by ring]
  apply stepStar_trans (r3r2r2_drain (m + 1) (4 * m + 3) 0 (f + 2))
  -- R4 chain: (0, 4m+3, 0, 0, f+2+4(m+1)) = (0, 4m+3, 0, 0, f+4m+6)
  rw [show f + 2 + 4 * (m + 1) = f + 4 * m + 6 from by ring]
  apply stepStar_trans (r4_chain (4 * m + 3) 0 (f + 4 * m + 6))
  ring_nf; finish

-- Even c transition (c >= 2): (0, 0, 2m+2, 0, f+2m+4) →⁺ (0, 0, 4m+5, 0, f+4m+8)
theorem even_trans : ∀ m f,
    ⟨0, 0, 2 * m + 2, 0, f + 2 * m + 4⟩ [fm]⊢⁺
    ⟨0, 0, 4 * m + 5, 0, f + 4 * m + 8⟩ := by
  intro m f
  rw [show f + 2 * m + 4 = f + 2 * m + 3 + 1 from by ring]
  step fm  -- R5
  rw [show f + 2 * m + 3 = f + 2 * m + 2 + 1 from by ring]
  step fm  -- R3
  rw [show 2 * m + 2 = 0 + 2 * (m + 1) from by ring,
      show f + 2 * m + 2 = (f + m + 1) + (m + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (m + 1) 0 1 0 (f + m + 1))
  rw [show 1 + 4 * (m + 1) = 4 * m + 5 from by ring,
      show 0 + (m + 1) = m + 1 from by ring]
  step fm  -- R2: (1, 4m+5, 0, m+1, f+m+3)
  step fm  -- R2: (0, 4m+5, 0, m+1, f+m+5)
  rw [show m + 1 = 0 + (m + 1) from by ring,
      show f + m + 1 + 2 + 2 = (f + 4) + (m + 1) from by ring]
  apply stepStar_trans (r3r2r2_drain (m + 1) (4 * m + 5) 0 (f + 4))
  rw [show f + 4 + 4 * (m + 1) = f + 4 * m + 8 from by ring]
  apply stepStar_trans (r4_chain (4 * m + 5) 0 (f + 4 * m + 8))
  ring_nf; finish

-- c=0 transition: (0, 0, 0, 0, f+2) →⁺ (0, 0, 1, 0, f+4)
theorem zero_trans : ∀ f,
    ⟨0, 0, 0, 0, f + 2⟩ [fm]⊢⁺ ⟨0, 0, 1, 0, f + 4⟩ := by
  intro f
  rw [show f + 2 = f + 1 + 1 from by ring]
  step fm  -- R5
  step fm  -- R3
  step fm  -- R2
  step fm  -- R2
  step fm  -- R4
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c f, q = ⟨0, 0, c, 0, f + c + 2⟩)
  · intro q ⟨c, f, hq⟩; subst hq
    rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      rcases m with _ | m
      · -- c = 0
        refine ⟨⟨0, 0, 1, 0, f + 4⟩, ⟨1, f + 1, rfl⟩, ?_⟩
        rw [show f + 0 + 2 = f + 2 from by ring]
        exact zero_trans f
      · -- c = 2(m+1)
        refine ⟨⟨0, 0, 4 * m + 5, 0, f + 4 * m + 8⟩,
          ⟨4 * m + 5, f + 1, by simp [Q]; ring⟩, ?_⟩
        rw [show f + 2 * (m + 1) + 2 = f + 2 * m + 4 from by ring]
        exact even_trans m f
    · subst hm
      -- c = 2m+1
      refine ⟨⟨0, 0, 4 * m + 3, 0, f + 4 * m + 6⟩,
        ⟨4 * m + 3, f + 1, by simp [Q]; ring⟩, ?_⟩
      rw [show f + (2 * m + 1) + 2 = f + 2 * m + 3 from by ring]
      exact odd_trans m f
  · exact ⟨0, 0, rfl⟩
