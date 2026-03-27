import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #108: [1/30, 6/77, 147/2, 15/7, 22/3]

Vector representation:
```
-1 -1 -1  0  0
 1  1  0 -1 -1
-1  1  0  2  0
 0  1  1 -1  0
 1 -1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_108

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R4 chain: (0, b, c, d+k, 0) →* (0, b+k, c+k, d, 0) when a=0, e=0
theorem r4_chain : ∀ k, ∀ b c d, ⟨0, b, c, d+k, 0⟩ [fm]⊢* ⟨0, b+k, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R5+R1 alternating: (0, b+2*k, k, 0, e) →* (0, b, 0, 0, e+k)
theorem r5r1_chain : ∀ k, ∀ b e, ⟨0, b+2*k, k, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
      show k + 1 = k + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3 drain: (a+k, b, 0, d, 0) →* (a, b+k, 0, d+2*k, 0)
theorem r3_drain : ∀ k, ∀ a b d, ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b+k, 0, d+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- One R3+R2+R2 triple: (a+1, b, 0, 0, e+2) →* (a+2, b+3, 0, 0, e)
theorem r3r2r2_step : ∀ a b e, ⟨a+1, b, 0, 0, e+2⟩ [fm]⊢* ⟨a+2, b+3, 0, 0, e⟩ := by
  intro a b e
  step fm; step fm; step fm; ring_nf; finish

-- Even drain: (a+1, b, 0, 0, 2*(k+1)) →* (a+k+2, b+3*(k+1), 0, 0, 0)
theorem even_drain : ∀ k, ∀ a b,
    ⟨a+1, b, 0, 0, 2*(k+1)⟩ [fm]⊢* ⟨a+k+2, b+3*(k+1), 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · rw [show 2 * (0 + 1) = 0 + 2 from by ring]
    apply stepStar_trans (r3r2r2_step a b 0)
    ring_nf; finish
  · rw [show 2 * (k + 1 + 1) = (2 * (k + 1)) + 2 from by ring]
    apply stepStar_trans (r3r2r2_step a b (2 * (k + 1)))
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (b + 3))
    ring_nf; finish

-- Odd drain: (a+1, b, 0, 0, 2*(k+1)+1) →* (a+k+2, b+3*(k+1), 0, 0, 1)
theorem odd_drain : ∀ k, ∀ a b,
    ⟨a+1, b, 0, 0, 2*(k+1)+1⟩ [fm]⊢* ⟨a+k+2, b+3*(k+1), 0, 0, 1⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · rw [show 2 * (0 + 1) + 1 = 1 + 2 from by ring]
    apply stepStar_trans (r3r2r2_step a b 1)
    ring_nf; finish
  · rw [show 2 * (k + 1 + 1) + 1 = (2 * (k + 1) + 1) + 2 from by ring]
    apply stepStar_trans (r3r2r2_step a b (2 * (k + 1) + 1))
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (b + 3))
    ring_nf; finish

-- Odd tail: (a+1, b, 0, 0, 1) →* (a, b+3, 0, 3, 0)
theorem odd_tail : ∀ a b, ⟨a+1, b, 0, 0, 1⟩ [fm]⊢* ⟨a, b+3, 0, 3, 0⟩ := by
  intro a b
  step fm; step fm; step fm; finish

-- Main transition for even d: (0, b'+2j+2, 0, 2j+1, 0) ⊢⁺ (0, b'+4j+5, 0, 2j+4, 0)
theorem main_even (j b' : ℕ) :
    ⟨0, b'+2*j+2, 0, 2*j+1, 0⟩ [fm]⊢⁺ ⟨0, b'+4*j+5, 0, 2*j+4, 0⟩ := by
  -- Phase 1: R4 chain (2j+1 times): → (0, b'+4j+3, 2j+1, 0, 0)
  rw [show 2 * j + 1 = 0 + (2 * j + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2*j+1) (b'+2*j+2) 0 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5+R1 chain (2j+1 times): → (0, b'+1, 0, 0, 2j+1)
  rw [show b' + 2 * j + 2 + (2 * j + 1) = (b' + 1) + 2 * (2 * j + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain (2*j+1) (b'+1) 0)
  simp only [Nat.zero_add]
  -- R5: (0, b'+1, 0, 0, 2j+1) → (1, b', 0, 0, 2j+2)
  step fm
  -- Phase 3: even drain with k=j: (1, b', 0, 0, 2(j+1)) → (j+2, b'+3(j+1), 0, 0, 0)
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) from by ring]
  apply stepStar_trans (even_drain j 0 b')
  simp only [Nat.zero_add]
  -- Phase 4: R3 drain (j+2 times): → (0, b'+3(j+1)+j+2, 0, 2(j+2), 0)
  rw [show j + 2 = 0 + (j + 2) from by ring]
  apply stepStar_trans (r3_drain (j+2) 0 (b'+3*(j+1)) 0)
  simp only [Nat.zero_add]
  ring_nf; finish

-- Main transition for odd d: (0, b'+2j+3, 0, 2j+2, 0) ⊢⁺ (0, b'+4j+7, 0, 2j+5, 0)
theorem main_odd (j b' : ℕ) :
    ⟨0, b'+2*j+3, 0, 2*j+2, 0⟩ [fm]⊢⁺ ⟨0, b'+4*j+7, 0, 2*j+5, 0⟩ := by
  -- Phase 1: R4 chain (2j+2 times): → (0, b'+4j+5, 2j+2, 0, 0)
  rw [show 2 * j + 2 = 0 + (2 * j + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2*j+2) (b'+2*j+3) 0 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5+R1 chain (2j+2 times): → (0, b'+1, 0, 0, 2j+2)
  rw [show b' + 2 * j + 3 + (2 * j + 2) = (b' + 1) + 2 * (2 * j + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain (2*j+2) (b'+1) 0)
  simp only [Nat.zero_add]
  -- R5: (0, b'+1, 0, 0, 2j+2) → (1, b', 0, 0, 2j+3)
  step fm
  -- Phase 3a: odd drain with k=j: (1, b', 0, 0, 2(j+1)+1) → (j+2, b'+3(j+1), 0, 0, 1)
  rw [show 2 * j + 2 + 1 = 2 * (j + 1) + 1 from by ring]
  have h3a := odd_drain j 0 b'
  simp only [Nat.zero_add] at h3a
  apply stepStar_trans h3a
  -- Phase 3b: odd tail: (j+2, b'+3(j+1), 0, 0, 1) → (j+1, b'+3(j+1)+3, 0, 3, 0)
  apply stepStar_trans (odd_tail (j+1) (b'+3*(j+1)))
  -- Phase 4: R3 drain (j+1 times): → (0, b'+3(j+1)+3+j+1, 0, 3+2(j+1), 0)
  have h4 := r3_drain (j+1) 0 (b'+3*(j+1)+3) 3
  simp only [Nat.zero_add] at h4
  apply stepStar_trans h4
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) ⊢* (0,7,0,5,0)
  -- (0,7,0,5,0) = (0, 1+2*2+2, 0, 2*2+1, 0) : even form with j=2, b'=1
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 7, 0, 5, 0⟩) (by execute fm 25)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ j b', q = ⟨0, b'+2*j+2, 0, 2*j+1, 0⟩ ∨
                           q = ⟨0, b'+2*j+3, 0, 2*j+2, 0⟩)
  · intro q ⟨j, b', hq⟩
    rcases hq with hq | hq <;> subst hq
    · -- Even case: (0, b'+2j+2, 0, 2j+1, 0) ⊢⁺ (0, b'+4j+5, 0, 2j+4, 0)
      -- Result: d=2j+4 = 2(j+1)+2, odd form with j'=j+1, b''=b'+2j
      -- Check: b''+2*(j+1)+3 = b'+2j+2j+2+3 = b'+4j+5 ✓
      exact ⟨⟨0, b'+4*j+5, 0, 2*j+4, 0⟩,
             ⟨j+1, b'+2*j, Or.inr (by ring_nf)⟩,
             main_even j b'⟩
    · -- Odd case: (0, b'+2j+3, 0, 2j+2, 0) ⊢⁺ (0, b'+4j+7, 0, 2j+5, 0)
      -- Result: d=2j+5 = 2(j+2)+1, even form with j'=j+2, b''=b'+2j+1
      -- Check: b''+2*(j+2)+2 = b'+2j+1+2j+4+2 = b'+4j+7 ✓
      exact ⟨⟨0, b'+4*j+7, 0, 2*j+5, 0⟩,
             ⟨j+2, b'+2*j+1, Or.inl (by ring_nf)⟩,
             main_odd j b'⟩
  · -- Initial state (0,7,0,5,0): even with j=2, b'=1
    exact ⟨2, 1, Or.inl (by ring_nf)⟩

end Sz22_2003_unofficial_108
