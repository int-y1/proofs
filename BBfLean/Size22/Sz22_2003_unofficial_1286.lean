import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1286: [56/45, 21/2, 1/147, 375/7]

Vector representation:
```
 3 -2 -1  1
-1  1  0  1
 0 -1  0 -2
 0  1  3 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1286

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d⟩ => some ⟨a+3, b, c, d+1⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+1, c, d+1⟩
  | ⟨a, b+1, c, d+2⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c+3, d⟩
  | _ => none

-- R2 chain: (a+k, b, 0, d) →* (a, b+k, 0, d+k)
theorem r2_chain : ∀ k, ⟨a + k, b, 0, d⟩ [fm]⊢* ⟨a, b + k, 0, d + k⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1) (d := d + 1))
    ring_nf; finish

-- R3 chain: (0, k, 0, d+2*k) →* (0, 0, 0, d)
theorem r3_chain : ∀ k d, ⟨0, k, 0, d + 2 * k⟩ [fm]⊢* ⟨0, 0, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show d + 2 * (k + 1) = 2 * k + d + 2 from by ring]
    step fm
    rw [show 2 * k + d = d + 2 * k from by ring]
    exact ih d

-- R4R3 chain: (0, 0, c, d + 3*k) →* (0, 0, c + 3*k, d)
theorem r4r3_chain : ∀ k c d, ⟨0, 0, c, d + 3 * k⟩ [fm]⊢* ⟨0, 0, c + 3 * k, d⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + 3 * (k + 1) = 3 * k + d + 2 + 1 from by ring]
    step fm
    step fm
    rw [show 3 * k + d = d + 3 * k from by ring]
    apply stepStar_trans (ih (c + 3) d)
    ring_nf; finish

-- Tail: (0, 0, c, 2) →* (3, 0, c+5, 1)
theorem tail : ⟨0, 0, c, 2⟩ [fm]⊢* ⟨3, 0, c + 5, 1⟩ := by
  step fm; step fm; step fm; finish

-- R2R2R1 spiral: (a+2, 0, n, d) →* (a+n+2, 0, 0, d+3*n)
theorem spiral : ∀ n, ⟨a + 2, 0, n, d⟩ [fm]⊢* ⟨a + n + 2, 0, 0, d + 3 * n⟩ := by
  intro n; induction' n with n ih generalizing a d
  · exists 0
  · step fm; step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (d := d + 3))
    ring_nf; finish

-- Combined: R2 + R3 drains a. (a, 0, 0, a+D) →* (0, 0, 0, D)
theorem drain_a (a D : ℕ) : ⟨a, 0, 0, a + D⟩ [fm]⊢* ⟨0, 0, 0, D⟩ := by
  have h1 := r2_chain a (a := 0) (b := 0) (d := a + D)
  simp only [Nat.zero_add] at h1
  -- h1 : (a, 0, 0, a+D) →* (0, a, 0, a+D+a)
  apply stepStar_trans h1
  rw [show a + D + a = D + 2 * a from by ring]
  exact r3_chain a D

-- Main transition: (a, 0, 0, a + (3*k+2)) ⊢⁺ (3*k+8, 0, 0, 9*k+16)
theorem main_trans (a : ℕ) (k : ℕ) :
    ⟨a, 0, 0, a + (3 * k + 2)⟩ [fm]⊢⁺ ⟨3 * k + 8, 0, 0, 9 * k + 16⟩ := by
  -- Phase 1+2: drain a
  have h12 : ⟨a, 0, 0, a + (3 * k + 2)⟩ [fm]⊢* ⟨0, 0, 0, 3 * k + 2⟩ :=
    drain_a a (3 * k + 2)
  -- Phase 3: R4R3 chain
  have h3 : ⟨0, 0, 0, 3 * k + 2⟩ [fm]⊢* ⟨0, 0, 3 * k, 2⟩ := by
    rw [show 3 * k + 2 = 2 + 3 * k from by ring]
    have := r4r3_chain k 0 2
    simp only [Nat.zero_add] at this
    exact this
  -- Phase 4: Tail
  have h4 : ⟨0, 0, 3 * k, 2⟩ [fm]⊢* ⟨3, 0, 3 * k + 5, 1⟩ := tail
  -- Phase 5: Spiral
  have h5 : ⟨3, 0, 3 * k + 5, 1⟩ [fm]⊢* ⟨3 * k + 8, 0, 0, 9 * k + 16⟩ := by
    rw [show (3 : ℕ) = 1 + 2 from by ring]
    apply stepStar_trans (spiral (3 * k + 5) (a := 1) (d := 1))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h12
    (stepStar_stepPlus_stepPlus h3
      (stepStar_stepPlus_stepPlus h4
        (stepStar_stepPlus h5 (by
          intro h
          have := congr_arg Prod.fst h
          simp at this))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 7⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a k, q = ⟨a, 0, 0, a + (3 * k + 2)⟩)
  · intro c ⟨a, k, hq⟩; subst hq
    exact ⟨⟨3 * k + 8, 0, 0, 9 * k + 16⟩,
      ⟨3 * k + 8, 2 * k + 2, by ring_nf⟩, main_trans a k⟩
  · exact ⟨5, 0, by ring_nf⟩
