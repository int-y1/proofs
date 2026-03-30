import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #872: [4/15, 1/14, 363/2, 7/3, 50/77]

Vector representation:
```
 2 -1 -1  0  0
-1  0  0 -1  0
-1  1  0  0  2
 0 -1  0  1  0
 1  0  2 -1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_872

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

-- R3 chain: drain a to b.
theorem r3_chain : ∀ k, ∀ a b e, ⟨a + k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) (e + 2))
    ring_nf; finish

-- R4 chain: drain b to d.
theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (d + 1) e)
    ring_nf; finish

-- R5+R2 drain: alternating R5 and R2 to drain odd d.
theorem r5r2_drain : ∀ k, ∀ c f, ⟨0, 0, c, 2 * k + 1, f + k + 1⟩ [fm]⊢* ⟨1, 0, c + 2 * (k + 1), 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c f
  · step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
         show f + (k + 1) + 1 = (f + k + 1) + 1 from by ring]
    step fm  -- R5
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm  -- R2
    apply stepStar_trans (ih (c + 2) f)
    ring_nf; finish

-- R3+R1 spiral: interleaved R3 and R1 to drain c and build a.
theorem r3r1_spiral : ∀ m, ∀ a e, ⟨a + 2, 0, m, 0, e⟩ [fm]⊢* ⟨a + m + 2, 0, 0, 0, e + 2 * m⟩ := by
  intro m; induction' m with m ih <;> intro a e
  · exists 0
  · step fm  -- R3
    step fm  -- R1
    apply stepStar_trans (ih (a + 1) (e + 2))
    ring_nf; finish

-- Main transition
theorem main_trans (k e : ℕ) : ⟨2 * k + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨2 * k + 3, 0, 0, 0, e + 7 * k + 5⟩ := by
  -- Phase 1+2: R3 chain then R4 chain
  have h12 : ⟨2 * k + 1, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * k + 1, e + 4 * k + 2⟩ := by
    apply stepStar_trans
    · rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
      exact r3_chain (2 * k + 1) 0 0 e
    rw [show e + 2 * (2 * k + 1) = e + 4 * k + 2 from by ring]
    have := r4_chain (2 * k + 1) 0 0 (e + 4 * k + 2)
    simp only [Nat.zero_add] at this ⊢
    exact this
  -- Phase 3: R5+R2 drain
  have h3 : ⟨0, 0, 0, 2 * k + 1, e + 4 * k + 2⟩ [fm]⊢* ⟨1, 0, 2 * k + 2, 0, e + 3 * k + 1⟩ := by
    rw [show e + 4 * k + 2 = (e + 3 * k + 1) + k + 1 from by ring]
    have := r5r2_drain k 0 (e + 3 * k + 1)
    rw [show 0 + 2 * (k + 1) = 2 * k + 2 from by ring] at this
    exact this
  -- Phase 4+5: R3 step then R1 step
  have h45 : ⟨1, 0, 2 * k + 2, 0, e + 3 * k + 1⟩ [fm]⊢⁺ ⟨2, 0, 2 * k + 1, 0, e + 3 * k + 3⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm  -- R3: (0, 1, 2k+2, 0, e+3k+3)
    step fm  -- R1: (2, 0, 2k+1, 0, e+3k+3)
    ring_nf; finish
  -- Phase 6: R3+R1 spiral
  have h6 : ⟨2, 0, 2 * k + 1, 0, e + 3 * k + 3⟩ [fm]⊢* ⟨2 * k + 3, 0, 0, 0, e + 7 * k + 5⟩ := by
    rw [show (2 : ℕ) = 0 + 2 from by ring]
    apply stepStar_trans (r3r1_spiral (2 * k + 1) 0 (e + 3 * k + 3))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus (stepStar_trans h12 h3) (stepPlus_stepStar_stepPlus h45 h6)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, e⟩ ↦ ⟨2 * k + 1, 0, 0, 0, e⟩) ⟨0, 0⟩
  intro ⟨k, e⟩; exists ⟨k + 1, e + 7 * k + 5⟩
  show ⟨2 * k + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨2 * (k + 1) + 1, 0, 0, 0, e + 7 * k + 5⟩
  rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by ring]
  exact main_trans k e
