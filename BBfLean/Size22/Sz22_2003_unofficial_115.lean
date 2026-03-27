import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #115: [1/30, 9/77, 175/3, 2/7, 363/2]

Vector representation:
```
-1 -1 -1  0  0
 0  2  0 -1 -1
 0 -1  2  1  0
 1  0  0 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_115

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- Phase 1: transfer d to a via rule 4
-- (a, 0, c, k, 0) ⊢* (a + k, 0, c, 0, 0)
theorem d_to_a : ∀ k, ∀ a c, ⟨a, 0, c, k, (0 : ℕ)⟩ [fm]⊢* ⟨a + k, 0, c, (0 : ℕ), 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) c)
    ring_nf; finish

-- Phase 2: drain a via alternating rule5/rule1
-- (a + 2*k + 1, 0, c + k, 0, e) ⊢* (a, 1, c, 0, e + 2*k + 2)
theorem drain_a : ∀ k, ∀ a c e, ⟨a + 2 * k + 1, (0 : ℕ), c + k, (0 : ℕ), e⟩ [fm]⊢* ⟨a, 1, c, (0 : ℕ), e + 2 * k + 2⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · step fm; finish
  · rw [show a + 2 * (k + 1) + 1 = (a + 2 * k + 1) + 2 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a c (e + 2))
    ring_nf; finish

-- Phase 3: interleave rule2/rule3
-- (0, b, c, 1, e + 1) ⊢* (0, b + e + 2, c + 2*e, 0, 0)
theorem interleave : ∀ e, ∀ b c, ⟨(0 : ℕ), b, c, 1, e + 1⟩ [fm]⊢* ⟨(0 : ℕ), b + e + 2, c + 2 * e, (0 : ℕ), 0⟩ := by
  intro e; induction' e with e ih <;> intro b c
  · step fm; finish
  · rw [show (e + 1) + 1 = e + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) (c + 2))
    ring_nf; finish

-- Phase 4: drain b via rule 3
-- (0, b + k, c, d, 0) ⊢* (0, b, c + 2*k, d + k, 0)
theorem b_drain : ∀ k, ∀ b c d, ⟨(0 : ℕ), b + k, c, d, (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 2 * k, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 2) (d + 1))
    ring_nf; finish

-- Main transition: (0, 0, c + n, 2*n + 1, 0) ⊢⁺ (0, 0, c + 8*n + 10, 2*n + 3, 0)
theorem main_trans (n : ℕ) (c : ℕ) :
    ⟨(0 : ℕ), 0, c + n, 2 * n + 1, (0 : ℕ)⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, c + 8 * n + 10, 2 * n + 3, (0 : ℕ)⟩ := by
  -- Phase 1 first step gives us stepPlus
  step fm
  -- Now we need: (1, 0, c+n, 2*n, 0) ⊢* (0, 0, c+8*n+10, 2*n+3, 0)
  -- Phase 1 rest: d_to_a
  have h1 := d_to_a (2 * n) 1 (c + n)
  apply stepStar_trans h1
  rw [show 1 + 2 * n = 2 * n + 1 from by ring]
  -- Phase 2: drain_a
  have h2 := drain_a n 0 c 0
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h2
  -- rule 3: (0, 1, c, 0, 2n+2) -> (0, 0, c+2, 1, 2n+2)
  have hr3 : ⟨(0 : ℕ), 1, c, (0 : ℕ), 2 * n + 2⟩ [fm]⊢ ⟨(0 : ℕ), 0, c + 2, 1, 2 * n + 2⟩ := rfl
  apply stepStar_trans (step_stepStar hr3)
  -- Phase 3: interleave
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  have h3 := interleave (2 * n + 1) 0 (c + 2)
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  -- Phase 4: b_drain
  show ⟨(0 : ℕ), 2 * n + 1 + 2, c + 2 + 2 * (2 * n + 1), (0 : ℕ), 0⟩ [fm]⊢*
       ⟨(0 : ℕ), 0, c + 8 * n + 10, 2 * n + 3, (0 : ℕ)⟩
  rw [show 2 * n + 1 + 2 = 2 * n + 3 from by ring,
      show c + 2 + 2 * (2 * n + 1) = c + 4 * n + 4 from by ring]
  have h4 := b_drain (2 * n + 3) 0 (c + 4 * n + 4) 0
  simp only [Nat.zero_add] at h4
  apply stepStar_trans h4
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 10, 3, 0⟩)
  · execute fm 8
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c n, q = ⟨(0 : ℕ), 0, c + n, 2 * n + 1, (0 : ℕ)⟩ ∧ n ≥ 1)
  · intro q ⟨c, n, hq, hn⟩; subst hq
    exact ⟨⟨0, 0, c + 8 * n + 10, 2 * n + 3, 0⟩,
           ⟨c + 7 * n + 9, n + 1, by ring_nf, by omega⟩,
           main_trans n c⟩
  · exact ⟨9, 1, by ring_nf, by omega⟩

end Sz22_2003_unofficial_115
