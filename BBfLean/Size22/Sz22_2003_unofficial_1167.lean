import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1167: [5/6, 44/35, 91/2, 39/11, 15/13]

Vector representation:
```
-1 -1  1  0  0  0
 2  0 -1 -1  1  0
-1  0  0  1  0  1
 0  1  0  0 -1  1
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1167

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R3 repeated: drain a. (a+k, 0, 0, d, e, f) →* (a, 0, 0, d+k, e, f+k)
theorem a_drain : ∀ k d f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d f
  · exists 0
  · rw [Nat.add_succ a k]; step fm
    apply stepStar_trans (ih (d + 1) (f + 1))
    ring_nf; finish

-- R4 repeated: drain e. (0, b, 0, d, e+k, f) →* (0, b+k, 0, d, e, f+k)
theorem e_drain : ∀ k b f, ⟨0, b, 0, d, e + k, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b f
  · exists 0
  · rw [Nat.add_succ e k]; step fm
    apply stepStar_trans (ih (b + 1) (f + 1))
    ring_nf; finish

-- Interleaved R2+R1+R1 loop.
-- (0, b+2k, c+1, d+k, e, f) →* (0, b, c+k+1, d, e+k, f)
theorem interleaved : ∀ k c d e, ⟨0, b + 2 * k, c + 1, d + k, e, f⟩ [fm]⊢*
    ⟨0, b, c + k + 1, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show (b + 2) + 2 * k = (b + 1 + 2 * k) + 1 from by ring]
    step fm
    rw [show b + 1 + 2 * k = (b + 2 * k) + 1 from by ring]
    step fm
    show ⟨0, b + 2 * k, c + 1 + 1, d + k, e + 1, f⟩ [fm]⊢*
        ⟨0, b, c + (k + 1) + 1, d, e + (k + 1), f⟩
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- R2+R3 alternating chain.
-- (a, 0, k+1, 1, e, f) →* (a+k+2, 0, 0, 0, e+k+1, f+k)
theorem r2r3_chain : ∀ k a e f, ⟨a, 0, k + 1, 1, e, f⟩ [fm]⊢*
    ⟨a + k + 2, 0, 0, 0, e + k + 1, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · step fm; finish
  · rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) (e + 1) (f + 1))
    ring_nf; finish

-- Main transition: (n+2, 0, 0, 0, 2n+2, (n+1)*(2n+1)) →⁺ (n+3, 0, 0, 0, 2n+4, (n+2)*(2n+3))
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 0, 2 * n + 2, (n + 1) * (2 * n + 1)⟩ [fm]⊢⁺
    ⟨n + 3, 0, 0, 0, 2 * n + 4, (n + 2) * (2 * n + 3)⟩ := by
  -- Phase 1: R3 x (n+2). Drain a.
  have h1 := a_drain (n + 2) 0 ((n + 1) * (2 * n + 1)) (a := 0) (e := 2 * n + 2)
  simp only [Nat.zero_add] at h1
  -- Phase 2: R4 x (2n+2). Drain e.
  have h2 := e_drain (2 * n + 2) 0 ((n + 1) * (2 * n + 1) + (n + 2)) (d := n + 2) (e := 0)
  simp only [Nat.zero_add] at h2
  -- Phase 3: R5.
  have h3 : fm ⟨0, 2 * n + 2, 0, n + 2, 0, (2 * n ^ 2 + 6 * n + 4) + 1⟩ =
      some ⟨0, 2 * n + 3, 1, n + 2, 0, 2 * n ^ 2 + 6 * n + 4⟩ := by simp [fm]
  have h23 : ⟨0, 2 * n + 2, 0, n + 2, 0,
      (n + 1) * (2 * n + 1) + (n + 2) + (2 * n + 2)⟩ [fm]⊢
      ⟨0, 2 * n + 3, 1, n + 2, 0, 2 * n ^ 2 + 6 * n + 4⟩ := by
    rw [show (n + 1) * (2 * n + 1) + (n + 2) + (2 * n + 2) =
        (2 * n ^ 2 + 6 * n + 4) + 1 from by ring]; exact h3
  -- Phase 4: Interleaved.
  have h4 : ⟨0, 2 * n + 3, 1, n + 2, 0, 2 * n ^ 2 + 6 * n + 4⟩ [fm]⊢*
      ⟨0, 1, n + 2, 1, n + 1, 2 * n ^ 2 + 6 * n + 4⟩ := by
    have := interleaved (n + 1) 0 1 0 (b := 1) (f := 2 * n ^ 2 + 6 * n + 4)
    simp only [Nat.zero_add] at this
    rw [show (1 + (n + 1) : ℕ) = n + 2 from by ring,
        show (n + 1 + 1 : ℕ) = n + 2 from by ring,
        show 1 + 2 * (n + 1) = 2 * n + 3 from by ring] at this
    exact this
  -- Phase 4b+5+6
  have h456 : ⟨0, 1, n + 2, 1, n + 1, 2 * n ^ 2 + 6 * n + 4⟩ [fm]⊢⁺
      ⟨n + 3, 0, 0, 0, 2 * n + 4, (n + 2) * (2 * n + 3)⟩ := by
    step fm; step fm; step fm
    have h6 := r2r3_chain (n + 1) 0 (n + 2) (2 * n ^ 2 + 6 * n + 4 + 1)
    simp only [Nat.zero_add] at h6
    apply stepStar_trans h6; ring_nf; finish
  exact stepStar_stepPlus_stepPlus
    (stepStar_trans h1 (stepStar_trans h2 (stepStar_trans (step_stepStar h23) h4))) h456

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2, 1⟩)
  · execute fm 6
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * n + 2, (n + 1) * (2 * n + 1)⟩) 0
  intro n; exists (n + 1); exact main_trans n
