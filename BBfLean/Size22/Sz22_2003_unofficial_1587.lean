import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1587: [7/90, 9/77, 22/3, 5/11, 21/2]

Vector representation:
```
-1 -2 -1  1  0
 0  2  0 -1 -1
 1 -1  0  0  1
 0  0  1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1587

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

private theorem r3_step (a c d : ℕ) :
    ⟨a, 1, c, d, 0⟩ [fm]⊢ ⟨a + 1, 0, c, d, 1⟩ := by simp [fm]

private theorem r3_step' (a k e : ℕ) :
    ⟨a, k + 1, 0, 0, e⟩ [fm]⊢ ⟨a + 1, k, 0, 0, e + 1⟩ := by simp [fm]

private theorem r4_step (a c k : ℕ) :
    ⟨a, 0, c, 0, k + 1⟩ [fm]⊢ ⟨a, 0, c + 1, 0, k⟩ := by simp [fm]

private theorem r5_step (a c d : ℕ) :
    ⟨a + 1, 0, c, d, 0⟩ [fm]⊢ ⟨a, 1, c, d + 1, 0⟩ := by simp [fm]

private theorem r2_step (a c d e : ℕ) :
    ⟨a, 0, c, d + 1, e + 1⟩ [fm]⊢ ⟨a, 2, c, d, e⟩ := by simp [fm]

-- R5R3R2R1 loop: 4 steps per round draining a and c together.
theorem r5r3r2r1_loop : ∀ k, ∀ a c d,
    ⟨a + k, 0, c + k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (step_stepStar (r3_step (a + k) ((c + k) + 1) (d + 1)))
    step fm; step fm
    apply stepStar_trans (ih a c (d + 1))
    ring_nf; finish

-- R3R2 chain: each pair drains d by 1, increases a and b by 1.
theorem r3r2_chain : ∀ k, ∀ a b d,
    ⟨a, b + 1, 0, d + k, 0⟩ [fm]⊢* ⟨a + k, b + k + 1, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (b + 1) d)
    ring_nf; finish

-- R3 drain: moves b into a and e.
theorem r3_drain : ∀ k, ∀ a e,
    ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · apply stepStar_trans (step_stepStar (r3_step' a k e))
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- R4 drain: moves e into c.
theorem r4_drain : ∀ k, ∀ a c,
    ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · apply stepStar_trans (step_stepStar (r4_step a c k))
    apply stepStar_trans (ih a (c + 1))
    ring_nf; finish

-- Canonical states: (n*n+3*n+3, 0, 2*n+2, 0, 0) for n : ℕ.
theorem main_trans (n : ℕ) :
    ⟨n * n + 3 * n + 3, 0, 2 * n + 2, 0, 0⟩ [fm]⊢⁺
    ⟨n * n + 5 * n + 7, 0, 2 * n + 4, 0, 0⟩ := by
  rw [show n * n + 3 * n + 3 = (n * n + n + 1) + (2 * n + 2) from by ring,
      show (2 * n + 2 : ℕ) = 0 + (2 * n + 2) from by ring]
  rw [show (n * n + n + 1) + (0 + (2 * n + 2)) = (n * n + n + 1) + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r3r2r1_loop (2 * n + 2) (n * n + n + 1) 0 0)
  rw [show (0 : ℕ) + (2 * n + 2) = (2 * n + 1) + 1 from by ring,
      show n * n + n + 1 = (n * n + n) + 1 from by ring]
  apply step_stepStar_stepPlus (r5_step (n * n + n) 0 ((2 * n + 1) + 1))
  apply stepStar_trans (step_stepStar (r3_step (n * n + n) 0 ((2 * n + 1) + 1 + 1)))
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (step_stepStar (r2_step (n * n + n + 1) 0 ((2 * n + 1) + 1) 0))
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (2 * n + 1) + 1 = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (r3r2_chain (2 * n + 2) (n * n + n + 1) 1 0)
  apply stepStar_trans (r3_drain (1 + (2 * n + 2) + 1) (n * n + n + 1 + (2 * n + 2)) 0)
  apply stepStar_trans (r4_drain (0 + (1 + (2 * n + 2) + 1))
    (n * n + n + 1 + (2 * n + 2) + (1 + (2 * n + 2) + 1)) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 2, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n * n + 3 * n + 3, 0, 2 * n + 2, 0, 0⟩) 0
  intro n; exists n + 1
  show ⟨n * n + 3 * n + 3, 0, 2 * n + 2, 0, 0⟩ [fm]⊢⁺
    ⟨(n + 1) * (n + 1) + 3 * (n + 1) + 3, 0, 2 * (n + 1) + 2, 0, 0⟩
  rw [show (n + 1) * (n + 1) + 3 * (n + 1) + 3 = n * n + 5 * n + 7 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1587
