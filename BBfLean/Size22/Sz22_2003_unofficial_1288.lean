import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1288: [63/10, 1/231, 2/3, 121/2, 75/11]

Vector representation:
```
-1  2 -1  1  0
 0 -1  0 -1 -1
 1 -1  0  0  0
-1  0  0  0  2
 0  1  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1288

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+2, d, e⟩
  | _ => none

-- R1+R3 interleaved chain: each round does R1 then R3.
-- (1, j, c+k, d, 0) →* (1, j+k, c, d+k, 0)
theorem r1r3_chain : ∀ k, ∀ j c d, ⟨1, j, c + k, d, 0⟩ [fm]⊢* ⟨1, j + k, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro j c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (j + 1) c (d + 1))
    ring_nf; finish

-- R3 chain: (a, k, 0, d, 0) →* (a+k, 0, 0, d, 0)
theorem r3_chain : ∀ k, ∀ a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) d)
    ring_nf; finish

-- R4 chain: (k, 0, 0, d, e) →* (0, 0, 0, d, e+2*k)
theorem r4_chain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 2))
    ring_nf; finish

-- R5+R2 drain: (0, 0, c, d+k, e+2*k) →* (0, 0, c+2*k, d, e)
theorem r5r2_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e + 2 * k⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (c + 2) d e)
    ring_nf; finish

-- Full cycle: (1, 0, n+1, 0, 1) →⁺ (1, 0, 2*(n+1), 0, 1)
theorem main_trans (n : ℕ) : ⟨1, 0, n + 1, 0, 1⟩ [fm]⊢⁺ ⟨1, 0, 2 * (n + 1), 0, 1⟩ := by
  have phase1 : ⟨1, 0, n + 1, 0, 1⟩ [fm]⊢⁺ ⟨1, 0, n, 0, 0⟩ := by
    step fm; step fm; step fm; finish
  have phase2 : ⟨1, 0, n, 0, 0⟩ [fm]⊢* ⟨1, n, 0, n, 0⟩ := by
    have := r1r3_chain n 0 0 0; simp at this; exact this
  have phase3 : ⟨1, n, 0, n, 0⟩ [fm]⊢* ⟨n + 1, 0, 0, n, 0⟩ := by
    have := r3_chain n 1 n; simp [Nat.add_comm] at this; exact this
  have phase4 : ⟨n + 1, 0, 0, n, 0⟩ [fm]⊢* ⟨0, 0, 0, n, 2 * (n + 1)⟩ := by
    have := r4_chain (n + 1) n 0; simp at this; exact this
  have phase5 : ⟨0, 0, 0, n, 2 * (n + 1)⟩ [fm]⊢* ⟨0, 0, 2 * n, 0, 2⟩ := by
    have := r5r2_chain n 0 0 2; simp at this
    rw [show 2 * (n + 1) = 2 + 2 * n from by ring]
    exact this
  have phase6 : ⟨0, 0, 2 * n, 0, 2⟩ [fm]⊢⁺ ⟨1, 0, 2 * (n + 1), 0, 1⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm; step fm
    rw [show 2 * n + 2 = 2 * (n + 1) from by ring]
    finish
  exact stepPlus_trans phase1
    (stepStar_stepPlus_stepPlus phase2
      (stepStar_stepPlus_stepPlus phase3
        (stepStar_stepPlus_stepPlus phase4
          (stepStar_stepPlus_stepPlus phase5 phase6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 2, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, n + 2, 0, 1⟩) 0
  intro n; exists 2 * n + 2
  show ⟨1, 0, n + 2, 0, 1⟩ [fm]⊢⁺ ⟨1, 0, 2 * n + 2 + 2, 0, 1⟩
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show 2 * n + 2 + 2 = 2 * ((n + 1) + 1) from by ring]
  exact main_trans (n + 1)
