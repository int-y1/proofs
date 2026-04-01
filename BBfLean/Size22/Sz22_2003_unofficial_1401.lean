import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1401: [7/15, 1/3, 66/7, 125/2, 1/55, 3/5]

Vector representation:
```
 0 -1 -1  1  0
 0 -1  0  0  0
 1  1  0 -1  1
-1  0  3  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1401

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: drain a, each step adds 3 to c
theorem r4_chain : ∀ k a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c e; exists 0
  · intro a c e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 3) e)
    ring_nf; finish

-- R5 chain: drain c and e together
theorem r5_chain : ∀ k c e, ⟨0, 0, c + k, 0, e + k⟩ [fm]⊢* ⟨0, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c e; exists 0
  · intro c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    exact ih c e

-- R3+R1 interleaved chain: k rounds transferring c to a and e via d
theorem r3r1_chain : ∀ k a c e, ⟨a, 0, c + k, 1, e⟩ [fm]⊢* ⟨a + k, 0, c, 1, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a c e; exists 0
  · intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 1) c (e + 1))
    ring_nf; finish

-- Full drain: (a, 0, 0, 0, a) →* (0, 0, 2a, 0, 0)
theorem drain_phase (a : ℕ) : ⟨a, 0, 0, 0, a⟩ [fm]⊢* ⟨0, 0, 2 * a, 0, 0⟩ := by
  have h1 := r4_chain a 0 0 a
  simp at h1
  apply stepStar_trans h1
  have h2 := r5_chain a (2 * a) 0
  simp at h2
  convert h2 using 1; ring_nf

-- Spiral: (0, 0, C+2, 0, 0) →⁺ (C+1, 0, 0, 0, C+1)
theorem spiral (C : ℕ) :
    ⟨0, 0, C + 2, 0, 0⟩ [fm]⊢⁺ ⟨C + 1, 0, 0, 0, C + 1⟩ := by
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm
  step fm
  have h := r3r1_chain C 0 0 0
  simp at h
  apply stepStar_trans h
  step fm
  step fm
  finish

-- Main transition: (n+2, 0, 0, 0, n+2) ⊢⁺ (2n+3, 0, 0, 0, 2n+3)
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 0, n + 2⟩ [fm]⊢⁺ ⟨2 * n + 3, 0, 0, 0, 2 * n + 3⟩ := by
  apply stepStar_stepPlus_stepPlus (drain_phase (n + 2))
  rw [show 2 * (n + 2) = (2 * n + 2) + 2 from by ring]
  exact spiral (2 * n + 2)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩)
  · execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, n + 2⟩) 0
  intro n; exact ⟨2 * n + 1, main_trans n⟩

end Sz22_2003_unofficial_1401
