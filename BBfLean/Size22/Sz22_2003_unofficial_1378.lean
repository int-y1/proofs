import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1378: [63/10, 5/33, 2/3, 11/7, 441/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  0 -1
 1 -1  0  0  0
 0  0  0 -1  1
-1  2  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1378

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+2, e⟩
  | _ => none

-- R4 chain: move d to e when b=0, c=0.
theorem d_to_e : ∀ k d e, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- R2+R1 chain: each round reduces a by 1, increases b by 1, d by 1, decreases e by 1.
theorem r2r1_chain : ∀ k a b d e, ⟨a + k, b + 1, 0, d, e + k⟩ [fm]⊢* ⟨a, b + k + 1, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (b + 1) (d + 1) e)
    ring_nf; finish

-- R2 drain: move e to c when a=0.
theorem r2_drain : ∀ k b c d, ⟨0, b + k, c, d, k⟩ [fm]⊢* ⟨0, b, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) d)
    ring_nf; finish

-- R3+R1 chain: each round increases b by 1, decreases c by 1, increases d by 1.
theorem r3r1_chain : ∀ k b c d, ⟨0, b + 1, c + k, d, 0⟩ [fm]⊢* ⟨0, b + 1 + k, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) c (d + 1))
    ring_nf; finish

-- R3 chain: move b to a when c=0, e=0.
theorem b_to_a : ∀ k a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) d)
    ring_nf; finish

-- Compose all phases into a single transition.
theorem full_trans (k : ℕ) :
    ⟨k + 1, 0, 0, 2 * k, 0⟩ [fm]⊢⁺ ⟨k + 2, 0, 0, 2 * (k + 1), 0⟩ := by
  -- Phase 1: d_to_e
  have h1 : ⟨k + 1, 0, 0, 2 * k, 0⟩ [fm]⊢* ⟨k + 1, 0, 0, 0, 2 * k⟩ := by
    have := d_to_e (2 * k) 0 0 (a := k + 1)
    simp at this; exact this
  -- Phase 2: R5
  have h2 : fm ⟨k + 1, 0, 0, 0, 2 * k⟩ = some ⟨k, 2, 0, 2, 2 * k⟩ := by simp [fm]
  -- Phase 3: r2r1_chain
  have h3 : ⟨k, 2, 0, 2, 2 * k⟩ [fm]⊢* ⟨0, k + 2, 0, k + 2, k⟩ := by
    have := r2r1_chain k 0 1 2 k
    simp at this; convert this using 2; ring_nf
  -- Phase 4: r2_drain
  have h4 : ⟨0, k + 2, 0, k + 2, k⟩ [fm]⊢* ⟨0, 2, k, k + 2, 0⟩ := by
    have := r2_drain k 2 0 (k + 2)
    simp at this; convert this using 2; ring_nf
  -- Phase 5: r3r1_chain
  have h5 : ⟨0, 2, k, k + 2, 0⟩ [fm]⊢* ⟨0, k + 2, 0, 2 * k + 2, 0⟩ := by
    have := r3r1_chain k 1 0 (k + 2)
    simp at this; convert this using 2; ring_nf
  -- Phase 6: b_to_a
  have h6 : ⟨0, k + 2, 0, 2 * k + 2, 0⟩ [fm]⊢* ⟨k + 2, 0, 0, 2 * k + 2, 0⟩ := by
    have := b_to_a (k + 2) 0 (2 * k + 2)
    simp at this; exact this
  -- Compose
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus (step_stepPlus h2)
      (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 2 * n, 0⟩) 0
  intro n; exact ⟨n + 1, full_trans n⟩
