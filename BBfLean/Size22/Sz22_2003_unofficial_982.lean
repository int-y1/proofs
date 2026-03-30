import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #982: [4/15, 33/14, 65/2, 7/11, 231/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 0  1  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_982

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e+1, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ c d f, ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih c (d + 1) f)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ c e f, ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 1) e (f + 1))
    ring_nf; finish

theorem r1r2_chain : ∀ k, ∀ a c d e f,
    ⟨a, 1, c + k, d + k, e, f⟩ [fm]⊢* ⟨a + k, 1, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1) f)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a b e f,
    ⟨a + k, b, 0, k, e, f⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a b e f
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (b + 1) (e + 1) f)
    ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ a b e f,
    ⟨a + 1, b + k, 0, 0, e, f⟩ [fm]⊢* ⟨a + 1 + k, b, 0, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e f
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) b e (f + 1))
    ring_nf; finish

theorem main_trans (n f : ℕ) :
    ⟨0, 0, n + 1, 0, 2 * n, f + 1⟩ [fm]⊢⁺ ⟨0, 0, n + 2, 0, 2 * (n + 1), f + 1 + 2 * (n + 1)⟩ := by
  -- Phase 1: R4 chain
  have h1 : ⟨0, 0, n + 1, 0, 2 * n, f + 1⟩ [fm]⊢* ⟨0, 0, n + 1, 2 * n, 0, f + 1⟩ := by
    have := r4_chain (2 * n) (n + 1) 0 (f + 1)
    rw [show 0 + 2 * n = 2 * n from by ring] at this; exact this
  -- Phase 2: R5
  have h2 : ⟨0, 0, n + 1, 2 * n, 0, f + 1⟩ [fm]⊢⁺ ⟨0, 1, n + 1, 2 * n + 1, 1, f⟩ := by
    step fm; finish
  -- Phase 3: R1
  have h3 : ⟨0, 1, n + 1, 2 * n + 1, 1, f⟩ [fm]⊢* ⟨2, 0, n, 2 * n + 1, 1, f⟩ := by
    step fm; finish
  -- Phase 4: R2
  have h4 : ⟨2, 0, n, 2 * n + 1, 1, f⟩ [fm]⊢* ⟨1, 1, n, 2 * n, 2, f⟩ := by
    rw [show 2 * n + 1 = (2 * n) + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
    step fm; ring_nf; finish
  -- Phase 5: R1-R2 chain
  have h5 : ⟨1, 1, n, 2 * n, 2, f⟩ [fm]⊢* ⟨n + 1, 1, 0, n, n + 2, f⟩ := by
    have := r1r2_chain n 1 0 n 2 f
    rw [show 0 + n = n from by ring, show n + n = 2 * n from by ring,
        show 1 + n = n + 1 from by ring, show 2 + n = n + 2 from by ring] at this
    exact this
  -- Phase 6: R2 chain
  have h6 : ⟨n + 1, 1, 0, n, n + 2, f⟩ [fm]⊢* ⟨1, n + 1, 0, 0, 2 * n + 2, f⟩ := by
    have := r2_chain n 1 1 (n + 2) f
    rw [show 1 + n = n + 1 from by ring, show n + 2 + n = 2 * n + 2 from by ring] at this
    exact this
  -- Phase 7: R3
  have h7 : ⟨1, n + 1, 0, 0, 2 * n + 2, f⟩ [fm]⊢* ⟨0, n + 1, 1, 0, 2 * n + 2, f + 1⟩ := by
    step fm; ring_nf; finish
  -- Phase 8: R1
  have h8 : ⟨0, n + 1, 1, 0, 2 * n + 2, f + 1⟩ [fm]⊢* ⟨2, n, 0, 0, 2 * n + 2, f + 1⟩ := by
    step fm; finish
  -- Phase 9: R3-R1 chain
  have h9 : ⟨2, n, 0, 0, 2 * n + 2, f + 1⟩ [fm]⊢* ⟨n + 2, 0, 0, 0, 2 * n + 2, f + 1 + n⟩ := by
    have := r3r1_chain n 1 0 (2 * n + 2) (f + 1)
    rw [show 0 + n = n from by ring, show 1 + 1 = 2 from by ring,
        show 1 + 1 + n = n + 2 from by ring] at this
    exact this
  -- Phase 10: R3 chain
  have h10 : ⟨n + 2, 0, 0, 0, 2 * n + 2, f + 1 + n⟩ [fm]⊢*
      ⟨0, 0, n + 2, 0, 2 * n + 2, f + 1 + n + (n + 2)⟩ := by
    have := r3_chain (n + 2) 0 (2 * n + 2) (f + 1 + n)
    rw [show 0 + (n + 2) = n + 2 from by ring] at this; exact this
  -- Rewrite target
  have heq : f + 1 + n + (n + 2) = f + 1 + 2 * (n + 1) := by ring
  rw [show 2 * (n + 1) = 2 * n + 2 from by ring]
  -- Compose
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans h4
          (stepStar_trans h5
            (stepStar_trans h6
              (stepStar_trans h7
                (stepStar_trans h8
                  (stepStar_trans h9
                    (heq ▸ h10)))))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, n + 1, 0, 2 * n, f + 1⟩) ⟨0, 0⟩
  intro ⟨n, f⟩
  refine ⟨⟨n + 1, f + 2 * (n + 1)⟩, ?_⟩
  show ⟨0, 0, n + 1, 0, 2 * n, f + 1⟩ [fm]⊢⁺ ⟨0, 0, n + 1 + 1, 0, 2 * (n + 1), f + 2 * (n + 1) + 1⟩
  rw [show f + 2 * (n + 1) + 1 = f + 1 + 2 * (n + 1) from by ring,
      show n + 1 + 1 = n + 2 from by ring]
  exact main_trans n f
