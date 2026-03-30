import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #987: [4/15, 33/14, 65/2, 7/11, 42/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 1  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_987

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d+1, e, f⟩
  | _ => none

-- R4 chain: drain e into d
theorem r4_chain : ∀ k, ∀ c d f, ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih c (d + 1) f)
    ring_nf; finish

-- R3 chain: a → c, f
theorem r3_chain : ∀ k, ∀ c e f, ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 1) e (f + 1))
    ring_nf; finish

-- R2-R1 interleaved chain:
-- Each round: R2 then R1
-- (a+1, 0, c+k, d+k, e, g) →* (a+1+k, 0, c, d, e+k, g)
theorem r2r1_chain : ∀ k, ∀ a c d e g,
    ⟨a + 1, 0, c + k, d + k, e, g⟩ [fm]⊢* ⟨a + 1 + k, 0, c, d, e + k, g⟩ := by
  intro k; induction' k with k ih <;> intro a c d e g
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm -- R2: (a+1, 0, (c+k)+1, (d+k)+1, e, g) → (a, 1, (c+k)+1, d+k, e+1, g)
    step fm -- R1: (a, 1, (c+k)+1, d+k, e+1, g) → (a+2, 0, c+k, d+k, e+1, g)
    apply stepStar_trans (ih (a + 1) c d (e + 1) g)
    ring_nf; finish

-- Main transition: C(n, g) ⊢⁺ C(n+1, g + n + 4)
-- C(n, g) = (0, 0, 2n+3, 0, n+1, g+1)
-- C(n+1, g+n+4) = (0, 0, 2n+5, 0, n+2, g+n+5)
theorem main_trans (n g : ℕ) :
    ⟨0, 0, 2 * n + 3, 0, n + 1, g + 1⟩ [fm]⊢⁺ ⟨0, 0, 2 * (n + 1) + 3, 0, (n + 1) + 1, g + n + 4 + 1⟩ := by
  -- Phase 1: R4 chain: drain e into d
  have h1 : ⟨0, 0, 2 * n + 3, 0, n + 1, g + 1⟩ [fm]⊢* ⟨0, 0, 2 * n + 3, n + 1, 0, g + 1⟩ := by
    have := r4_chain (n + 1) (2 * n + 3) 0 (g + 1)
    rw [show 0 + (n + 1) = n + 1 from by ring] at this
    exact this
  -- Phase 2: R5 (1 step)
  have h2 : ⟨0, 0, 2 * n + 3, n + 1, 0, g + 1⟩ [fm]⊢⁺ ⟨1, 1, 2 * n + 3, n + 2, 0, g⟩ := by
    rw [show n + 1 = n + 1 from rfl]
    step fm
    ring_nf; finish
  -- Phase 3: R1 (1 step)
  have h3 : ⟨1, 1, 2 * n + 3, n + 2, 0, g⟩ [fm]⊢* ⟨3, 0, 2 * n + 2, n + 2, 0, g⟩ := by
    rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
    step fm
    finish
  -- Phase 4: R2-R1 chain (n+2 rounds)
  have h4 : ⟨3, 0, 2 * n + 2, n + 2, 0, g⟩ [fm]⊢* ⟨n + 5, 0, n, 0, n + 2, g⟩ := by
    have := r2r1_chain (n + 2) 2 n 0 0 g
    simp only [] at this; convert this using 2; all_goals ring_nf
  -- Phase 5: R3 chain (n+5 steps)
  have h5 : ⟨n + 5, 0, n, 0, n + 2, g⟩ [fm]⊢* ⟨0, 0, 2 * n + 5, 0, n + 2, n + 5 + g⟩ := by
    have := r3_chain (n + 5) n (n + 2) g
    simp only [] at this; convert this using 2; all_goals ring_nf
  -- Compose all phases
  show ⟨0, 0, 2 * n + 3, 0, n + 1, g + 1⟩ [fm]⊢⁺ ⟨0, 0, 2 * (n + 1) + 3, 0, (n + 1) + 1, g + n + 4 + 1⟩
  have h5' : ⟨n + 5, 0, n, 0, n + 2, g⟩ [fm]⊢* ⟨0, 0, 2 * (n + 1) + 3, 0, (n + 1) + 1, g + n + 4 + 1⟩ := by
    convert h5 using 2; all_goals ring_nf
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans h4 h5')))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 1, 4⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, g⟩ ↦ ⟨0, 0, 2 * n + 3, 0, n + 1, g + 1⟩) ⟨0, 3⟩
  intro ⟨n, g⟩
  refine ⟨⟨n + 1, g + n + 4⟩, ?_⟩
  exact main_trans n g
