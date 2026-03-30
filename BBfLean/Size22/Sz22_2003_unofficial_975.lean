import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #975: [4/15, 33/14, 65/2, 7/11, 105/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 0  1  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_975

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d+1, e, f⟩
  | _ => none

-- R4 drain: (0, 0, c, d, k, f) ⊢* (0, 0, c, d+k, 0, f)
theorem r4_drain : ∀ k, ∀ c d f,
    ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1) f); ring_nf; finish

-- R3 drain: (k, 0, c, 0, e, f) ⊢* (0, 0, c+k, 0, e, f+k)
theorem r3_drain : ∀ k, ∀ c e f,
    ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 1) e (f + 1)); ring_nf; finish

-- R2/R1 chain: (a+1, 0, c+k, k, e, f) ⊢* (a+1+k, 0, c, 0, e+k, f)
-- Each round: R2 gives (a, 1, c+k, k-1, e+1, f), then R1 gives (a+2, 0, c+k-1, k-1, e+1, f)
theorem r2r1_chain : ∀ k, ∀ a c e f,
    ⟨a + 1, 0, c + k, k, e, f⟩ [fm]⊢* ⟨a + 1 + k, 0, c, 0, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c e f
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1) f); ring_nf; finish

-- Main transition: (0, 0, 2*e+1, 0, e, f+1) ⊢⁺ (0, 0, 2*e+3, 0, e+1, f+e+3)
theorem main_trans (e f : ℕ) :
    ⟨0, 0, 2 * e + 1, 0, e, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 2 * e + 3, 0, e + 1, f + e + 3⟩ := by
  -- Phase 1: R4 drain e→d (e steps)
  have h1 : ⟨0, 0, 2 * e + 1, 0, e, f + 1⟩ [fm]⊢*
      ⟨0, 0, 2 * e + 1, e, 0, f + 1⟩ := by
    have := r4_drain e (2 * e + 1) 0 (f + 1)
    rw [show 0 + e = e from by ring] at this
    exact this
  -- Phase 2: R5 then R1 (2 steps)
  have h2 : ⟨0, 0, 2 * e + 1, e, 0, f + 1⟩ [fm]⊢⁺
      ⟨2, 0, 2 * e + 1, e + 1, 0, f⟩ := by
    rw [show 2 * e + 1 = (2 * e) + 1 from by ring]
    apply step_stepStar_stepPlus
    · show fm ⟨0, 0, (2 * e) + 1, e, 0, f + 1⟩ =
        some ⟨0, 1, (2 * e) + 1 + 1, e + 1, 0, f⟩
      unfold fm; simp only
    · apply step_stepStar
      show fm ⟨0, 1, (2 * e) + 1 + 1, e + 1, 0, f⟩ =
        some ⟨2, 0, (2 * e) + 1, e + 1, 0, f⟩
      unfold fm; simp only
  -- Phase 3: R2/R1 chain (e+1 rounds)
  have h3 : ⟨2, 0, 2 * e + 1, e + 1, 0, f⟩ [fm]⊢*
      ⟨e + 3, 0, e, 0, e + 1, f⟩ := by
    have := r2r1_chain (e + 1) 1 e 0 f
    rw [show 1 + 1 = 2 from rfl,
        show e + (e + 1) = 2 * e + 1 from by ring,
        show 1 + 1 + (e + 1) = e + 3 from by ring,
        show 0 + (e + 1) = e + 1 from by ring] at this
    exact this
  -- Phase 4: R3 drain (e+3 steps)
  have h4 : ⟨e + 3, 0, e, 0, e + 1, f⟩ [fm]⊢*
      ⟨0, 0, 2 * e + 3, 0, e + 1, f + e + 3⟩ := by
    have := r3_drain (e + 3) e (e + 1) f
    rw [show e + (e + 3) = 2 * e + 3 from by ring,
        show f + (e + 3) = f + e + 3 from by ring] at this
    exact this
  -- Compose all phases
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 1, 3⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨e, f⟩ ↦ ⟨0, 0, 2 * e + 1, 0, e, f + 1⟩) ⟨1, 2⟩
  intro ⟨e, f⟩
  refine ⟨⟨e + 1, f + e + 2⟩, ?_⟩
  show ⟨0, 0, 2 * e + 1, 0, e, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 2 * (e + 1) + 1, 0, e + 1, (f + e + 2) + 1⟩
  rw [show 2 * (e + 1) + 1 = 2 * e + 3 from by ring,
      show (f + e + 2) + 1 = f + e + 3 from by ring]
  exact main_trans e f
