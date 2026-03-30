import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #977: [4/15, 33/14, 65/2, 7/11, 14/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_977

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ c e f,
    ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 1) e (f + 1)); ring_nf; finish

theorem r4_drain : ∀ k, ∀ c d f,
    ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1) f); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d e f,
    ⟨a + 1, 0, c + k, d + k, e, f⟩ [fm]⊢* ⟨a + 1 + k, 0, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1) f); ring_nf; finish

theorem main_trans (e f : ℕ) :
    ⟨e + 2, 0, 0, 0, e + 1, f⟩ [fm]⊢⁺
    ⟨e + 3, 0, 0, 0, e + 2, f + e + 1⟩ := by
  -- Phase 1: R3 drain (e+2 steps)
  have h1 : ⟨e + 2, 0, 0, 0, e + 1, f⟩ [fm]⊢*
      ⟨0, 0, e + 2, 0, e + 1, f + e + 2⟩ := by
    have := r3_drain (e + 2) 0 (e + 1) f
    rw [show 0 + (e + 2) = e + 2 from by ring,
        show f + (e + 2) = f + e + 2 from by ring] at this
    exact this
  -- Phase 2: R4 drain (e+1 steps)
  have h2 : ⟨0, 0, e + 2, 0, e + 1, f + e + 2⟩ [fm]⊢*
      ⟨0, 0, e + 2, e + 1, 0, f + e + 2⟩ := by
    have := r4_drain (e + 1) (e + 2) 0 (f + e + 2)
    rw [show 0 + (e + 1) = e + 1 from by ring] at this
    exact this
  -- Phase 3: R5 (1 step)
  have h3 : ⟨0, 0, e + 2, e + 1, 0, f + e + 2⟩ [fm]⊢⁺
      ⟨1, 0, e + 2, e + 2, 0, f + e + 1⟩ := by
    rw [show f + e + 2 = (f + e + 1) + 1 from by ring]
    apply step_stepPlus
    show fm ⟨0, 0, e + 2, e + 1, 0, (f + e + 1) + 1⟩ =
      some ⟨1, 0, e + 2, e + 2, 0, f + e + 1⟩
    unfold fm; simp only
  -- Phase 4: R2/R1 chain (e+2 rounds)
  have h4 : ⟨1, 0, e + 2, e + 2, 0, f + e + 1⟩ [fm]⊢*
      ⟨e + 3, 0, 0, 0, e + 2, f + e + 1⟩ := by
    have := r2r1_chain (e + 2) 0 0 0 0 (f + e + 1)
    rw [show 0 + 1 = 1 from by ring,
        show 0 + (e + 2) = e + 2 from by ring,
        show 1 + (e + 2) = e + 3 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus
      (stepStar_stepPlus_stepPlus h2 h3) h4)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨e, f⟩ ↦ ⟨e + 2, 0, 0, 0, e + 1, f⟩) ⟨0, 0⟩
  intro ⟨e, f⟩
  refine ⟨⟨e + 1, f + e + 1⟩, ?_⟩
  show ⟨e + 2, 0, 0, 0, e + 1, f⟩ [fm]⊢⁺
    ⟨(e + 1) + 2, 0, 0, 0, (e + 1) + 1, (f + e + 1)⟩
  rw [show (e + 1) + 2 = e + 3 from by ring,
      show (e + 1) + 1 = e + 2 from by ring]
  exact main_trans e f
