import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #959: [4/15, 33/14, 325/2, 7/11, 22/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  2  0  0  1
 0  0  0  1 -1  0
 1  0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_959

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | _ => none

-- R4 drain: e into d
theorem r4_drain : ∀ k, ∀ c d f,
    ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1) f); ring_nf; finish

-- R3 drain: a into c (*2) and f
theorem r3_drain : ∀ k, ∀ c e f,
    ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) e (f + 1)); ring_nf; finish

-- R1/R2 interleaved chain
theorem r1r2_chain : ∀ d, ∀ a c e f,
    ⟨a, 1, c + d + 1, d, e, f⟩ [fm]⊢* ⟨a + d, 1, c + 1, 0, e + d, f⟩ := by
  intro d; induction' d with d ih <;> intro a c e f
  · ring_nf; finish
  · rw [show c + (d + 1) + 1 = (c + d + 1) + 1 from by ring,
        show (d : ℕ) + 1 = d + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1) f); ring_nf; finish

-- Main transition for e >= 1 (using e+1 to ensure this)
-- Canonical: (0, 0, g+2*e+4, 0, e+1, g+1)
-- Next:      (0, 0, g+3*e+7, 0, e+2, g+e+2)
theorem main_trans (e g : ℕ) :
    ⟨0, 0, g + 2 * e + 4, 0, e + 1, g + 1⟩ [fm]⊢⁺ ⟨0, 0, g + 3 * e + 7, 0, e + 2, g + e + 2⟩ := by
  -- Phase 1: R4 drain (e+1 steps)
  have h1 : ⟨0, 0, g + 2 * e + 4, 0, e + 1, g + 1⟩ [fm]⊢*
      ⟨0, 0, g + 2 * e + 4, e + 1, 0, g + 1⟩ := by
    have := r4_drain (e + 1) (g + 2 * e + 4) 0 (g + 1)
    rw [show 0 + (e + 1) = e + 1 from by ring] at this
    exact this
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2: R5 kick (1 step)
  have h2 : ⟨0, 0, g + 2 * e + 4, e + 1, 0, g + 1⟩ [fm]⊢⁺
      ⟨1, 0, g + 2 * e + 4, e + 1, 1, g⟩ := by
    apply step_stepPlus
    show fm ⟨0, 0, g + 2 * e + 4, e + 1, 0, g + 1⟩ = some ⟨1, 0, g + 2 * e + 4, e + 1, 1, g⟩
    unfold fm; simp only
  -- Phase 3: R2 kick (1 step)
  have h3 : ⟨1, 0, g + 2 * e + 4, e + 1, 1, g⟩ [fm]⊢*
      ⟨0, 1, g + 2 * e + 4, e, 2, g⟩ := by
    rw [show e + 1 = e + 1 from rfl]
    apply step_stepStar
    show fm ⟨1, 0, g + 2 * e + 4, e + 1, 1, g⟩ = some ⟨0, 1, g + 2 * e + 4, e, 2, g⟩
    unfold fm; simp only
  -- Phase 4: R1/R2 chain (e rounds)
  have h4 : ⟨0, 1, g + 2 * e + 4, e, 2, g⟩ [fm]⊢*
      ⟨e, 1, g + e + 4, 0, e + 2, g⟩ := by
    have := r1r2_chain e 0 (g + e + 3) 2 g
    rw [show (g + e + 3) + e + 1 = g + 2 * e + 4 from by ring,
        show 0 + e = e from by ring,
        show 2 + e = e + 2 from by ring,
        show (g + e + 3) + 1 = g + e + 4 from by ring] at this
    exact this
  -- Phase 5: Last R1 (1 step)
  have h5 : ⟨e, 1, g + e + 4, 0, e + 2, g⟩ [fm]⊢*
      ⟨e + 2, 0, g + e + 3, 0, e + 2, g⟩ := by
    rw [show g + e + 4 = (g + e + 3) + 1 from by ring]
    apply step_stepStar
    show fm ⟨e, 1, (g + e + 3) + 1, 0, e + 2, g⟩ = some ⟨e + 2, 0, g + e + 3, 0, e + 2, g⟩
    unfold fm; simp only
  -- Phase 6: R3 drain (e+2 steps)
  have h6 : ⟨e + 2, 0, g + e + 3, 0, e + 2, g⟩ [fm]⊢*
      ⟨0, 0, g + 3 * e + 7, 0, e + 2, g + e + 2⟩ := by
    have := r3_drain (e + 2) (g + e + 3) (e + 2) g
    rw [show (g + e + 3) + 2 * (e + 2) = g + 3 * e + 7 from by ring,
        show g + (e + 2) = g + e + 2 from by ring] at this
    exact this
  -- Compose all phases
  exact stepPlus_stepStar_stepPlus h2
    (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 1, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨e, g⟩ ↦ ⟨0, 0, g + 2 * e + 4, 0, e + 1, g + 1⟩) ⟨0, 0⟩
  intro ⟨e, g⟩
  refine ⟨⟨e + 1, g + e + 1⟩, ?_⟩
  show ⟨0, 0, g + 2 * e + 4, 0, e + 1, g + 1⟩ [fm]⊢⁺
    ⟨0, 0, (g + e + 1) + 2 * (e + 1) + 4, 0, (e + 1) + 1, (g + e + 1) + 1⟩
  rw [show (g + e + 1) + 2 * (e + 1) + 4 = g + 3 * e + 7 from by ring,
      show (e + 1) + 1 = e + 2 from by ring,
      show (g + e + 1) + 1 = g + e + 2 from by ring]
  exact main_trans e g

end Sz22_2003_unofficial_959
