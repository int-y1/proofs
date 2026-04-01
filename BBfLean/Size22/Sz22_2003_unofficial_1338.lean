import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1338: [63/10, 2/33, 1573/2, 5/7, 15/13]

Vector representation:
```
-1  2 -1  1  0  0
 1 -1  0  0 -1  0
-1  0  0  0  2  1
 0  0  1 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1338

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- Phase 1: R4 drain d to c.
theorem r4_drain : ∀ k, ∀ c e f,
    ⟨(0 : ℕ), 0, c, k, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e f)
    ring_nf; finish

-- Phase 4: R1R2 chain.
theorem r1r2_chain : ∀ k, ∀ b d f,
    ⟨(1 : ℕ), b, k, d, k, f⟩ [fm]⊢* ⟨1, b + k, 0, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro b d f
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) (d + 1) f)
    ring_nf; finish

-- R3 drain: repeated R3 steps.
theorem r3_drain : ∀ k, ∀ e D f,
    ⟨k, (0 : ℕ), 0, D, e, f⟩ [fm]⊢* ⟨0, 0, 0, D, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro e D f
  · ring_nf; finish
  · rw [show (k + 1 : ℕ) = k + 1 from rfl,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih (e + 2) D (f + 1))
    ring_nf; finish

-- R2R2R3 chain: each round does R2, R2, R3.
theorem r2r2r3_chain : ∀ k, ∀ a b D f,
    ⟨a, b + 2 * k, (0 : ℕ), D, 2, f⟩ [fm]⊢* ⟨a + k, b, 0, D, 2, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a b D f
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show a + (k + 1) = (a + 1) + k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) b D (f + 1))
    ring_nf; finish

-- Even case: d+1 = 2*m, so d = 2*m-1.
theorem main_even (m f : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * m, 2 * m + 2, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 1, 2 * m + 3, f + 2 * m + 2⟩ := by
  -- Phase 1: R4 drain (2m steps).
  have h1 : ⟨(0 : ℕ), 0, 0, 2 * m, 2 * m + 2, f + 1⟩ [fm]⊢*
      ⟨0, 0, 2 * m, 0, 2 * m + 2, f + 1⟩ := by
    have := r4_drain (2 * m) 0 (2 * m + 2) (f + 1)
    convert this using 2; ring_nf
  -- Phase 2: R5 step.
  have h2 : ⟨(0 : ℕ), 0, 2 * m, 0, 2 * m + 2, f + 1⟩ [fm]⊢⁺
      ⟨0, 1, 2 * m + 1, 0, 2 * m + 2, f⟩ := by
    step fm; finish
  -- Phase 3: R2 step.
  have h3 : ⟨(0 : ℕ), 1, 2 * m + 1, 0, 2 * m + 2, f⟩ [fm]⊢*
      ⟨1, 0, 2 * m + 1, 0, 2 * m + 1, f⟩ := by
    step fm; finish
  -- Phase 4: R1R2 chain (2m+1 rounds).
  have h4 : ⟨(1 : ℕ), 0, 2 * m + 1, 0, 2 * m + 1, f⟩ [fm]⊢*
      ⟨1, 2 * m + 1, 0, 2 * m + 1, 0, f⟩ := by
    have := r1r2_chain (2 * m + 1) 0 0 f
    convert this using 2; ring_nf
  -- Phase 5: R3 step.
  have h5 : ⟨(1 : ℕ), 2 * m + 1, 0, 2 * m + 1, 0, f⟩ [fm]⊢*
      ⟨0, 2 * m + 1, 0, 2 * m + 1, 2, f + 1⟩ := by
    step fm; finish
  -- Phase 6a: R2R2R3 chain (m rounds, odd b = 2m+1).
  have h6 : ⟨(0 : ℕ), 2 * m + 1, 0, 2 * m + 1, 2, f + 1⟩ [fm]⊢*
      ⟨m, 1, 0, 2 * m + 1, 2, f + 1 + m⟩ := by
    have := r2r2r3_chain m 0 1 (2 * m + 1) (f + 1)
    convert this using 2; ring_nf
  -- Phase 6b: R2 step.
  have h7 : ⟨m, (1 : ℕ), 0, 2 * m + 1, 2, f + 1 + m⟩ [fm]⊢*
      ⟨m + 1, 0, 0, 2 * m + 1, 1, f + 1 + m⟩ := by
    step fm; finish
  -- Phase 6c: R3 drain (m+1 steps).
  have h8 : ⟨m + 1, (0 : ℕ), 0, 2 * m + 1, 1, f + 1 + m⟩ [fm]⊢*
      ⟨0, 0, 0, 2 * m + 1, 1 + 2 * (m + 1), f + 1 + m + (m + 1)⟩ := by
    exact r3_drain (m + 1) 1 (2 * m + 1) (f + 1 + m)
  -- Compose all phases.
  have h8' : ⟨0, 0, 0, 2 * m + 1, 1 + 2 * (m + 1), f + 1 + m + (m + 1)⟩ =
      (⟨0, 0, 0, 2 * m + 1, 2 * m + 3, f + 2 * m + 2⟩ : Q) := by
    ext <;> simp <;> ring
  rw [h8'] at h8
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans h4
          (stepStar_trans h5
            (stepStar_trans h6
              (stepStar_trans h7 h8))))))

-- Odd case: d+1 = 2*m+2, so d = 2*m+1.
theorem main_odd (m f : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * m + 1, 2 * m + 3, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 2, 2 * m + 4, f + 2 * m + 3⟩ := by
  -- Phase 1: R4 drain (2m+1 steps).
  have h1 : ⟨(0 : ℕ), 0, 0, 2 * m + 1, 2 * m + 3, f + 1⟩ [fm]⊢*
      ⟨0, 0, 2 * m + 1, 0, 2 * m + 3, f + 1⟩ := by
    have := r4_drain (2 * m + 1) 0 (2 * m + 3) (f + 1)
    convert this using 2; ring_nf
  -- Phase 2: R5 step.
  have h2 : ⟨(0 : ℕ), 0, 2 * m + 1, 0, 2 * m + 3, f + 1⟩ [fm]⊢⁺
      ⟨0, 1, 2 * m + 2, 0, 2 * m + 3, f⟩ := by
    step fm; finish
  -- Phase 3: R2 step.
  have h3 : ⟨(0 : ℕ), 1, 2 * m + 2, 0, 2 * m + 3, f⟩ [fm]⊢*
      ⟨1, 0, 2 * m + 2, 0, 2 * m + 2, f⟩ := by
    step fm; finish
  -- Phase 4: R1R2 chain (2m+2 rounds).
  have h4 : ⟨(1 : ℕ), 0, 2 * m + 2, 0, 2 * m + 2, f⟩ [fm]⊢*
      ⟨1, 2 * m + 2, 0, 2 * m + 2, 0, f⟩ := by
    have := r1r2_chain (2 * m + 2) 0 0 f
    convert this using 2; ring_nf
  -- Phase 5: R3 step.
  have h5 : ⟨(1 : ℕ), 2 * m + 2, 0, 2 * m + 2, 0, f⟩ [fm]⊢*
      ⟨0, 2 * m + 2, 0, 2 * m + 2, 2, f + 1⟩ := by
    step fm; finish
  -- Phase 6a: R2R2R3 chain (m+1 rounds, even b = 2*(m+1)).
  have h6 : ⟨(0 : ℕ), 2 * m + 2, 0, 2 * m + 2, 2, f + 1⟩ [fm]⊢*
      ⟨m + 1, 0, 0, 2 * m + 2, 2, f + m + 2⟩ := by
    have := r2r2r3_chain (m + 1) 0 0 (2 * m + 2) (f + 1)
    convert this using 2; ring_nf
  -- Phase 6b: R3 drain (m+1 steps).
  have h7 : ⟨m + 1, (0 : ℕ), 0, 2 * m + 2, 2, f + m + 2⟩ [fm]⊢*
      ⟨0, 0, 0, 2 * m + 2, 2 + 2 * (m + 1), f + m + 2 + (m + 1)⟩ := by
    exact r3_drain (m + 1) 2 (2 * m + 2) (f + m + 2)
  -- Compose.
  have h7' : ⟨0, 0, 0, 2 * m + 2, 2 + 2 * (m + 1), f + m + 2 + (m + 1)⟩ =
      (⟨0, 0, 0, 2 * m + 2, 2 * m + 4, f + 2 * m + 3⟩ : Q) := by
    ext <;> simp <;> ring
  rw [h7'] at h7
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans h4
          (stepStar_trans h5
            (stepStar_trans h6 h7)))))

-- Combined transition.
theorem main_trans (d f : ℕ) :
    ⟨(0 : ℕ), 0, 0, d, d + 2, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, d + 1, d + 3, f + d + 2⟩ := by
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    exact main_even m f
  · subst hm
    exact main_odd m f

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, f⟩ ↦ ⟨0, 0, 0, d, d + 2, f + 1⟩) ⟨0, 0⟩
  intro ⟨d, f⟩
  exact ⟨⟨d + 1, f + d + 1⟩, main_trans d f⟩

end Sz22_2003_unofficial_1338
