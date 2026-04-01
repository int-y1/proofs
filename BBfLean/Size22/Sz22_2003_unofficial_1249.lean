import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1249: [5/6, 77/2, 52/35, 3/13, 325/11]

Vector representation:
```
-1 -1  1  0  0  0
-1  0  0  1  1  0
 2  0 -1 -1  0  1
 0  1  0  0  0 -1
 0  0  2  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1249

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+2, d, e, f+1⟩
  | _ => none

-- R4 drain: transfer f to b.
theorem r4_drain : ∀ k, ∀ b d e f,
    ⟨(0 : ℕ), b, 0, d, e, f + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · ring_nf; finish
  · rw [show f + (k + 1) = f + k + 1 from by ring,
        show b + (k + 1) = (b + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

-- R3R1R1 chain (even b): each round consumes 2 from b, 1 from d, adds 1 to c and f.
theorem r3r1r1_chain : ∀ k, ∀ c d e f,
    ⟨(0 : ℕ), 2 * k, c + 1, d + k, e, f⟩ [fm]⊢*
    ⟨0, 0, c + k + 1, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · ring_nf; finish
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show c + (k + 1) + 1 = (c + 1) + k + 1 from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) d e (f + 1))
    ring_nf; finish

-- R3R1R1 chain for odd b: k rounds of R3R1R1 then one R3R1R2.
theorem r3r1r1_odd_chain : ∀ k, ∀ c d e f,
    ⟨(0 : ℕ), 2 * k + 1, c + 1, d + k + 1, e, f⟩ [fm]⊢*
    ⟨0, 0, c + k + 1, d + 1, e + 1, f + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · rw [show d + 0 + 1 = d + 1 from by ring]
    step fm; step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring,
        show d + (k + 1) + 1 = (d + k + 1) + 1 from by ring,
        show c + (k + 1) + 1 = (c + 1) + k + 1 from by ring,
        show f + (k + 1) + 1 = (f + 1) + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) d e (f + 1))
    ring_nf; finish

-- R3R2R2 chain: each round consumes 1 from c, adds 1 to d and f, adds 2 to e.
theorem r3r2r2_chain : ∀ k, ∀ c d e f,
    ⟨(0 : ℕ), 0, c + k, d + 1, e, f⟩ [fm]⊢*
    ⟨0, 0, c, d + k + 1, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) + 1 = (d + 1) + (k + 1) from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih c (d + 1) (e + 2) (f + 1))
    ring_nf; finish

-- Even case: n = 2*m, so f = 6*m (even), d = 4*m+1.
theorem main_even (m e : ℕ) :
    ⟨(0 : ℕ), 0, 0, 4 * m + 1, e + 1, 6 * m⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + 3, e + 6 * m + 4, 6 * m + 3⟩ := by
  -- Phase 1: R4 drain (6m steps).
  have h1 : ⟨(0 : ℕ), 0, 0, 4 * m + 1, e + 1, 6 * m⟩ [fm]⊢*
      ⟨0, 6 * m, 0, 4 * m + 1, e + 1, 0⟩ := by
    have := r4_drain (6 * m) 0 (4 * m + 1) (e + 1) 0
    convert this using 2; ring_nf
  -- Phase 2: R5 step.
  have h2 : ⟨(0 : ℕ), 6 * m, 0, 4 * m + 1, e + 1, 0⟩ [fm]⊢⁺
      ⟨0, 6 * m, 2, 4 * m + 1, e, 1⟩ := by
    step fm; finish
  -- Phase 3: R3R1R1 chain (3m rounds).
  have h3 : ⟨(0 : ℕ), 6 * m, 2, 4 * m + 1, e, 1⟩ [fm]⊢*
      ⟨0, 0, 3 * m + 2, m + 1, e, 3 * m + 1⟩ := by
    have := r3r1r1_chain (3 * m) 1 (m + 1) e 1
    convert this using 2; ring_nf
  -- Phase 4: R3R2R2 chain (3m+2 rounds).
  have h4 : ⟨(0 : ℕ), 0, 3 * m + 2, m + 1, e, 3 * m + 1⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * m + 3, e + 6 * m + 4, 6 * m + 3⟩ := by
    have := r3r2r2_chain (3 * m + 2) 0 m e (3 * m + 1)
    convert this using 2; ring_nf
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 h4))

-- Odd case: n = 2*m+1, so f = 6*m+3 (odd), d = 4*m+3.
theorem main_odd (m e : ℕ) :
    ⟨(0 : ℕ), 0, 0, 4 * m + 3, e + 1, 6 * m + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + 5, e + 6 * m + 7, 6 * m + 6⟩ := by
  -- Phase 1: R4 drain (6m+3 steps).
  have h1 : ⟨(0 : ℕ), 0, 0, 4 * m + 3, e + 1, 6 * m + 3⟩ [fm]⊢*
      ⟨0, 6 * m + 3, 0, 4 * m + 3, e + 1, 0⟩ := by
    have := r4_drain (6 * m + 3) 0 (4 * m + 3) (e + 1) 0
    convert this using 2; ring_nf
  -- Phase 2: R5 step.
  have h2 : ⟨(0 : ℕ), 6 * m + 3, 0, 4 * m + 3, e + 1, 0⟩ [fm]⊢⁺
      ⟨0, 6 * m + 3, 2, 4 * m + 3, e, 1⟩ := by
    step fm; finish
  -- Phase 3: R3R1R1 odd chain (3m+1 full rounds + R3R1R2 tail).
  have h3 : ⟨(0 : ℕ), 6 * m + 3, 2, 4 * m + 3, e, 1⟩ [fm]⊢*
      ⟨0, 0, 3 * m + 3, m + 2, e + 1, 3 * m + 3⟩ := by
    have := r3r1r1_odd_chain (3 * m + 1) 1 (m + 1) e 1
    convert this using 2; ring_nf
  -- Phase 4: R3R2R2 chain (3m+3 rounds).
  have h4 : ⟨(0 : ℕ), 0, 3 * m + 3, m + 2, e + 1, 3 * m + 3⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * m + 5, e + 6 * m + 7, 6 * m + 6⟩ := by
    have := r3r2r2_chain (3 * m + 3) 0 (m + 1) (e + 1) (3 * m + 3)
    convert this using 2; ring_nf
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 h4))

-- Combined transition.
theorem main_trans (n e : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * n + 1, e + 1, 3 * n⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * n + 3, e + 3 * n + 4, 3 * n + 3⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    convert main_even m e using 2; ring_nf
  · subst hm; convert main_odd m e using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨0, 0, 0, 2 * n + 1, e + 1, 3 * n⟩) ⟨0, 0⟩
  intro ⟨n, e⟩
  exact ⟨⟨n + 1, e + 3 * n + 3⟩, main_trans n e⟩

end Sz22_2003_unofficial_1249
