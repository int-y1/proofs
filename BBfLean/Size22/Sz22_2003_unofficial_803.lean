import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #803: [35/6, 605/2, 4/77, 39/5, 7/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  1  0  2  0
 2  0  0 -1 -1  0
 0  1 -1  0  0  1
 0  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_803

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+2, f⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d+1, e, f⟩
  | _ => none

-- R4 chain: move c to b and f
theorem r4_chain : ∀ k, ∀ b e f, ⟨0, b, k, 0, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e (f + 1))
    ring_nf; finish

-- R1R1(R3R1R1)* chain
theorem r1r1r3_chain : ∀ k, ∀ c d e f,
    ⟨2, 2 + 2 * k, c, d, e + 1 + k, f⟩ [fm]⊢* ⟨0, 0, c + 2 + 2 * k, d + k + 2, e + 1, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · step fm; step fm; ring_nf; finish
  · rw [show 2 + 2 * (k + 1) = (2 + 2 * k) + 1 + 1 from by ring,
        show e + 1 + (k + 1) = (e + 1 + k) + 1 from by ring]
    step fm; step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1 + 1) (d + 1) e f)
    ring_nf; finish

-- R3R2R2 chain
theorem r3r2r2_chain : ∀ k, ∀ c d e f,
    ⟨0, 0, c, d + k, e + 1, f⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e + 3 * k + 1, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + 4 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (c + 2) d (e + 3) f)
    ring_nf; finish

-- Canonical state parameterized by (m, n) with 2*m ≥ 3*n + 2:
--   (0, 0, 2*(m+1), 0, 2*m+n+4, 2*m-(3*n+2))
-- Transition: (m, n) → (2*m+2, n+1)
theorem main_transition (m n : ℕ) (hm : 2 * m ≥ 3 * n + 2) :
    ⟨0, 0, 2 * (m + 1), 0, 2 * m + n + 4, 2 * m - (3 * n + 2)⟩ [fm]⊢⁺
    ⟨0, 0, 4 * m + 6, 0, 4 * m + n + 9, 4 * m - (3 * n + 1)⟩ := by
  -- Phase 1: R4 chain
  have h1 : ⟨0, 0, 2 * (m + 1), 0, 2 * m + n + 4, 2 * m - (3 * n + 2)⟩ [fm]⊢*
      ⟨0, 0 + 2 * (m + 1), 0, 0, 2 * m + n + 4, 2 * m - (3 * n + 2) + 2 * (m + 1)⟩ :=
    r4_chain (2 * (m + 1)) 0 (2 * m + n + 4) (2 * m - (3 * n + 2))
  -- Phase 2: R5 step
  have h2 : ⟨0, 0 + 2 * (m + 1), 0, 0, 2 * m + n + 4,
      2 * m - (3 * n + 2) + 2 * (m + 1)⟩ [fm]⊢
      ⟨0, 0 + 2 * (m + 1), 0, 1, 2 * m + n + 4, 4 * m - (3 * n + 1)⟩ := by
    rw [show 2 * m - (3 * n + 2) + 2 * (m + 1) = (4 * m - (3 * n + 1)) + 1 from by omega]
    simp [fm]
  -- Phase 3: R3 step
  have h3 : ⟨0, 0 + 2 * (m + 1), 0, 1, 2 * m + n + 4, 4 * m - (3 * n + 1)⟩ [fm]⊢
      ⟨2, 0 + 2 * (m + 1), 0, 0, 2 * m + n + 3, 4 * m - (3 * n + 1)⟩ := by
    rw [show 2 * m + n + 4 = (2 * m + n + 3) + 1 from by ring]
    simp [fm]
  -- Phase 4: R1R1R3 chain
  have h4 : ⟨2, 0 + 2 * (m + 1), 0, 0, 2 * m + n + 3, 4 * m - (3 * n + 1)⟩ [fm]⊢*
      ⟨0, 0, 0 + 2 + 2 * m, 0 + m + 2, (m + n + 2) + 1, 4 * m - (3 * n + 1)⟩ := by
    rw [show (0 + 2 * (m + 1) : ℕ) = 2 + 2 * m from by ring,
        show 2 * m + n + 3 = (m + n + 2) + 1 + m from by ring]
    exact r1r1r3_chain m 0 0 (m + n + 2) (4 * m - (3 * n + 1))
  -- Phase 5: R3R2R2 chain
  have h5 : ⟨0, 0, 0 + 2 + 2 * m, 0 + m + 2, (m + n + 2) + 1,
      4 * m - (3 * n + 1)⟩ [fm]⊢*
      ⟨0, 0, 4 * m + 6, 0, 4 * m + n + 9, 4 * m - (3 * n + 1)⟩ := by
    rw [show ((m + n + 2) + 1 : ℕ) = (m + n + 2) + 1 from by ring,
        show (0 + m + 2 : ℕ) = 0 + (m + 2) from by ring]
    have := r3r2r2_chain (m + 2) (0 + 2 + 2 * m) 0 (m + n + 2) (4 * m - (3 * n + 1))
    rw [show 0 + 2 + 2 * m + 2 * (m + 2) = 4 * m + 6 from by ring,
        show (m + n + 2) + 3 * (m + 2) + 1 = 4 * m + n + 9 from by ring] at this
    exact this
  -- Compose: (h1: ⊢*) + (h2: ⊢) gives ⊢⁺, then + (h3: ⊢) + (h4: ⊢*) + (h5: ⊢*) = ⊢⁺
  exact stepPlus_stepStar_stepPlus
    (stepStar_stepPlus_stepPlus h1 (step_stepPlus (stepNat_step h2)))
    (stepStar_trans (step_stepStar h3) (stepStar_trans h4 h5))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 6, 0⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m n, q = ⟨0, 0, 2 * (m + 1), 0, 2 * m + n + 4, 2 * m - (3 * n + 2)⟩ ∧
                          2 * m ≥ 3 * n + 2)
  · intro c ⟨m, n, hq, hm⟩; subst hq
    refine ⟨⟨0, 0, 4 * m + 6, 0, 4 * m + n + 9, 4 * m - (3 * n + 1)⟩,
            ⟨2 * m + 2, n + 1, ?_, ?_⟩, main_transition m n hm⟩
    · have h1 : 4 * m + 6 = 2 * (2 * m + 2 + 1) := by ring
      have h2 : 4 * m + n + 9 = 2 * (2 * m + 2) + (n + 1) + 4 := by ring
      have h3 : 4 * m - (3 * n + 1) = 2 * (2 * m + 2) - (3 * (n + 1) + 2) := by omega
      simp [h1, h2, h3]
    · omega
  · exact ⟨1, 0, rfl, by omega⟩
