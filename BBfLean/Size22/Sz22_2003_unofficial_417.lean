import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #417: [25/63, 847/3, 3/55, 2/11, 9/2]

Vector representation:
```
 0 -2  2 -1  0
 0 -1  0  1  2
 0  1 -1  0 -1
 1  0  0  0 -1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_417

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- Phase 1: interleaved R5+R1 descent
theorem unwind : ∀ k a c, ⟨a+k, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; exists 0
  | succ k ih =>
    intro a c
    show ⟨a + k + 1, 0, c, k + 1, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * (k + 1), 0, 0⟩
    step fm
    step fm
    apply stepStar_trans (ih a (c + 2))
    ring_nf; finish

-- Phase 3: alternating R3+R2 loop
theorem r3r2_loop : ∀ k m d e, ⟨m, 0, k, d, e+1⟩ [fm]⊢* ⟨m, 0, 0, d+k, e+k+1⟩ := by
  intro k; induction k with
  | zero => intro m d e; exists 0
  | succ k ih =>
    intro m d e
    step fm
    step fm
    apply stepStar_trans (ih m (d + 1) (e + 1))
    ring_nf; finish

-- Phase 4: R4 loop converting e to a
theorem r4_loop : ∀ k a d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a+k, 0, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; exists 0
  | succ k ih =>
    intro a d
    step fm
    apply stepStar_trans (ih (a + 1) d)
    ring_nf; finish

-- Main transition: one full cycle
theorem main_trans (m d : ℕ) :
    ⟨m+d+2, 0, 0, d+1, 0⟩ [fm]⊢⁺ ⟨m+2*d+6, 0, 0, 2*d+4, 0⟩ := by
  -- Phase 1: unwind (d+1) steps
  apply stepStar_stepPlus_stepPlus
  · have h := unwind (d+1) (m+1) 0
    simp only [Nat.zero_add] at h
    rw [show m + 1 + (d + 1) = m + d + 2 from by ring,
        show 2 * (d + 1) = 2 * d + 2 from by ring] at h
    exact h
  -- Phase 2: R5, R2, R2
  apply step_stepStar_stepPlus
  · show fm ⟨m + 1, 0, 2 * d + 2, 0, 0⟩ = some ⟨m, 2, 2 * d + 2, 0, 0⟩; rfl
  step fm
  step fm
  -- Phase 3: r3r2_loop
  apply stepStar_trans
  · show ⟨m, 0, 2 * d + 2, 2, 3 + 1⟩ [fm]⊢* ⟨m, 0, 0, 2 + (2 * d + 2), 3 + (2 * d + 2) + 1⟩
    exact r3r2_loop (2 * d + 2) m 2 3
  -- Phase 4: r4_loop
  have h := r4_loop (2 * d + 6) m (2 * d + 4)
  rw [show 2 + (2 * d + 2) = 2 * d + 4 from by ring,
      show 3 + (2 * d + 2) + 1 = 2 * d + 6 from by ring]
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 2, 0⟩) (by execute fm 7)
  refine progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m d, q = (⟨m + d + 2, 0, 0, d + 1, 0⟩ : Q)) ?_ ⟨1, 1, rfl⟩
  intro q ⟨m, d, hq⟩; subst hq
  exact ⟨⟨m + 2 * d + 6, 0, 0, 2 * d + 4, 0⟩,
    ⟨m + 1, 2 * d + 3, by ring_nf⟩, main_trans m d⟩

end Sz22_2003_unofficial_417
