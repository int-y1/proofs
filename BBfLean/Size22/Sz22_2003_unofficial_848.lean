import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #848: [36/35, 5/22, 49/2, 11/3, 5/7]

Vector representation:
```
 2  2 -1 -1  0
-1  0  1  0 -1
-1  0  0  2  0
 0 -1  0  0  1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_848

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k d, ⟨k, b, 0, d, (0 : ℕ)⟩ [fm]⊢* ⟨0, b, 0, d + 2 * k, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 2))
    ring_nf; finish

theorem r4_chain : ∀ k e, ⟨(0 : ℕ), k, 0, d, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  · step fm
    apply stepStar_trans (ih (e + 1))
    ring_nf; finish

theorem r2_r1_chain : ∀ k a b, ⟨a + 1, b, 0, k, k⟩ [fm]⊢* ⟨a + 1 + k, b + 2 * k, 0, 0, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (a + 1) (b + 2))
    ring_nf; finish

-- Full cycle: (n+2, 2n+2, 0, 0, 0) →⁺ (2n+4, 4n+6, 0, 0, 0)
theorem main_trans (n : ℕ) : ⟨n + 2, 2 * n + 2, 0, 0, (0 : ℕ)⟩ [fm]⊢⁺ ⟨2 * n + 4, 4 * n + 6, 0, 0, (0 : ℕ)⟩ := by
  -- Phase 1: R3 chain (n+2 times): (n+2, 2n+2, 0, 0, 0) →* (0, 2n+2, 0, 2n+4, 0)
  have p1 : ⟨n + 2, 2 * n + 2, 0, 0, (0 : ℕ)⟩ [fm]⊢* ⟨0, 2 * n + 2, 0, 2 * n + 4, (0 : ℕ)⟩ := by
    have h := r3_chain (b := 2 * n + 2) (n + 2) 0
    rw [show 0 + 2 * (n + 2) = 2 * n + 4 from by ring] at h
    exact h
  -- Phase 2: R4 chain (2n+2 times): (0, 2n+2, 0, 2n+4, 0) →* (0, 0, 0, 2n+4, 2n+2)
  have p2 : ⟨(0 : ℕ), 2 * n + 2, 0, 2 * n + 4, (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, 2 * n + 4, 2 * n + 2⟩ := by
    have h := r4_chain (d := 2 * n + 4) (2 * n + 2) 0
    rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring] at h
    exact h
  -- Phase 3: R5+R1: (0, 0, 0, 2n+4, 2n+2) →* (2, 2, 0, 2n+2, 2n+2)
  have p3 : ⟨(0 : ℕ), 0, 0, 2 * n + 4, 2 * n + 2⟩ [fm]⊢* ⟨2, 2, 0, 2 * n + 2, 2 * n + 2⟩ := by
    rw [show 2 * n + 4 = (2 * n + 2) + 1 + 1 from by ring]
    step fm; step fm; finish
  -- Phase 4: R2+R1 chain (2n+2 rounds): (2, 2, 0, 2n+2, 2n+2) →* (2n+4, 4n+6, 0, 0, 0)
  have p4 : ⟨2, 2, 0, 2 * n + 2, 2 * n + 2⟩ [fm]⊢* ⟨2 * n + 4, 4 * n + 6, 0, 0, (0 : ℕ)⟩ := by
    have h := r2_r1_chain (2 * n + 2) 1 2
    rw [show 1 + 1 + (2 * n + 2) = 2 * n + 4 from by ring,
        show 2 + 2 * (2 * n + 2) = 4 * n + 6 from by ring] at h
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    exact h
  exact stepStar_stepPlus_stepPlus p1
    (stepStar_stepPlus_stepPlus p2
      (stepStar_stepPlus_stepPlus p3
        (stepStar_stepPlus p4 (by simp [Q]))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 6, 0, 0, 0⟩)
  · execute fm 13
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 2 * n + 2, 0, 0, 0⟩) 2
  intro n; refine ⟨2 * n + 2, ?_⟩
  have h := main_trans n
  rw [show 2 * n + 2 + 2 = 2 * n + 4 from by ring,
      show 2 * (2 * n + 2) + 2 = 4 * n + 6 from by ring]
  exact h
