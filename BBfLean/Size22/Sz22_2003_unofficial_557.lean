import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #557: [308/15, 3/7, 1/3, 25/2, 1/55, 3/5]

Vector representation:
```
 2 -1 -1  1  1
 0  1  0 -1  0
 0 -1  0  0  0
-1  0  2  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_557

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1+R2 interleaved chain: (a, 1, c, 0, e) →* (a+2*c, 1, 0, 0, e+c)
theorem r1r2_chain : ⟨a, 1, c, 0, e⟩ [fm]⊢* ⟨a+2*c, 1, 0, 0, e+c⟩ := by
  have many_step : ∀ c a e, ⟨a, 1, c, 0, e⟩ [fm]⊢* ⟨a+2*c, 1, 0, 0, e+c⟩ := by
    intro c; induction' c with c h <;> intro a e
    · exists 0
    rw [show a + 2 * (c + 1) = (a + 2) + 2 * c from by ring]
    rw [show e + (c + 1) = (e + 1) + c from by ring]
    step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step c a e

-- R4 repeated: (a, 0, c, 0, e) →* (0, 0, c+2*a, 0, e)
theorem r4_chain : ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+2*a, 0, e⟩ := by
  have many_step : ∀ a c, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+2*a, 0, e⟩ := by
    intro a; induction' a with a h <;> intro c
    · exists 0
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step a c

-- R5 repeated: (0, 0, c+e, 0, e) →* (0, 0, c, 0, 0)
theorem r5_chain : ⟨0, 0, c+e, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  have many_step : ∀ e c, ⟨0, 0, c+e, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
    intro e; induction' e with e h <;> intro c
    · exists 0
    rw [show c + (e + 1) = (c + e) + 1 from by ring]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step e c

-- R6+R1R2+R3: (0, 0, n+2, 0, 0) →⁺ (2*n+2, 0, 0, 0, n+1)
theorem phase_r6_r1r2_r3 : ⟨0, 0, n+2, 0, 0⟩ [fm]⊢⁺ ⟨2*n+2, 0, 0, 0, n+1⟩ := by
  step fm
  have h := @r1r2_chain 0 (n+1) 0
  rw [show 0 + 2 * (n + 1) = 2 * n + 2 from by ring] at h
  rw [show 0 + (n + 1) = n + 1 from by ring] at h
  apply stepStar_trans h
  step fm; finish

-- Main transition: (0, 0, n+2, 0, 0) →⁺ (0, 0, 3*n+3, 0, 0)
theorem main_trans : ⟨0, 0, n+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3*n+3, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus phase_r6_r1r2_r3
  have h1 := @r4_chain (2*n+2) 0 (n+1)
  rw [show 0 + 2 * (2 * n + 2) = 4 * n + 4 from by ring] at h1
  apply stepStar_trans h1
  have h2 := @r5_chain (3*n+3) (n+1)
  rw [show 3 * n + 3 + (n + 1) = 4 * n + 4 from by ring] at h2
  exact h2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n+2, 0, 0⟩) 0
  intro n; exact ⟨3*n+1, main_trans⟩

end Sz22_2003_unofficial_557
