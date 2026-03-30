import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #763: [35/6, 4/55, 9317/2, 3/7, 2/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  3
 0  1  0 -1  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_763

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 3))
    ring_nf; finish

theorem r4_drain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ c d e, ⟨2, 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, 0, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

-- Phase C: (0, 2*m+1, 0, 0, 4*m+3) →⁺ (2*m+2, 0, 0, 2*m+1, 2*m+1)
theorem phase_c : ⟨0, 2 * m + 1, 0, 0, 4 * m + 3⟩ [fm]⊢⁺ ⟨2 * m + 2, 0, 0, 2 * m + 1, 2 * m + 1⟩ := by
  -- R5: → (1, 2*m+1, 0, 0, 4*m+2)
  rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring]
  step fm
  -- R1: (1, (2*m)+1, 0, 0, 4*m+2) → (0, 2*m, 1, 1, 4*m+2)
  rw [show 2 * m + 1 = 2 * m + 1 from rfl]
  step fm
  -- R2: (0, 2*m, 1, 1, 4*m+2) → (2, 2*m, 0, 1, 4*m+1)
  rw [show 4 * m + 2 = (4 * m + 1) + 1 from by ring]
  step fm
  -- R1+R1+R2 chain: (2, 2*m, 0, 1, 4*m+1) →* (2, 0, m, 2*m+1, 3*m+1)
  rw [show 4 * m + 1 = (3 * m + 1) + m from by ring]
  apply stepStar_trans (r1r1r2_chain m 0 1 (3 * m + 1))
  -- R2 drain: (2, 0, 0+m, 1+2*m, (2*m+1)+m) →* (2+2*m, 0, 0, 2*m+1, 2*m+1)
  rw [show 0 + m = m from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring,
      show 3 * m + 1 = (2 * m + 1) + m from by ring]
  apply stepStar_trans (r2_drain m 2 (2 * m + 1) (2 * m + 1))
  ring_nf; finish

theorem main_transition : ⟨N + 1, 0, 0, N, N⟩ [fm]⊢⁺ ⟨2 * N + 2, 0, 0, 2 * N + 1, 2 * N + 1⟩ := by
  apply stepStar_stepPlus_stepPlus
  · apply stepStar_trans
    · rw [show N + 1 = 0 + (N + 1) from by ring]
      exact r3_drain (N + 1) 0 N N
    · rw [show N + (N + 1) = 0 + (2 * N + 1) from by ring,
          show N + 3 * (N + 1) = 4 * N + 3 from by ring]
      exact r4_drain (2 * N + 1) 0 0 (4 * N + 3)
  · rw [show 0 + (2 * N + 1) = 2 * N + 1 from by ring]
    exact phase_c

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 1⟩)
  · execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun N ↦ ⟨N + 1, 0, 0, N, N⟩) 1
  intro N; exists 2 * N + 1
  exact main_transition

end Sz22_2003_unofficial_763
