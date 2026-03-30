import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1082: [5/6, 196/55, 847/2, 3/7, 5/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1  2 -1
-1  0  0  1  2
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude
-/

namespace Sz22_2003_unofficial_1082

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

private theorem r4_chain : ∀ k, ∀ b e,
    ⟨(0 : ℕ), b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) e

private theorem r3_chain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; exact ih (d + 1) (e + 2)

private theorem r1r1r2_chain : ∀ k, ∀ c d,
    ⟨(2 : ℕ), 2 * k + 1, c, d, k⟩ [fm]⊢* ⟨2, 1, c + k, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm
    rw [show k + 1 = k + 1 from rfl]
    step fm
    exact ih (c + 1) (d + 2)

private theorem drain_phase : ∀ C, ∀ a d,
    ⟨a, (0 : ℕ), C + 1, d, 2⟩ [fm]⊢* ⟨0, 0, 0, d + a + 4 * C + 4, 2 * a + 3 * C + 5⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih; intro a d
  rcases C with _ | C
  · -- C = 0
    step fm
    rw [show d + a + 4 * 0 + 4 = (d + 2) + (a + 2) from by ring,
        show 2 * a + 3 * 0 + 5 = 1 + 2 * (a + 2) from by ring]
    exact r3_chain (a + 2) (d + 2) 1
  · -- C + 1
    rw [show (C + 1 : ℕ) + 1 = (C + 1) + 1 from rfl]
    step fm
    rw [show (C + 1 : ℕ) = C + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    step fm
    rcases C with _ | C'
    · -- C = 0
      rw [show d + a + 4 * (0 + 1) + 4 = (d + 5) + (a + 3) from by ring,
          show 2 * a + 3 * (0 + 1) + 5 = 2 + 2 * (a + 3) from by ring]
      exact r3_chain (a + 3) (d + 5) 2
    · -- C = C' + 1
      have h := ih C' (by omega) (a + 3) (d + 5)
      rw [show d + a + 4 * (C' + 1 + 1) + 4 = (d + 5) + (a + 3) + 4 * C' + 4 from by ring,
          show 2 * a + 3 * (C' + 1 + 1) + 5 = 2 * (a + 3) + 3 * C' + 5 from by ring]
      exact h

private theorem main_trans (E : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * E + 1, E + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * E + 7, 3 * E + 5⟩ := by
  -- Phase 1: R4 chain
  have h1 : ⟨(0 : ℕ), 0, 0, 2 * E + 1, E + 2⟩ [fm]⊢*
      ⟨0, 2 * E + 1, 0, 0, E + 2⟩ := by
    have := r4_chain (2 * E + 1) 0 (E + 2)
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R5
  have h2 : ⟨(0 : ℕ), 2 * E + 1, 0, 0, E + 2⟩ [fm]⊢⁺
      ⟨0, 2 * E + 1, 1, 0, E + 1⟩ := by
    rw [show E + 2 = (E + 1) + 1 from by ring]
    step fm; finish
  -- Phase 3: R2
  have h3 : ⟨(0 : ℕ), 2 * E + 1, 1, 0, E + 1⟩ [fm]⊢⁺
      ⟨2, 2 * E + 1, 0, 2, E⟩ := by
    rw [show E + 1 = E + 1 from rfl]
    step fm; finish
  -- Phase 4: R1R1R2 chain
  have h4 : ⟨(2 : ℕ), 2 * E + 1, 0, 2, E⟩ [fm]⊢*
      ⟨2, 1, E, 2 * E + 2, 0⟩ := by
    have := r1r1r2_chain E 0 2
    rw [show 0 + E = E from by ring,
        show 2 + 2 * E = 2 * E + 2 from by ring] at this
    exact this
  -- Phase 5: R1 + R3
  have h5 : ⟨(2 : ℕ), 1, E, 2 * E + 2, 0⟩ [fm]⊢⁺
      ⟨0, 0, E + 1, 2 * E + 3, 2⟩ := by
    step fm; step fm; finish
  -- Phase 6: drain phase
  have h6 : ⟨(0 : ℕ), 0, E + 1, 2 * E + 3, 2⟩ [fm]⊢*
      ⟨0, 0, 0, 6 * E + 7, 3 * E + 5⟩ := by
    have := drain_phase E 0 (2 * E + 3)
    rw [show (2 * E + 3) + 0 + 4 * E + 4 = 6 * E + 7 from by ring,
        show 2 * 0 + 3 * E + 5 = 3 * E + 5 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_trans h2
      (stepPlus_trans h3
        (stepStar_stepPlus_stepPlus h4
          (stepPlus_stepStar_stepPlus h5 h6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun E ↦ ⟨0, 0, 0, 2 * E + 1, E + 2⟩) 0
  intro E
  exact ⟨3 * E + 3, by
    rw [show 2 * (3 * E + 3) + 1 = 6 * E + 7 from by ring,
        show (3 * E + 3) + 2 = 3 * E + 5 from by ring]
    exact main_trans E⟩

end Sz22_2003_unofficial_1082
