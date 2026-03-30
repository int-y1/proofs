import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1022: [4/15, 99/14, 5/2, 7/11, 28/5]

Vector representation:
```
 2 -1 -1  0  0
-1  2  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 2  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1022

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ c d,
    ⟨(0 : ℕ), 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a c e,
    ⟨a + k, (0 : ℕ), c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, (0 : ℕ), c + 2 * k, d + k, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show a + 3 * (k + 1) + 1 = (a + 3) + 3 * k + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) c d (e + 1))
    ring_nf; finish

theorem main_trans (c d : ℕ) (hc : c ≥ 2 * d + 3) :
    ⟨(0 : ℕ), 0, c, d, 0⟩ [fm]⊢⁺ ⟨0, 0, c + d + 2, d + 1, 0⟩ := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 * (d + 1) + 1 := ⟨c - 2 * (d + 1) - 1, by omega⟩
  -- R5: (0, 0, c'+2*(d+1)+1, d, 0) -> (2, 0, c'+2*(d+1), d+1, 0)
  have hR5 : ⟨(0 : ℕ), 0, c' + 2 * (d + 1) + 1, d, 0⟩ [fm]⊢
      ⟨2, 0, c' + 2 * (d + 1), d + 1, 0⟩ := by
    rw [show c' + 2 * (d + 1) + 1 = (c' + 2 * (d + 1)) + 1 from by ring]
    unfold fm; simp only
  -- R2R1R1 chain (d+1 rounds)
  have hchain : ⟨(2 : ℕ), 0, c' + 2 * (d + 1), d + 1, 0⟩ [fm]⊢*
      ⟨3 * (d + 1) + 2, 0, c', 0, d + 1⟩ := by
    have := r2r1r1_chain (d + 1) 1 c' 0 0
    rw [show (1 : ℕ) + 1 = 2 from rfl,
        show 1 + 3 * (d + 1) + 1 = 3 * (d + 1) + 2 from by ring] at this
    simpa using this
  -- R3 chain: drain a into c
  have hR3 : ⟨3 * (d + 1) + 2, (0 : ℕ), c', 0, d + 1⟩ [fm]⊢*
      ⟨0, 0, c' + 3 * (d + 1) + 2, 0, d + 1⟩ := by
    have := r3_chain (3 * (d + 1) + 2) 0 c' (d + 1)
    rw [show (0 : ℕ) + (3 * (d + 1) + 2) = 3 * (d + 1) + 2 from by ring] at this
    exact this
  -- R4 chain: drain e into d
  have hR4 : ⟨(0 : ℕ), 0, c' + 3 * (d + 1) + 2, 0, d + 1⟩ [fm]⊢*
      ⟨0, 0, c' + 3 * (d + 1) + 2, d + 1, 0⟩ := by
    have := r4_chain (d + 1) (c' + 3 * (d + 1) + 2) 0
    rw [show (0 : ℕ) + (d + 1) = d + 1 from by ring] at this
    exact this
  -- Combine: need to show c' + 3*(d+1) + 2 = (c' + 2*(d+1) + 1) + d + 2
  have heq : c' + 3 * (d + 1) + 2 = c' + 2 * (d + 1) + 1 + d + 2 := by ring
  rw [heq] at hR3 hR4
  exact step_stepStar_stepPlus hR5
    (stepStar_trans hchain (stepStar_trans hR3 hR4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 10, 3, 0⟩) (by execute fm 52)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c, d, 0⟩ ∧ c ≥ 2 * d + 3)
  · intro q ⟨c, d, hq, hc⟩
    exact ⟨⟨0, 0, c + d + 2, d + 1, 0⟩,
      ⟨c + d + 2, d + 1, rfl, by omega⟩,
      hq ▸ main_trans c d hc⟩
  · exact ⟨10, 3, rfl, by omega⟩

end Sz22_2003_unofficial_1022
