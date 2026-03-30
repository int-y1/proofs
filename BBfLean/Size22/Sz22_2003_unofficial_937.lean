import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #937: [4/15, 33/14, 25/2, 7/11, 42/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_937

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d+1, e⟩
  | _ => none

theorem r2r1_chain : ∀ k, ∀ a c e,
    ⟨a + 1, 0, c + k, k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1)); ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) e); ring_nf; finish

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem main_trans (c d : ℕ) (hc : c ≥ d + 4) :
    ⟨0, 0, c, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, c + d + 6, d + 2, 0⟩ := by
  set c' := c - d - 4 with hc'
  have hc_eq : c = c' + d + 1 + 2 + 1 := by omega
  rw [hc_eq]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, c' + d + 1 + 2 + 1, d + 1, 0⟩ =
        some ⟨1, 1, c' + d + 1 + 2, d + 2, 0⟩
    unfold fm; simp only
  have h1 : ⟨1, 1, c' + d + 1 + 2, d + 2, 0⟩ [fm]⊢*
      ⟨3, 0, c' + d + 1 + 1, d + 2, 0⟩ := by
    rw [show c' + d + 1 + 2 = (c' + d + 1 + 1) + 1 from by ring]
    apply step_stepStar
    show fm ⟨1, 1, (c' + d + 1 + 1) + 1, d + 2, 0⟩ =
        some ⟨3, 0, c' + d + 1 + 1, d + 2, 0⟩
    unfold fm; simp only
  have h2 : ⟨3, 0, c' + d + 1 + 1, d + 2, 0⟩ [fm]⊢*
      ⟨d + 5, 0, c', 0, d + 2⟩ := by
    have := r2r1_chain (d + 2) 2 c' 0
    rw [show c' + (d + 2) = c' + d + 1 + 1 from by ring,
        show 2 + (d + 2) + 1 = d + 5 from by ring,
        show 2 + 1 = 3 from by ring,
        show 0 + (d + 2) = d + 2 from by ring] at this
    exact this
  have h3 : ⟨d + 5, 0, c', 0, d + 2⟩ [fm]⊢*
      ⟨0, 0, c' + 2 * (d + 5), 0, d + 2⟩ := by
    exact r3_drain (d + 5) c' (d + 2)
  have h4 : ⟨0, 0, c' + 2 * (d + 5), 0, d + 2⟩ [fm]⊢*
      ⟨0, 0, c' + 2 * (d + 5), d + 2, 0⟩ := by
    have := r4_drain (d + 2) (c' + 2 * (d + 5)) 0
    rw [show 0 + (d + 2) = d + 2 from by ring] at this
    exact this
  have compose := stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4))
  rw [show c' + 2 * (d + 5) = c' + d + 1 + 2 + 1 + d + 6 from by ring] at compose
  exact compose

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 7, 1, 0⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c, d + 1, 0⟩ ∧ c ≥ d + 4)
  · intro q ⟨c, d, hq, hc⟩
    exact ⟨⟨0, 0, c + d + 6, d + 2, 0⟩,
      ⟨c + d + 6, d + 1, rfl, by omega⟩,
      hq ▸ main_trans c d hc⟩
  · exact ⟨7, 0, rfl, by omega⟩

end Sz22_2003_unofficial_937
