import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #948: [4/15, 33/14, 275/2, 7/11, 3/7]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_948

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r2r1_chain : ∀ k, ∀ a c e,
    ⟨a + 1, 0, c + k, k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1)); ring_nf; finish

theorem r3_chain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) (e + 1)); ring_nf; finish

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem main_trans (c d : ℕ) :
    ⟨0, 0, c + d + 1, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * d + 4, 2 * d + 2, 0⟩ := by
  have h1 : ⟨0, 0, (c + d) + 1, d + 1, 0⟩ [fm]⊢ ⟨0, 1, (c + d) + 1, d, 0⟩ := by
    show fm ⟨0, 0, (c + d) + 1, d + 1, 0⟩ = some ⟨0, 1, (c + d) + 1, d, 0⟩
    unfold fm; simp only
  have h2 : ⟨0, 1, (c + d) + 1, d, 0⟩ [fm]⊢ ⟨2, 0, c + d, d, 0⟩ := by
    show fm ⟨0, 1, (c + d) + 1, d, 0⟩ = some ⟨2, 0, c + d, d, 0⟩
    unfold fm; simp only
  have h3 : ⟨2, 0, c + d, d, 0⟩ [fm]⊢* ⟨d + 2, 0, c, 0, d⟩ := by
    have h := r2r1_chain d 1 c 0
    rw [show 1 + d + 1 = d + 2 from by ring,
        show 0 + d = d from by ring] at h
    exact h
  have h4 : ⟨d + 2, 0, c, 0, d⟩ [fm]⊢* ⟨0, 0, c + 2 * d + 4, 0, 2 * d + 2⟩ := by
    have h := r3_chain (d + 2) c d
    rw [show c + 2 * (d + 2) = c + 2 * d + 4 from by ring,
        show d + (d + 2) = 2 * d + 2 from by ring] at h
    exact h
  have h5 : ⟨0, 0, c + 2 * d + 4, 0, 2 * d + 2⟩ [fm]⊢* ⟨0, 0, c + 2 * d + 4, 2 * d + 2, 0⟩ := by
    have h := r4_drain (2 * d + 2) (c + 2 * d + 4) 0
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus h1
  apply stepStar_trans (step_stepStar h2)
  apply stepStar_trans h3
  apply stepStar_trans h4
  exact h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, d⟩ ↦ ⟨0, 0, c + d + 1, d + 1, 0⟩) ⟨1, 0⟩
  intro ⟨c, d⟩
  refine ⟨⟨c + 2, 2 * d + 1⟩, ?_⟩
  show ⟨0, 0, c + d + 1, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, (c + 2) + (2 * d + 1) + 1, (2 * d + 1) + 1, 0⟩
  rw [show (c + 2) + (2 * d + 1) + 1 = c + 2 * d + 4 from by ring,
      show (2 * d + 1) + 1 = 2 * d + 2 from by ring]
  exact main_trans c d

end Sz22_2003_unofficial_948
