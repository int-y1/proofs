import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #946: [4/15, 33/14, 275/2, 7/11, 3/35]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 0  1 -1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_946

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c e,
    ⟨a + 1, 0, c + k + 1, k + 1, e⟩ [fm]⊢* ⟨a + k + 2, 0, c, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · rw [show c + 0 + 1 = c + 1 from by ring]
    step fm; step fm; ring_nf; finish
  · rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring,
        show (k : ℕ) + 1 + 1 = (k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1)); ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) (e + 1)); ring_nf; finish

theorem main_trans (c e : ℕ) :
    ⟨0, 0, c + e + 4, 0, e + 2⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * e + 7, 0, 2 * e + 4⟩ := by
  have h1 : ⟨0, 0, c + e + 4, 0, e + 2⟩ [fm]⊢*
      ⟨0, 0, c + e + 4, e + 2, 0⟩ := by
    have h := r4_drain (e + 2) (c + e + 4) 0
    simp only [Nat.zero_add] at h; exact h
  have h2 : ⟨0, 0, c + e + 4, e + 2, 0⟩ [fm]⊢⁺
      ⟨e + 3, 0, c + 1, 0, e + 1⟩ := by
    rw [show c + e + 4 = (c + e + 3) + 1 from by ring,
        show e + 2 = (e + 1) + 1 from by ring]
    apply step_stepStar_stepPlus
    · show fm ⟨0, 0, (c + e + 3) + 1, (e + 1) + 1, 0⟩ =
          some ⟨0, 1, c + e + 3, e + 1, 0⟩
      unfold fm; simp only
    rw [show c + e + 3 = (c + e + 2) + 1 from by ring]
    step fm
    rw [show c + e + 2 = c + e + 1 + 1 from by ring]
    have h := r2r1_chain e 1 (c + 1) 0
    rw [show 1 + e + 2 = e + 3 from by ring,
        show c + 1 + e + 1 = c + e + 1 + 1 from by ring,
        show 0 + e + 1 = e + 1 from by ring] at h
    exact h
  have h3 : ⟨e + 3, 0, c + 1, 0, e + 1⟩ [fm]⊢*
      ⟨0, 0, c + 2 * e + 7, 0, 2 * e + 4⟩ := by
    have h := r3_drain (e + 3) (c + 1) (e + 1)
    rw [show c + 1 + 2 * (e + 3) = c + 2 * e + 7 from by ring,
        show e + 1 + (e + 3) = 2 * e + 4 from by ring] at h
    exact h
  exact stepPlus_stepStar_stepPlus
    (stepStar_stepPlus_stepPlus h1 h2)
    h3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 2⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, e⟩ ↦ ⟨0, 0, c + e + 4, 0, e + 2⟩) ⟨0, 0⟩
  intro ⟨c, e⟩
  refine ⟨⟨c + 1, 2 * e + 2⟩, ?_⟩
  show ⟨0, 0, c + e + 4, 0, e + 2⟩ [fm]⊢⁺ ⟨0, 0, (c + 1) + (2 * e + 2) + 4, 0, (2 * e + 2) + 2⟩
  rw [show (c + 1) + (2 * e + 2) + 4 = c + 2 * e + 7 from by ring,
      show (2 * e + 2) + 2 = 2 * e + 4 from by ring]
  exact main_trans c e
