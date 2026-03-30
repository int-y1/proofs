import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #971: [4/15, 33/14, 5/2, 7/11, 726/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 1  1 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_971

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e+2⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 2, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 + k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1)); ring_nf; finish

theorem r2_drain : ∀ k, ∀ a b e,
    ⟨a + k, b, 0, k, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + (k + 1) = (b + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih a (b + 1) (e + 1)); ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ a b e,
    ⟨a + 1, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) b e); ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih (c + 1) e); ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 1, 0, 2 * n⟩ [fm]⊢⁺ ⟨0, 0, n + 2, 0, 2 * n + 2⟩ := by
  rcases n with _ | n
  · execute fm 5
  · have h1 : ⟨0, 0, n + 2, 0, 2 * n + 2⟩ [fm]⊢* ⟨0, 0, n + 2, 2 * n + 2, 0⟩ := by
      have := r4_drain (2 * n + 2) (n + 2) 0
      rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring] at this
      exact this
    have h2 : ⟨0, 0, n + 2, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨1, 1, n + 1, 2 * n + 2, 2⟩ := by
      rw [show n + 2 = (n + 1) + 1 from by ring]
      apply step_stepPlus
      show fm ⟨0, 0, (n + 1) + 1, 2 * n + 2, 0⟩ = some ⟨1, 1, n + 1, 2 * n + 2, 2⟩
      unfold fm; simp only
    have h3 : ⟨1, 1, n + 1, 2 * n + 2, 2⟩ [fm]⊢* ⟨3, 0, n, 2 * n + 2, 2⟩ := by
      rw [show n + 1 = n + 1 from rfl]
      step fm; ring_nf; finish
    have h4 : ⟨3, 0, n, 2 * n + 2, 2⟩ [fm]⊢* ⟨n + 3, 0, 0, n + 2, n + 2⟩ := by
      have := r2r1_chain n 1 0 (n + 2) 2
      rw [show 1 + 2 = 3 from by ring,
          show 0 + n = n from by ring,
          show (n + 2) + n = 2 * n + 2 from by ring,
          show 1 + 2 + n = n + 3 from by ring,
          show 2 + n = n + 2 from by ring] at this
      exact this
    have h5 : ⟨n + 3, 0, 0, n + 2, n + 2⟩ [fm]⊢* ⟨1, n + 2, 0, 0, 2 * n + 4⟩ := by
      have := r2_drain (n + 2) 1 0 (n + 2)
      rw [show 1 + (n + 2) = n + 3 from by ring,
          show 0 + (n + 2) = n + 2 from by ring,
          show (n + 2) + (n + 2) = 2 * n + 4 from by ring] at this
      exact this
    have h6 : ⟨1, n + 2, 0, 0, 2 * n + 4⟩ [fm]⊢* ⟨0, n + 2, 1, 0, 2 * n + 4⟩ := by
      step fm; ring_nf; finish
    have h7 : ⟨0, n + 2, 1, 0, 2 * n + 4⟩ [fm]⊢* ⟨2, n + 1, 0, 0, 2 * n + 4⟩ := by
      rw [show n + 2 = (n + 1) + 1 from by ring]
      step fm; ring_nf; finish
    have h8 : ⟨2, n + 1, 0, 0, 2 * n + 4⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
      have := r3r1_chain (n + 1) 1 0 (2 * n + 4)
      rw [show 1 + 1 = 2 from by ring,
          show 0 + (n + 1) = n + 1 from by ring,
          show 1 + 1 + (n + 1) = n + 3 from by ring] at this
      exact this
    have h9 : ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ [fm]⊢* ⟨0, 0, n + 3, 0, 2 * n + 4⟩ := by
      have := r3_drain (n + 3) 0 (2 * n + 4)
      rw [show 0 + (n + 3) = n + 3 from by ring] at this
      exact this
    exact stepStar_stepPlus_stepPlus h1
      (stepPlus_stepStar_stepPlus h2
        (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5
          (stepStar_trans h6 (stepStar_trans h7 (stepStar_trans h8 h9)))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 1, 0, 2 * n⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨0, 0, n + 1, 0, 2 * n⟩ [fm]⊢⁺ ⟨0, 0, (n + 1) + 1, 0, 2 * (n + 1)⟩
  rw [show (n + 1) + 1 = n + 2 from by ring,
      show 2 * (n + 1) = 2 * n + 2 from by ring]
  exact main_trans n
