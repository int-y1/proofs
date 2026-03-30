import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #936: [4/15, 33/14, 25/2, 7/11, 363/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 0  1 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_936

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

theorem r2r1_chain : ∀ k, ∀ a c e,
    ⟨a + 1, 0, c + k, k, e + 1⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + k + 1⟩ := by
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

theorem main_trans (n c : ℕ) :
    ⟨n + 2, 0, c, 0, n + 2⟩ [fm]⊢⁺ ⟨n + 4, 0, c + n, 0, n + 4⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨n + 2, 0, c, 0, n + 2⟩ = some ⟨n + 1, 0, c + 2, 0, n + 2⟩
    unfold fm; simp only
  have h1 : ⟨n + 1, 0, c + 2, 0, n + 2⟩ [fm]⊢*
      ⟨0, 0, c + 2 * (n + 2), 0, n + 2⟩ := by
    have := r3_drain (n + 1) (c + 2) (n + 2)
    rw [show c + 2 + 2 * (n + 1) = c + 2 * (n + 2) from by ring] at this
    exact this
  have h2 : ⟨0, 0, c + 2 * (n + 2), 0, n + 2⟩ [fm]⊢*
      ⟨0, 0, c + 2 * (n + 2), n + 2, 0⟩ := by
    have := r4_drain (n + 2) (c + 2 * (n + 2)) 0
    rw [show 0 + (n + 2) = n + 2 from by ring] at this
    exact this
  have h3 : ⟨0, 0, c + 2 * (n + 2), n + 2, 0⟩ [fm]⊢*
      ⟨2, 0, c + 2 * n + 2, n + 2, 2⟩ := by
    rw [show c + 2 * (n + 2) = (c + 2 * n + 2) + 1 + 1 from by ring]
    step fm; step fm; finish
  have h4 : ⟨2, 0, c + 2 * n + 2, n + 2, 2⟩ [fm]⊢*
      ⟨n + 4, 0, c + n, 0, n + 4⟩ := by
    have := r2r1_chain (n + 2) 1 (c + n) 1
    rw [show (c + n) + (n + 2) = c + 2 * n + 2 from by ring,
        show 1 + (n + 2) + 1 = n + 4 from by ring,
        show 1 + 1 = 2 from by ring] at this
    exact this
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, c⟩ ↦ ⟨n + 2, 0, c, 0, n + 2⟩) ⟨0, 0⟩
  intro ⟨n, c⟩
  refine ⟨⟨n + 2, c + n⟩, ?_⟩
  show ⟨n + 2, 0, c, 0, n + 2⟩ [fm]⊢⁺ ⟨(n + 2) + 2, 0, c + n, 0, (n + 2) + 2⟩
  rw [show (n + 2) + 2 = n + 4 from by ring]
  exact main_trans n c

end Sz22_2003_unofficial_936
