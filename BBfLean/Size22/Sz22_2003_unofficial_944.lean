import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #944: [4/15, 33/14, 275/2, 7/11, 2/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 1  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_944

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
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

theorem main_trans (n : ℕ) :
    ⟨1, 0, n, n, 0⟩ [fm]⊢⁺ ⟨1, 0, 2 * n + 1, 2 * n + 1, 0⟩ := by
  have h1 : ⟨1, 0, n, n, 0⟩ [fm]⊢* ⟨n + 1, 0, 0, 0, n⟩ := by
    have h := r2r1_chain n 0 0 0
    simp only [Nat.zero_add] at h; exact h
  have h2 : ⟨n + 1, 0, 0, 0, n⟩ [fm]⊢* ⟨0, 0, 2 * (n + 1), 0, 2 * n + 1⟩ := by
    have h := r3_chain (n + 1) 0 n
    rw [show 0 + 2 * (n + 1) = 2 * (n + 1) from by ring,
        show n + (n + 1) = 2 * n + 1 from by ring] at h
    exact h
  have h3 : ⟨0, 0, 2 * (n + 1), 0, 2 * n + 1⟩ [fm]⊢* ⟨0, 0, 2 * (n + 1), 2 * n + 1, 0⟩ := by
    have h := r4_drain (2 * n + 1) (2 * (n + 1)) 0
    simp only [Nat.zero_add] at h; exact h
  have h4 : ⟨0, 0, 2 * (n + 1), 2 * n + 1, 0⟩ [fm]⊢* ⟨1, 0, 2 * n + 1, 2 * n + 1, 0⟩ := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
    step fm; finish
  apply stepStar_stepPlus_stepPlus h1
  apply stepStar_stepPlus_stepPlus h2
  apply stepStar_stepPlus_stepPlus h3
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (2 * n + 1) + 1, 2 * n + 1, 0⟩ = some ⟨1, 0, 2 * n + 1, 2 * n + 1, 0⟩
    unfold fm; simp only
  · finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 1, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, n, n, 0⟩) 1
  intro n
  refine ⟨2 * n + 1, ?_⟩
  exact main_trans n

end Sz22_2003_unofficial_944
