import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #693: [35/6, 4/55, 11/2, 3/7, 70/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 1  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_693

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d+1, e⟩
  | _ => none

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ m c d e,
    ⟨0, m + 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, m, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro m c d e
  · exists 0
  · rw [show m + 2 * (k + 1) = (m + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih m (c + 1) (d + 2) e)
    ring_nf; finish

theorem phase_even (j : ℕ) :
    ⟨0, 2 * j, 2, 2, 2 * j + 1⟩ [fm]⊢* ⟨0, 2 * j + 2, 0, 0, 2 * j + 3⟩ := by
  have h1 := r2r1r1_chain j 0 1 2 (j + 1)
  have h2 := r2_chain (j + 1) 0 1 (2 * j + 2) 0
  have h3 := r3_chain (2 * j + 3) 0 (2 * j + 2) 0
  have h4 := r4_chain (2 * j + 2) 0 0 (2 * j + 3)
  apply stepStar_trans
  show ⟨0, 2 * j, 2, 2, 2 * j + 1⟩ [fm]⊢* ⟨0, 0, j + 2, 2 * j + 2, j + 1⟩
  · convert h1 using 3 <;> ring_nf
  apply stepStar_trans
  show ⟨0, 0, j + 2, 2 * j + 2, j + 1⟩ [fm]⊢* ⟨2 * j + 2, 0, 1, 2 * j + 2, 0⟩
  · convert h2 using 3 <;> ring_nf
  rw [show 2 * j + 2 = (2 * j + 1) + 1 from by ring]
  step fm
  rw [show 2 * j + 1 + 1 = (2 * j) + 1 + 1 from by ring]
  step fm
  rw [show 2 * j + 1 + 1 + 1 = (2 * j + 3) + 0 from by ring]
  apply stepStar_trans
  show ⟨(2 * j + 3) + 0, 0, 0, 2 * j + 2, 0⟩ [fm]⊢* ⟨0, 0, 0, 2 * j + 2, 2 * j + 3⟩
  · convert h3 using 3 <;> ring_nf
  apply stepStar_trans
  show ⟨0, 0, 0, 2 * j + 2, 2 * j + 3⟩ [fm]⊢* ⟨0, 2 * j + 2, 0, 0, 2 * j + 3⟩
  · convert h4 using 3 <;> ring_nf
  ring_nf; finish

theorem phase_odd (j : ℕ) :
    ⟨0, 2 * j + 1, 2, 2, 2 * j + 2⟩ [fm]⊢* ⟨0, 2 * j + 3, 0, 0, 2 * j + 4⟩ := by
  have h1 := r2r1r1_chain j 1 1 2 (j + 2)
  have h2 := r2_chain (j + 1) 1 1 (2 * j + 3) 0
  have h3 := r3_chain (2 * j + 4) 0 (2 * j + 3) 0
  have h4 := r4_chain (2 * j + 3) 0 0 (2 * j + 4)
  apply stepStar_trans
  show ⟨0, 2 * j + 1, 2, 2, 2 * j + 2⟩ [fm]⊢* ⟨0, 1, j + 2, 2 * j + 2, j + 2⟩
  · convert h1 using 3 <;> ring_nf
  rw [show j + 2 = (j + 1) + 1 from by ring]
  step fm; step fm
  -- After R2+R1: (1, 0, j+1+1, 2*j+2+1, j+1) = (1, 0, j+2, 2j+3, j+1)
  apply stepStar_trans
  show ⟨1, 0, j + 1 + 1, 2 * j + 2 + 1, j + 1⟩ [fm]⊢* ⟨2 * j + 3, 0, 1, 2 * j + 3, 0⟩
  · convert h2 using 3 <;> ring_nf
  rw [show 2 * j + 3 = (2 * j + 2) + 1 from by ring]
  step fm
  rw [show 2 * j + 2 + 1 = (2 * j + 1) + 1 + 1 from by ring]
  step fm
  rw [show 2 * j + 1 + 1 + 1 + 1 = (2 * j + 4) + 0 from by ring]
  apply stepStar_trans
  show ⟨(2 * j + 4) + 0, 0, 0, 2 * j + 3, 0⟩ [fm]⊢* ⟨0, 0, 0, 2 * j + 3, 2 * j + 4⟩
  · convert h3 using 3 <;> ring_nf
  apply stepStar_trans
  show ⟨0, 0, 0, 2 * j + 3, 2 * j + 4⟩ [fm]⊢* ⟨0, 2 * j + 3, 0, 0, 2 * j + 4⟩
  · convert h4 using 3 <;> ring_nf
  ring_nf; finish

theorem main_even (j : ℕ) :
    ⟨0, 2 * j + 1, 0, 0, 2 * j + 2⟩ [fm]⊢⁺ ⟨0, 2 * j + 2, 0, 0, 2 * j + 3⟩ := by
  rw [show 2 * j + 2 = (2 * j + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * j + 1, 0, 0, (2 * j + 1) + 1⟩ = some ⟨1, 2 * j + 1, 1, 1, 2 * j + 1⟩
    simp [fm]
  rw [show 2 * j + 1 = (2 * j) + 1 from by ring]
  step fm
  -- After R1: (0, 2j, 2, 2, 2j+1)
  show ⟨0, 2 * j, 2, 2, 2 * j + 1⟩ [fm]⊢* ⟨0, 2 * j + 2, 0, 0, 2 * j + 3⟩
  exact phase_even j

theorem main_odd (j : ℕ) :
    ⟨0, 2 * j + 2, 0, 0, 2 * j + 3⟩ [fm]⊢⁺ ⟨0, 2 * j + 3, 0, 0, 2 * j + 4⟩ := by
  rw [show 2 * j + 3 = (2 * j + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * j + 2, 0, 0, (2 * j + 2) + 1⟩ = some ⟨1, 2 * j + 2, 1, 1, 2 * j + 2⟩
    simp [fm]
  rw [show 2 * j + 2 = (2 * j + 1) + 1 from by ring]
  step fm
  -- After R1: (0, 2j+1, 2, 2, 2j+2)
  show ⟨0, 2 * j + 1, 2, 2, 2 * j + 2⟩ [fm]⊢* ⟨0, 2 * j + 3, 0, 0, 2 * j + 4⟩
  exact phase_odd j

theorem main_trans (n : ℕ) :
    ⟨0, n + 1, 0, 0, n + 2⟩ [fm]⊢⁺ ⟨0, n + 2, 0, 0, n + 3⟩ := by
  rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [show j + j = 2 * j from by ring] at hj; subst hj
    exact main_even j
  · subst hj
    rw [show 2 * j + 1 + 1 = 2 * j + 2 from by ring,
        show 2 * j + 1 + 2 = 2 * j + 3 from by ring,
        show 2 * j + 1 + 3 = 2 * j + 4 from by ring]
    exact main_odd j

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, n + 1, 0, 0, n + 2⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_693
