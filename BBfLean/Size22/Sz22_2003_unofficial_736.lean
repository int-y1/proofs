import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #736: [35/6, 4/55, 143/2, 3/7, 70/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 1  0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_736

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c+1, d+1, e, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) e f

theorem r3_chain : ∀ k, ∀ d e f, ⟨k, 0, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 1) (f + 1))
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a d e f, ⟨a, 0, k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e f)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ c d e f,
    ⟨0, 2 * k, c + 1, d, e + k, f⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem r2r1r1_chain_odd : ∀ k, ∀ c d e f,
    ⟨0, 2 * k + 1, c + 1, d, e + k + 1, f⟩ [fm]⊢* ⟨1, 0, c + k + 1, d + 2 * k + 1, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · rw [show e + 0 + 1 = (e) + 1 from by ring]
    step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem main_even (m F : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, 4 * m + 3, F + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 2, 4 * m + 5, F + 2 * m + 4⟩ := by
  apply stepStar_stepPlus_stepPlus
  · exact r4_chain (2 * m + 1) 0 (4 * m + 3) (F + 1)
  rw [show 0 + (2 * m + 1) = (2 * m) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, (2 * m) + 1, 0, 0, 4 * m + 3, F + 1⟩ = some ⟨1, (2 * m) + 1, 1, 1, 4 * m + 3, F⟩
    simp [fm]
  step fm
  rw [show 4 * m + 3 = (3 * m + 3) + m from by ring]
  apply stepStar_trans (r2r1r1_chain m 1 2 (3 * m + 3) F)
  rw [show 1 + m + 1 = m + 2 from by ring,
      show 2 + 2 * m = 2 * m + 2 from by ring,
      show 3 * m + 3 = (2 * m + 1) + (m + 2) from by ring]
  apply stepStar_trans (r2_chain (m + 2) 0 (2 * m + 2) (2 * m + 1) F)
  rw [show 0 + 2 * (m + 2) = 2 * m + 4 from by ring]
  apply stepStar_trans (r3_chain (2 * m + 4) (2 * m + 2) (2 * m + 1) F)
  ring_nf; finish

theorem main_odd (m F : ℕ) :
    ⟨0, 0, 0, 2 * m + 2, 4 * m + 5, F + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 3, 4 * m + 7, F + 2 * m + 5⟩ := by
  apply stepStar_stepPlus_stepPlus
  · exact r4_chain (2 * m + 2) 0 (4 * m + 5) (F + 1)
  rw [show 0 + (2 * m + 2) = (2 * m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, (2 * m + 1) + 1, 0, 0, 4 * m + 5, F + 1⟩ = some ⟨1, (2 * m + 1) + 1, 1, 1, 4 * m + 5, F⟩
    simp [fm]
  step fm
  rw [show 4 * m + 5 = (3 * m + 4) + (m + 1) from by ring]
  apply stepStar_trans (r2r1r1_chain_odd m 1 2 (3 * m + 4) F)
  rw [show 1 + m + 1 = m + 2 from by ring,
      show 2 + 2 * m + 1 = 2 * m + 3 from by ring,
      show 3 * m + 4 = (2 * m + 2) + (m + 2) from by ring]
  apply stepStar_trans (r2_chain (m + 2) 1 (2 * m + 3) (2 * m + 2) F)
  rw [show 1 + 2 * (m + 2) = 2 * m + 5 from by ring]
  apply stepStar_trans (r3_chain (2 * m + 5) (2 * m + 3) (2 * m + 2) F)
  ring_nf; finish

theorem main_trans (n F : ℕ) :
    ⟨0, 0, 0, n + 1, 2 * n + 3, F + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 2, 2 * n + 5, F + n + 4⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    convert main_even m F using 2; ring_nf
  · subst hm
    convert main_odd m F using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3, 3⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, F⟩ ↦ ⟨0, 0, 0, n + 1, 2 * n + 3, F + 1⟩) ⟨0, 2⟩
  intro ⟨n, F⟩; exact ⟨⟨n + 1, F + n + 3⟩, main_trans n F⟩

end Sz22_2003_unofficial_736
