import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #732: [35/6, 4/55, 143/2, 3/7, 385/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 0  0  1  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_732

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d+1, e+1, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ d e f, ⟨k, 0, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 1) (f + 1))
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a d e f, ⟨a, 0, k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e f)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ b c d e f,
    ⟨0, 2 * k + b, c + 1, d, e + k, f⟩ [fm]⊢* ⟨0, b, c + k + 1, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · simp; exists 0
  · rw [show 2 * (k + 1) + b = (2 * k + b + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + b + 1 = (2 * k + b) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e f)
    ring_nf; finish

theorem main_even (m f : ℕ) :
    ⟨0, 0, 0, 2 * m, 4 * m + 1, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 1, 4 * m + 3, f + 2 * m + 2⟩ := by
  apply stepStar_stepPlus_stepPlus
  · exact r4_chain (2 * m) 0 (4 * m + 1) (f + 1)
  rw [show 0 + 2 * m = 2 * m from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * m, 0, 0, 4 * m + 1, f + 1⟩ = some ⟨0, 2 * m, 1, 1, 4 * m + 2, f⟩
    simp [fm]
  rw [show 4 * m + 2 = (3 * m + 2) + m from by ring]
  apply stepStar_trans (r2r1r1_chain m 0 0 1 (3 * m + 2) f)
  rw [show 0 + m + 1 = m + 1 from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring,
      show 3 * m + 2 = (2 * m + 1) + (m + 1) from by ring]
  apply stepStar_trans (r2_drain (m + 1) 0 (2 * m + 1) (2 * m + 1) f)
  rw [show 0 + 2 * (m + 1) = 2 * m + 2 from by ring]
  apply stepStar_trans (r3_chain (2 * m + 2) (2 * m + 1) (2 * m + 1) f)
  ring_nf; finish

theorem main_odd (m f : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, 4 * m + 3, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 2, 4 * m + 5, f + 2 * m + 3⟩ := by
  apply stepStar_stepPlus_stepPlus
  · exact r4_chain (2 * m + 1) 0 (4 * m + 3) (f + 1)
  rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * m + 1, 0, 0, 4 * m + 3, f + 1⟩ = some ⟨0, 2 * m + 1, 1, 1, 4 * m + 4, f⟩
    simp [fm]
  rw [show 4 * m + 4 = (3 * m + 4) + m from by ring]
  apply stepStar_trans (r2r1r1_chain m 1 0 1 (3 * m + 4) f)
  rw [show 0 + m + 1 = m + 1 from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring]
  rw [show m + 1 = (m) + 1 from by ring,
      show 3 * m + 4 = (3 * m + 3) + 1 from by ring]
  step fm
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm
  rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
      show 3 * m + 3 = (2 * m + 2) + (m + 1) from by ring]
  apply stepStar_trans (r2_drain (m + 1) 1 (2 * m + 2) (2 * m + 2) f)
  rw [show 1 + 2 * (m + 1) = 2 * m + 3 from by ring]
  apply stepStar_trans (r3_chain (2 * m + 3) (2 * m + 2) (2 * m + 2) f)
  ring_nf; finish

theorem main_trans (n f : ℕ) :
    ⟨0, 0, 0, n, 2 * n + 1, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 1, 2 * n + 3, f + n + 2⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    rw [show 2 * (2 * m) + 1 = 4 * m + 1 from by ring,
        show 2 * (2 * m) + 3 = 4 * m + 3 from by ring,
        show f + 2 * m + 2 = f + 2 * m + 2 from rfl]
    exact main_even m f
  · subst hm
    rw [show 2 * (2 * m + 1) + 1 = 4 * m + 3 from by ring,
        show 2 * (2 * m + 1) + 3 = 4 * m + 5 from by ring,
        show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show f + (2 * m + 1) + 2 = f + 2 * m + 3 from by ring]
    exact main_odd m f

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3, 2⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, 0, n, 2 * n + 1, f + 1⟩) ⟨1, 1⟩
  intro ⟨n, f⟩; exact ⟨⟨n + 1, f + n + 1⟩, main_trans n f⟩

end Sz22_2003_unofficial_732
