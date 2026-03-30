import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #722: [35/6, 4/55, 143/2, 3/7, 14/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_722

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

theorem r1r2_chain : ∀ k, ∀ a c d e f, ⟨a + 1, k, c, d, e + k, f⟩ [fm]⊢* ⟨a + k + 1, 0, c, d + k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rcases a with _ | a
    · step fm
      have h := ih 1 c (d + 1) e f
      rw [show (1 : ℕ) + k + 1 = 0 + (k + 1) + 1 from by ring,
          show d + 1 + k = d + (k + 1) from by ring] at h
      exact h
    · rw [show e + k + 1 = (e + 1) + k from by ring]
      apply stepStar_trans (ih a (c + 1) (d + 1) (e + 1) f)
      step fm
      ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) (f + 1))
    ring_nf; finish

theorem main_trans (n f : ℕ) :
    ⟨0, 0, 0, n, n + 1, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 1, n + 2, f + n + 1⟩ := by
  apply stepStar_stepPlus_stepPlus (r4_chain n 0 (n + 1) (f + 1))
  rw [show (0 : ℕ) + n = n from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, n, 0, 0, n + 1, f + 1⟩ = some ⟨1, n, 0, 1, n + 1, f⟩
    simp [fm]
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show n + 1 = 1 + n from by ring]
  apply stepStar_trans (r1r2_chain n 0 0 1 1 f)
  rw [show 0 + n + 1 = 0 + (n + 1) from by ring,
      show 1 + n = n + 1 from by ring]
  apply stepStar_trans (r3_chain (n + 1) 0 (n + 1) 1 f)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, 0, n, n + 1, f + 1⟩) ⟨0, 0⟩
  intro ⟨n, f⟩; exact ⟨⟨n + 1, f + n⟩, main_trans n f⟩

end Sz22_2003_unofficial_722
