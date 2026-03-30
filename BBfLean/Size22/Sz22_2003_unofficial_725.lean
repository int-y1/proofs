import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #725: [35/6, 4/55, 143/2, 3/7, 165/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 0  1  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_725

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e+1, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) (f + 1))
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a d e f, ⟨a, 0, k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e f)
    ring_nf; finish

theorem r1r1r2_even : ∀ m, ∀ c d e f, ⟨2, 2 * m, c, d, e + m, f⟩ [fm]⊢* ⟨2, 0, c + m, d + 2 * m, e, f⟩ := by
  intro m; induction' m with m ih <;> intro c d e f
  · exists 0
  · rw [show 2 * (m + 1) = (2 * m + 1) + 1 from by ring,
        show e + (m + 1) = (e + m) + 1 from by ring]
    step fm
    rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem r1r1r2_odd : ∀ m, ∀ c d e f, ⟨2, 2 * m + 1, c, d, e + m, f⟩ [fm]⊢* ⟨1, 0, c + m + 1, d + 2 * m + 1, e, f⟩ := by
  intro m; induction' m with m ih <;> intro c d e f
  · step fm; finish
  · rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 from by ring,
        show e + (m + 1) = (e + m) + 1 from by ring]
    step fm
    rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem main_even (k f : ℕ) :
    ⟨0, 0, 0, 2 * k + 1, 4 * k + 3, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 2, 4 * k + 5, f + 2 * k + 4⟩ := by
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * k + 1) 0 (4 * k + 3) (f + 1))
  rw [show (0 : ℕ) + (2 * k + 1) = 2 * k + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * k + 1, 0, 0, 4 * k + 3, f + 1⟩ = some ⟨0, 2 * k + 2, 1, 0, 4 * k + 4, f⟩
    simp [fm]
  step fm
  rw [show 2 * k + 2 = 2 * (k + 1) from by ring,
      show 4 * k + 3 = (3 * k + 2) + (k + 1) from by ring]
  apply stepStar_trans (r1r1r2_even (k + 1) 0 0 (3 * k + 2) f)
  rw [show (0 : ℕ) + (k + 1) = k + 1 from by ring,
      show (0 : ℕ) + 2 * (k + 1) = 2 * k + 2 from by ring,
      show 3 * k + 2 = (2 * k + 1) + (k + 1) from by ring]
  apply stepStar_trans (r2_chain (k + 1) 2 (2 * k + 2) (2 * k + 1) f)
  rw [show 2 + 2 * (k + 1) = 0 + (2 * k + 4) from by ring]
  apply stepStar_trans (r3_chain (2 * k + 4) 0 (2 * k + 2) (2 * k + 1) f)
  ring_nf; finish

theorem main_odd (k f : ℕ) :
    ⟨0, 0, 0, 2 * k + 2, 4 * k + 5, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 3, 4 * k + 7, f + 2 * k + 5⟩ := by
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * k + 2) 0 (4 * k + 5) (f + 1))
  rw [show (0 : ℕ) + (2 * k + 2) = 2 * k + 2 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * k + 2, 0, 0, 4 * k + 5, f + 1⟩ = some ⟨0, 2 * k + 3, 1, 0, 4 * k + 6, f⟩
    simp [fm]
  step fm
  rw [show 2 * k + 3 = 2 * (k + 1) + 1 from by ring,
      show 4 * k + 5 = (3 * k + 4) + (k + 1) from by ring]
  apply stepStar_trans (r1r1r2_odd (k + 1) 0 0 (3 * k + 4) f)
  rw [show (0 : ℕ) + (k + 1) + 1 = k + 2 from by ring,
      show (0 : ℕ) + 2 * (k + 1) + 1 = 2 * k + 3 from by ring,
      show 3 * k + 4 = (2 * k + 2) + (k + 2) from by ring]
  apply stepStar_trans (r2_chain (k + 2) 1 (2 * k + 3) (2 * k + 2) f)
  rw [show 1 + 2 * (k + 2) = 0 + (2 * k + 5) from by ring]
  apply stepStar_trans (r3_chain (2 * k + 5) 0 (2 * k + 3) (2 * k + 2) f)
  ring_nf; finish

theorem main_trans (n f : ℕ) :
    ⟨0, 0, 0, n + 1, 2 * n + 3, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 2, 2 * n + 5, f + n + 4⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    rw [show 2 * (2 * k) + 3 = 4 * k + 3 from by ring,
        show 2 * (2 * k) + 5 = 4 * k + 5 from by ring,
        show f + 2 * k + 4 = f + 2 * k + 4 from by ring]
    exact main_even k f
  · subst hk
    rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
        show 2 * (2 * k + 1) + 3 = 4 * k + 5 from by ring,
        show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
        show 2 * (2 * k + 1) + 5 = 4 * k + 7 from by ring,
        show f + (2 * k + 1) + 4 = f + 2 * k + 5 from by ring]
    exact main_odd k f

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3, 3⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, 0, n + 1, 2 * n + 3, f + 1⟩) ⟨0, 2⟩
  intro ⟨n, f⟩; exact ⟨⟨n + 1, f + n + 3⟩, main_trans n f⟩

end Sz22_2003_unofficial_725
