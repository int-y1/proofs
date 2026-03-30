import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #692: [35/6, 4/55, 11/2, 3/7, 60/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 2  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_692

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b+1, c+1, d, e⟩
  | _ => none

theorem r1r1r2_even : ∀ k, ∀ c d e, ⟨2, 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, 0, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem r1r1r2_odd : ∀ k, ∀ c d e, ⟨2, 2 * k + 1, c, d, e + k⟩ [fm]⊢* ⟨1, 0, c + k + 1, d + 2 * k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

theorem r4_drain : ∀ k, ∀ b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

theorem main_even (m : ℕ) :
    ⟨0, 2 * m + 2, 0, 0, 4 * m + 5⟩ [fm]⊢⁺ ⟨0, 2 * m + 3, 0, 0, 4 * m + 7⟩ := by
  rw [show 4 * m + 5 = (4 * m + 4) + 1 from by ring]
  step fm
  rw [show 2 * m + 2 + 1 = 2 * (m + 1) + 1 from by ring,
      show 4 * m + 4 = (3 * m + 3) + (m + 1) from by ring]
  apply stepStar_trans (r1r1r2_odd (m + 1) 1 0 (3 * m + 3))
  rw [show 1 + (m + 1) + 1 = m + 3 from by ring,
      show 0 + 2 * (m + 1) + 1 = 2 * m + 3 from by ring,
      show 3 * m + 3 = (2 * m) + (m + 3) from by ring]
  apply stepStar_trans (r2_chain (m + 3) 1 (2 * m + 3) (2 * m))
  rw [show 1 + 2 * (m + 3) = 2 * m + 7 from by ring]
  apply stepStar_trans (r3_drain (2 * m + 7) (2 * m + 3) (2 * m))
  rw [show 2 * m + (2 * m + 7) = 4 * m + 7 from by ring]
  apply stepStar_trans (r4_drain (2 * m + 3) 0 (4 * m + 7))
  ring_nf; finish

theorem main_odd (m : ℕ) :
    ⟨0, 2 * m + 3, 0, 0, 4 * m + 7⟩ [fm]⊢⁺ ⟨0, 2 * m + 4, 0, 0, 4 * m + 9⟩ := by
  rw [show 4 * m + 7 = (4 * m + 6) + 1 from by ring]
  step fm
  rw [show 2 * m + 3 + 1 = 2 * (m + 2) from by ring,
      show 4 * m + 6 = (3 * m + 4) + (m + 2) from by ring]
  apply stepStar_trans (r1r1r2_even (m + 2) 1 0 (3 * m + 4))
  rw [show 1 + (m + 2) = m + 3 from by ring,
      show 0 + 2 * (m + 2) = 2 * m + 4 from by ring,
      show 3 * m + 4 = (2 * m + 1) + (m + 3) from by ring]
  apply stepStar_trans (r2_chain (m + 3) 2 (2 * m + 4) (2 * m + 1))
  rw [show 2 + 2 * (m + 3) = 2 * m + 8 from by ring]
  apply stepStar_trans (r3_drain (2 * m + 8) (2 * m + 4) (2 * m + 1))
  rw [show 2 * m + 1 + (2 * m + 8) = 4 * m + 9 from by ring]
  apply stepStar_trans (r4_drain (2 * m + 4) 0 (4 * m + 9))
  ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, n + 2, 0, 0, 2 * n + 5⟩ [fm]⊢⁺ ⟨0, n + 3, 0, 0, 2 * n + 7⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    rw [show 2 * (2 * m) + 5 = 4 * m + 5 from by ring,
        show 2 * m + 3 = 2 * m + 3 from rfl,
        show 2 * (2 * m) + 7 = 4 * m + 7 from by ring]
    exact main_even m
  · subst hm
    rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 2 * (2 * m + 1) + 5 = 4 * m + 7 from by ring,
        show 2 * m + 1 + 3 = 2 * m + 4 from by ring,
        show 2 * (2 * m + 1) + 7 = 4 * m + 9 from by ring]
    exact main_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 5⟩)
  · execute fm 25
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, n + 2, 0, 0, 2 * n + 5⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_692
