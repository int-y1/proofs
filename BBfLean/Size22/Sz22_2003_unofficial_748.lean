import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #748: [35/6, 4/55, 5929/2, 3/7, 2/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  2  2
 0  1  0 -1  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_748

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (d + 2) (e + 2))
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ b c d e,
    ⟨0, b + 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, b, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e)
    ring_nf; finish

theorem r3r2r2_chain : ∀ m, ∀ a c d,
    ⟨a + 1, 0, c + 2 * m, d, 0⟩ [fm]⊢* ⟨a + 3 * m + 1, 0, c, d + 2 * m, 0⟩ := by
  intro m; induction' m with m ih <;> intro a c d
  · exists 0
  · rw [show c + 2 * (m + 1) = (c + 2 * m + 1) + 1 from by ring]
    step fm
    rw [show c + 2 * m + 1 = (c + 2 * m) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 3) c (d + 2))
    ring_nf; finish

theorem r3r2_tail : ∀ a, ∀ d,
    ⟨a + 1, 0, 1, d, 0⟩ [fm]⊢* ⟨a + 2, 0, 0, d + 2, 1⟩ := by
  intro a; induction' a with a ih <;> intro d
  · step fm; step fm; finish
  · step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    rw [show a + 1 + 2 = (a + 2) + 1 from by ring]
    finish

theorem main_even (m : ℕ) :
    ⟨0, 0, 0, 4 * m + 2, 2 * m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 12 * m + 8, 6 * m + 5⟩ := by
  rw [show 4 * m + 2 = 0 + (4 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (4 * m + 2) 0 0 (2 * m + 2))
  rw [show 0 + (4 * m + 2) = 4 * m + 2 from by ring]
  rw [show (2 * m + 2 : ℕ) = (2 * m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 4 * m + 2, 0, 0, (2 * m + 1) + 1⟩ = some ⟨1, 4 * m + 2, 0, 0, 2 * m + 1⟩
    simp [fm]
  rw [show 4 * m + 2 = (4 * m + 1) + 1 from by ring]
  step fm
  rw [show 4 * m + 1 = 1 + 2 * (2 * m) from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (r2r1r1_chain (2 * m) 1 0 1 1)
  rw [show 0 + 2 * m + 1 = 2 * m + 1 from by ring,
      show 1 + 2 * (2 * m) = 4 * m + 1 from by ring]
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm
  rw [show 2 * m = (2 * m) from rfl]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (r3r2r2_chain m 0 1 (4 * m + 2))
  rw [show 0 + 3 * m + 1 = 3 * m + 1 from by ring,
      show 4 * m + 2 + 2 * m = 6 * m + 2 from by ring]
  apply stepStar_trans (r3r2_tail (3 * m) (6 * m + 2))
  rw [show 3 * m + 2 = 3 * m + 2 from rfl]
  apply stepStar_trans (r3_drain (3 * m + 2) (6 * m + 4) 1)
  ring_nf; finish

theorem main_odd (m : ℕ) :
    ⟨0, 0, 0, 4 * m + 4, 2 * m + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 12 * m + 14, 6 * m + 8⟩ := by
  rw [show 4 * m + 4 = 0 + (4 * m + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (4 * m + 4) 0 0 (2 * m + 3))
  rw [show 0 + (4 * m + 4) = 4 * m + 4 from by ring]
  rw [show (2 * m + 3 : ℕ) = (2 * m + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 4 * m + 4, 0, 0, (2 * m + 2) + 1⟩ = some ⟨1, 4 * m + 4, 0, 0, 2 * m + 2⟩
    simp [fm]
  rw [show 4 * m + 4 = (4 * m + 3) + 1 from by ring]
  step fm
  rw [show 4 * m + 3 = 1 + 2 * (2 * m + 1) from by ring,
      show 2 * m + 2 = 1 + (2 * m + 1) from by ring]
  apply stepStar_trans (r2r1r1_chain (2 * m + 1) 1 0 1 1)
  rw [show 0 + (2 * m + 1) + 1 = 2 * m + 2 from by ring,
      show 1 + 2 * (2 * m + 1) = 4 * m + 3 from by ring]
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm
  rw [show 2 * m + 1 = (2 * m + 1) from rfl]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * m + 2 = 0 + 2 * (m + 1) from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 1) 0 0 (4 * m + 4))
  rw [show 0 + 3 * (m + 1) + 1 = 3 * m + 4 from by ring,
      show 4 * m + 4 + 2 * (m + 1) = 6 * m + 6 from by ring]
  apply stepStar_trans (r3_drain (3 * m + 4) (6 * m + 6) 0)
  ring_nf; finish

theorem main_trans (f : ℕ) :
    ⟨0, 0, 0, 2 * f + 2, f + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * f + 8, 3 * f + 5⟩ := by
  rcases Nat.even_or_odd f with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    rw [show 2 * (2 * m) + 2 = 4 * m + 2 from by ring,
        show 2 * m + 2 = 2 * m + 2 from rfl,
        show 6 * (2 * m) + 8 = 12 * m + 8 from by ring,
        show 3 * (2 * m) + 5 = 6 * m + 5 from by ring]
    exact main_even m
  · subst hm
    rw [show 2 * (2 * m + 1) + 2 = 4 * m + 4 from by ring,
        show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 6 * (2 * m + 1) + 8 = 12 * m + 14 from by ring,
        show 3 * (2 * m + 1) + 5 = 6 * m + 8 from by ring]
    exact main_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun f ↦ ⟨0, 0, 0, 2 * f + 2, f + 2⟩) 0
  intro f; refine ⟨3 * f + 3, ?_⟩
  convert main_trans f using 2; ring_nf

end Sz22_2003_unofficial_748
