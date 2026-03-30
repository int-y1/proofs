import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #710: [35/6, 4/55, 121/2, 3/7, 75/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  1  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_710

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+2, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ c d e, ⟨0, 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem r2r1r1_chain_tail : ∀ k, ∀ c d e,
    ⟨0, 2 * k + 1, c + 1, d, e + k + 1⟩ [fm]⊢* ⟨1, 0, c + k + 1, d + 2 * k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem main_odd (m e : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, e + 2 * m + 5⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * m + 2, e + 4 * m + 12⟩ := by
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * m + 1) 0 0 (e + 2 * m + 5))
  rw [show 0 + (2 * m + 1) = (2 * m) + 1 from by ring,
      show e + 2 * m + 5 = (e + 2 * m + 4) + 1 from by ring]
  step fm
  rw [show e + 2 * m + 4 = (e + 2 * m + 3) + 1 from by ring]
  step fm
  rw [show (2 * m) + 1 = (2 * m) + 1 from rfl]
  step fm; step fm
  rw [show e + 2 * m + 3 = (e + m + 3) + m from by ring]
  apply stepStar_trans (r2r1r1_chain m 2 2 (e + m + 3))
  rw [show 2 + m + 1 = 0 + (m + 3) from by ring,
      show 2 + 2 * m = 2 * m + 2 from by ring,
      show e + m + 3 = e + (m + 3) from by ring]
  apply stepStar_trans (r2_chain (m + 3) 0 0 (2 * m + 2) e)
  rw [show 0 + 2 * (m + 3) = 0 + (2 * m + 6) from by ring]
  apply stepStar_trans (r3_drain (2 * m + 6) 0 (2 * m + 2) e)
  ring_nf; finish

theorem main_even (m e : ℕ) :
    ⟨0, 0, 0, 2 * m + 2, e + 2 * m + 6⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * m + 3, e + 4 * m + 14⟩ := by
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * m + 2) 0 0 (e + 2 * m + 6))
  rw [show 0 + (2 * m + 2) = (2 * m + 1) + 1 from by ring,
      show e + 2 * m + 6 = (e + 2 * m + 5) + 1 from by ring]
  step fm
  rw [show e + 2 * m + 5 = (e + 2 * m + 4) + 1 from by ring]
  step fm
  rw [show (2 * m + 1) + 1 = (2 * m) + 1 + 1 from by ring]
  step fm; step fm
  rw [show e + 2 * m + 4 = (e + m + 3) + m + 1 from by ring,
      show 2 * m + 1 = 2 * m + 1 from rfl]
  apply stepStar_trans (r2r1r1_chain_tail m 2 2 (e + m + 3))
  rw [show 2 + m + 1 = 0 + (m + 3) from by ring,
      show 2 + 2 * m + 1 = 2 * m + 3 from by ring,
      show e + m + 3 = e + (m + 3) from by ring]
  apply stepStar_trans (r2_chain (m + 3) 1 0 (2 * m + 3) e)
  rw [show 1 + 2 * (m + 3) = 0 + (2 * m + 7) from by ring]
  apply stepStar_trans (r3_drain (2 * m + 7) 0 (2 * m + 3) e)
  ring_nf; finish

theorem main_trans (n e : ℕ) :
    ⟨0, 0, 0, n + 1, e + n + 5⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 2, e + 2 * n + 12⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    rw [show 2 * m + 1 = 2 * m + 1 from rfl,
        show e + 2 * m + 5 = e + 2 * m + 5 from rfl,
        show 2 * m + 2 = 2 * m + 2 from rfl,
        show e + 2 * (2 * m) + 12 = e + 4 * m + 12 from by ring]
    exact main_odd m e
  · subst hm
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show e + (2 * m + 1) + 5 = e + 2 * m + 6 from by ring,
        show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show e + 2 * (2 * m + 1) + 12 = e + 4 * m + 14 from by ring]
    exact main_even m e

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 8⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨0, 0, 0, n + 1, e + n + 5⟩) ⟨0, 3⟩
  intro ⟨n, e⟩
  refine ⟨⟨n + 1, e + n + 6⟩, ?_⟩
  convert main_trans n e using 2
  ring_nf

end Sz22_2003_unofficial_710
