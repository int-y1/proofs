import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #696: [35/6, 4/55, 11011/2, 3/7, 5/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  1  2  1
 0  1  0 -1  0  0
 0  0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_696

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+2, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b e fv, ⟨0, b, 0, 0 + k, e, fv⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, fv⟩ := by
  intro k; induction' k with k ih <;> intro b e fv
  · exists 0
  · rw [show 0 + (k + 1) = (0 + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) e fv)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e fv, ⟨a + k, 0, 0, d, e, fv⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 2 * k, fv + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e fv
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 2) (fv + 1))
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a d e fv, ⟨a, 0, 0 + k, d, e + k, fv⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e, fv⟩ := by
  intro k; induction' k with k ih <;> intro a d e fv
  · exists 0
  · rw [show 0 + (k + 1) = (0 + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e fv)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ c d e fv, ⟨0, 2 * k, c + 1, d, e + k, fv⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, e, fv⟩ := by
  intro k; induction' k with k ih <;> intro c d e fv
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e fv)
    ring_nf; finish

theorem main_trans (m n : ℕ) (hm : m ≥ n + 1) :
    ⟨0, 0, 0, 2 * m, 2 * m + n + 1, 2 * m - n⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + 2, 4 * m + n + 4, 4 * m - n + 1⟩ := by
  obtain ⟨p, hp⟩ : ∃ p, 2 * m - n = p + 1 := ⟨2 * m - n - 1, by omega⟩
  have hp2 : 4 * m - n + 1 = p + 2 * m + 2 := by omega
  rw [hp, hp2]
  have phase1 : ⟨0, 0, 0, 2 * m, 2 * m + n + 1, p + 1⟩ [fm]⊢*
      ⟨0, 2 * m, 0, 0, 2 * m + n + 1, p + 1⟩ := by
    have := r4_chain (2 * m) 0 (2 * m + n + 1) (p + 1)
    simp only [Nat.zero_add] at this; exact this
  have phase2 : ⟨0, 2 * m, 0, 0, 2 * m + n + 1, p + 1⟩ [fm]⊢⁺
      ⟨0, 2 * m, 1, 0, 2 * m + n + 1, p⟩ := by
    step fm; finish
  have phase3 : ⟨0, 2 * m, 1, 0, 2 * m + n + 1, p⟩ [fm]⊢*
      ⟨0, 0, m + 1, 2 * m, m + n + 1, p⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 2 * m + n + 1 = (m + n + 1) + m from by ring]
    have := r2r1r1_chain m 0 0 (m + n + 1) p
    simp only [Nat.zero_add] at this ⊢; exact this
  have phase4 : ⟨0, 0, m + 1, 2 * m, m + n + 1, p⟩ [fm]⊢*
      ⟨2 * m + 2, 0, 0, 2 * m, n, p⟩ := by
    rw [show m + 1 = 0 + (m + 1) from by ring,
        show m + n + 1 = n + (m + 1) from by ring,
        show 2 * m + 2 = 0 + 2 * (m + 1) from by ring]
    exact r2_chain (m + 1) 0 (2 * m) n p
  have phase5 : ⟨2 * m + 2, 0, 0, 2 * m, n, p⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * m + 2, 4 * m + n + 4, p + 2 * m + 2⟩ := by
    rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring,
        show 4 * m + 2 = 2 * m + (2 * m + 2) from by ring,
        show 4 * m + n + 4 = n + 2 * (2 * m + 2) from by ring,
        show p + 2 * m + 2 = p + (2 * m + 2) from by ring]
    exact r3_chain (2 * m + 2) 0 (2 * m) n p
  exact stepStar_stepPlus_stepPlus phase1
    (stepPlus_stepStar_stepPlus phase2
      (stepStar_trans phase3
        (stepStar_trans phase4 phase5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 6, 3⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m n, q = ⟨0, 0, 0, 2 * m, 2 * m + n + 1, 2 * m - n⟩ ∧ m ≥ n + 1)
  · intro c ⟨m, n, hq, hm⟩; subst hq
    refine ⟨⟨0, 0, 0, 4 * m + 2, 4 * m + n + 4, 4 * m - n + 1⟩,
      ⟨2 * m + 1, n + 1, ?_, ?_⟩, main_trans m n hm⟩
    · show (0, 0, 0, 4 * m + 2, 4 * m + n + 4, 4 * m - n + 1) =
           (0, 0, 0, 2 * (2 * m + 1), 2 * (2 * m + 1) + (n + 1) + 1, 2 * (2 * m + 1) - (n + 1))
      have h1 : 4 * m + 2 = 2 * (2 * m + 1) := by ring
      have h2 : 4 * m + n + 4 = 2 * (2 * m + 1) + (n + 1) + 1 := by ring
      have h3 : 4 * m - n + 1 = 2 * (2 * m + 1) - (n + 1) := by omega
      rw [h1, h2, h3]
    · omega
  · exact ⟨2, 1, by simp, by omega⟩
