import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #812: [35/6, 7865/2, 4/77, 3/5, 2/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  1  0  2  1
 2  0  0 -1 -1  0
 0  1 -1  0  0  0
 1  0  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_812

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+2, f+1⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

theorem c_to_b : ∀ k b, ⟨(0 : ℕ), b, c + k, 0, e, f⟩ [fm]⊢* ⟨0, b + k, c, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (b + 1)); ring_nf; finish

theorem r1r1r3_chain : ∀ k c d e f,
    ⟨(2 : ℕ), 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, 0, c + 2 * k, d + k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
      show e + (k + 1) = (e + 1) + k from by ring]
  step fm; step fm
  rw [show (e + 1) + k = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (c + 1 + 1) (d + 1) e f)
  ring_nf; finish

theorem r3r2r2_chain : ∀ k c e f,
    ⟨(0 : ℕ), 0, c, k, e + k, f⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + 4 * k, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show e + k + 2 + 2 = (e + 4) + k from by ring]
  apply stepStar_trans (ih (c + 1 + 1) (e + 4) (f + 1 + 1))
  ring_nf; finish

theorem main_trans (s t : ℕ) (hs : s ≥ 1) (m : ℕ) (hm : s + t = 2 * m + 1) :
    ⟨(0 : ℕ), 0, s + t, 0, 2 * s + t, t + 1⟩ [fm]⊢⁺
    ⟨0, 0, s + 1 + (s + 2 * t), 0, 2 * (s + 1) + (s + 2 * t), s + 2 * t + 1⟩ := by
  have phase1 : ⟨(0 : ℕ), 0, s + t, 0, 2 * s + t, t + 1⟩ [fm]⊢*
      ⟨0, s + t, 0, 0, 2 * s + t, t + 1⟩ := by
    rw [show s + t = 0 + (s + t) from by ring]
    exact c_to_b (s + t) 0
  have phase2 : ⟨(0 : ℕ), s + t, 0, 0, 2 * s + t, t + 1⟩ [fm]⊢⁺
      ⟨2, 2 * m, 1, 0, 2 * s + t - 1, t⟩ := by
    rw [hm, show 2 * s + t = (2 * s + t - 1) + 1 from by omega]
    step fm; step fm; step fm; finish
  have phase3 : ⟨(2 : ℕ), 2 * m, 1, 0, 2 * s + t - 1, t⟩ [fm]⊢*
      ⟨2, 0, 1 + 2 * m, m, s + m, t⟩ := by
    rw [show 2 * s + t - 1 = (s + m) + m from by omega]
    have := r1r1r3_chain m 1 0 (s + m) t
    simp at this; exact this
  have phase4 : ⟨(2 : ℕ), 0, 1 + 2 * m, m, s + m, t⟩ [fm]⊢*
      ⟨0, 0, 1 + 2 * m + 1 + 1, m, s + m + 2 + 2, t + 1 + 1⟩ := by
    step fm; step fm; finish
  have phase5 : ⟨(0 : ℕ), 0, 1 + 2 * m + 1 + 1, m, s + m + 2 + 2, t + 1 + 1⟩ [fm]⊢*
      ⟨0, 0, s + 1 + (s + 2 * t), 0, 2 * (s + 1) + (s + 2 * t), s + 2 * t + 1⟩ := by
    rw [show s + m + 2 + 2 = (s + 4) + m from by ring,
        show 1 + 2 * m + 1 + 1 = s + t + 2 from by omega,
        show t + 1 + 1 = t + 2 from by ring,
        show s + 1 + (s + 2 * t) = s + t + 2 + 2 * m from by omega,
        show 2 * (s + 1) + (s + 2 * t) = s + 4 + 4 * m from by omega,
        show s + 2 * t + 1 = t + 2 + 2 * m from by omega]
    exact r3r2r2_chain m (s + t + 2) (s + 4) (t + 2)
  apply stepStar_stepPlus_stepPlus phase1
  apply stepPlus_stepStar_stepPlus phase2
  apply stepStar_trans phase3
  apply stepStar_trans phase4
  exact phase5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ s t, q = ⟨0, 0, s + t, 0, 2 * s + t, t + 1⟩ ∧
      s ≥ 1 ∧ ∃ m, s + t = 2 * m + 1)
  · intro c ⟨s, t, hq, hs, m, hm⟩
    refine ⟨⟨0, 0, s + 1 + (s + 2 * t), 0, 2 * (s + 1) + (s + 2 * t), s + 2 * t + 1⟩,
      ⟨s + 1, s + 2 * t, rfl, by omega, s + t, by omega⟩, ?_⟩
    rw [hq]
    exact main_trans s t hs m hm
  · exact ⟨1, 0, rfl, by omega, 0, by omega⟩
