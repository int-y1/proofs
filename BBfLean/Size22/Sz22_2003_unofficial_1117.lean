import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1117: [5/6, 4/35, 77/2, 9/7, 28/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  1  1
 0  2  0 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1117

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

theorem spiral : ∀ k, ∀ a e, ⟨a + 1, 0, k, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- One round of the main loop: 6 steps.
-- (0, b+4, C, 0, E+1) →* (0, b, C+3, 0, E)
-- R5: (2, b+4, C, 1, E)
-- R1: (1, b+3, C+1, 1, E)
-- R1: (0, b+2, C+2, 1, E)
-- R2: (2, b+2, C+1, 0, E)
-- R1: (1, b+1, C+2, 0, E)
-- R1: (0, b, C+3, 0, E)
theorem main_round : ⟨0, b + 4, C, 0, E + 1⟩ [fm]⊢* ⟨0, b, C + 3, 0, E⟩ := by
  execute fm 6

theorem main_loop : ∀ k, ∀ b C E, ⟨0, b + 4 * k, C, 0, E + k⟩ [fm]⊢* ⟨0, b, C + 3 * k, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro b C E
  · exists 0
  · rw [show b + 4 * (k + 1) = (b + 4) + 4 * k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    apply stepStar_trans (ih (b + 4) C (E + 1))
    rw [show C + 3 * k = C + 3 * k from rfl]
    apply stepStar_trans (main_round (b := b) (C := C + 3 * k) (E := E))
    ring_nf; finish

theorem tail_b0 : ⟨0, 0, C + 1, 0, E + 1⟩ [fm]⊢⁺ ⟨C + 4, 0, 0, 0, E + C⟩ := by
  step fm
  step fm
  show ⟨3 + 1, 0, C, 0, E⟩ [fm]⊢* ⟨C + 4, 0, 0, 0, E + C⟩
  apply stepStar_trans (spiral C 3 E)
  ring_nf; finish

theorem tail_b2 : ⟨0, 2, C, 0, E + 1⟩ [fm]⊢⁺ ⟨C + 3, 0, 0, 0, E + C + 1⟩ := by
  step fm
  step fm
  step fm
  step fm
  show ⟨1 + 1, 0, C + 1, 0, E⟩ [fm]⊢* ⟨C + 3, 0, 0, 0, E + C + 1⟩
  apply stepStar_trans (spiral (C + 1) 1 E)
  ring_nf; finish

theorem even_trans : ⟨2 * m + 2, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨3 * m + 6, 0, 0, 0, e + 4 * m + 2⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
    exact r3_chain (2 * m + 2) 0 0 e
  apply stepStar_stepPlus_stepPlus
  · exact r4_chain (2 * m + 2) 0 0 (e + (2 * m + 2))
  apply stepStar_stepPlus_stepPlus
  · rw [show 0 + 2 * (2 * m + 2) = 0 + 4 * (m + 1) from by ring,
        show e + (2 * m + 2) = (e + m + 1) + (m + 1) from by ring]
    exact main_loop (m + 1) 0 0 (e + m + 1)
  rw [show 0 + 3 * (m + 1) = (3 * m + 2) + 1 from by ring,
      show e + m + 1 = (e + m) + 1 from by ring]
  have := tail_b0 (C := 3 * m + 2) (E := e + m)
  rw [show 3 * m + 2 + 4 = 3 * m + 6 from by ring,
      show e + m + (3 * m + 2) = e + 4 * m + 2 from by ring] at this
  exact this

theorem odd_trans : ⟨2 * m + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨3 * m + 3, 0, 0, 0, e + 4 * m + 1⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
    exact r3_chain (2 * m + 1) 0 0 e
  apply stepStar_stepPlus_stepPlus
  · exact r4_chain (2 * m + 1) 0 0 (e + (2 * m + 1))
  apply stepStar_stepPlus_stepPlus
  · rw [show 0 + 2 * (2 * m + 1) = 2 + 4 * m from by ring,
        show e + (2 * m + 1) = (e + m + 1) + m from by ring]
    exact main_loop m 2 0 (e + m + 1)
  rw [show 0 + 3 * m = 3 * m from by ring,
      show e + m + 1 = (e + m) + 1 from by ring]
  have := tail_b2 (C := 3 * m) (E := e + m)
  rw [show e + m + (3 * m) + 1 = e + 4 * m + 1 from by ring] at this
  exact this

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 1)
  · intro c ⟨a, e, hq, ha⟩; subst hq
    rcases Nat.even_or_odd a with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact ⟨⟨3 * m' + 6, 0, 0, 0, e + 4 * m' + 2⟩,
        ⟨3 * m' + 6, e + 4 * m' + 2, rfl, by omega⟩, even_trans⟩
    · subst hm
      exact ⟨⟨3 * m + 3, 0, 0, 0, e + 4 * m + 1⟩,
        ⟨3 * m + 3, e + 4 * m + 1, rfl, by omega⟩, odd_trans⟩
  · exact ⟨1, 0, rfl, by omega⟩
