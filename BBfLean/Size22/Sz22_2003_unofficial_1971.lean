import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1971: [99/35, 2/5, 275/6, 7/11, 15/2]

Vector representation:
```
 0  2 -1 -1  1
 1  0 -1  0  0
-1 -1  2  0  1
 0  0  0  1 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1971

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: move e to d
theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih (d + 1)

-- Main loop: R3+R1+R1 interleaving
theorem main_loop : ∀ k A B D E,
    ⟨A + k, B + 1, 0, D + 2 * k, E⟩ [fm]⊢* ⟨A, B + 3 * k + 1, 0, D, E + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro A B D E
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show D + 2 * (k + 1) = (D + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    rw [show E + 1 + 1 + 1 = (E + 3) from by ring]
    apply stepStar_trans (ih A (B + 3) D (E + 3))
    ring_nf; finish

-- R3+R2+R2 drain
theorem drain : ∀ k A E,
    ⟨A + 1, k + 1, 0, 0, E⟩ [fm]⊢* ⟨A + k + 2, 0, 0, 0, E + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · step fm; step fm; step fm; finish
  · step fm; step fm; step fm
    apply stepStar_trans (ih (A + 1) (E + 1))
    ring_nf; finish

-- Full odd transition composed as ⊢*
theorem odd_star :
    ⟨A + m + 2, 0, 0, 0, 2 * m + 1⟩ [fm]⊢*
    ⟨A + 3 * m + 4, 0, 0, 0, 6 * m + 4⟩ := by
  -- R4 chain
  apply stepStar_trans (e_to_d (2 * m + 1) (d := 0) (a := A + m + 2))
  rw [show (0 : ℕ) + (2 * m + 1) = 2 * m + 1 from by ring]
  -- R5 + R1
  rw [show A + m + 2 = (A + m + 1) + 1 from by ring,
      show 2 * m + 1 = (2 * m) + 0 + 1 from by ring]
  step fm; step fm
  -- Main loop m times
  rw [show A + m + 1 = (A + 1) + m from by ring,
      show 2 * m = 0 + 2 * m from by ring]
  apply stepStar_trans (main_loop m (A + 1) 2 0 1)
  -- After main loop: (A+1, 3m+3, 0, 0, 3m+1)
  rw [show 2 + 3 * m + 1 = (3 * m + 2) + 1 from by ring,
      show 1 + 3 * m = 3 * m + 1 from by ring]
  -- Drain
  apply stepStar_trans (drain (3 * m + 2) A (3 * m + 1))
  ring_nf; finish

-- Full even transition composed as ⊢*
theorem even_star :
    ⟨A + m + 2, 0, 0, 0, 2 * (m + 1)⟩ [fm]⊢*
    ⟨A + 3 * m + 5, 0, 0, 0, 6 * m + 7⟩ := by
  -- R4 chain
  apply stepStar_trans (e_to_d (2 * (m + 1)) (d := 0) (a := A + m + 2))
  rw [show (0 : ℕ) + 2 * (m + 1) = 2 * m + 2 from by ring]
  -- R5 + R1
  rw [show A + m + 2 = (A + m + 1) + 1 from by ring,
      show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm; step fm
  -- Main loop m times
  rw [show A + m + 1 = (A + 1) + m from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (main_loop m (A + 1) 2 1 1)
  -- After main loop: (A+1, 3m+3, 0, 1, 3m+1)
  rw [show 2 + 3 * m + 1 = (3 * m + 2) + 1 from by ring,
      show 1 + 3 * m = 3 * m + 1 from by ring]
  -- D=1 exit: R3+R1+R2
  step fm; step fm; step fm
  -- After D=1 exit: (A+1, 3m+4, 0, 0, 3m+3)
  rw [show 3 * m + 2 + 2 = (3 * m + 3) + 1 from by ring,
      show 3 * m + 1 + 1 + 1 = 3 * m + 3 from by ring]
  -- Drain
  apply stepStar_trans (drain (3 * m + 3) A (3 * m + 3))
  ring_nf; finish

-- Convert ⊢* to ⊢⁺
theorem odd_trans :
    ⟨A + m + 2, 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺
    ⟨A + 3 * m + 4, 0, 0, 0, 6 * m + 4⟩ := by
  apply stepStar_stepPlus odd_star
  intro h; have := congr_arg (fun q : Q ↦ q.2.2.2.2) h; simp at this; omega

theorem even_trans :
    ⟨A + m + 2, 0, 0, 0, 2 * (m + 1)⟩ [fm]⊢⁺
    ⟨A + 3 * m + 5, 0, 0, 0, 6 * m + 7⟩ := by
  apply stepStar_stepPlus even_star
  intro h; have := congr_arg (fun q : Q ↦ q.2.2.2.2) h; simp at this; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 1 ∧ 2 * a ≥ e + 3)
  · intro c ⟨a, e, hq, he, ha⟩; subst hq
    rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
      obtain ⟨A, rfl⟩ : ∃ A, a = A + m + 2 := ⟨a - m - 2, by omega⟩
      exact ⟨⟨A + 3 * m + 5, 0, 0, 0, 6 * m + 7⟩,
        ⟨A + 3 * m + 5, 6 * m + 7, rfl, by omega, by omega⟩, even_trans⟩
    · subst hK
      obtain ⟨A, rfl⟩ : ∃ A, a = A + K + 2 := ⟨a - K - 2, by omega⟩
      exact ⟨⟨A + 3 * K + 4, 0, 0, 0, 6 * K + 4⟩,
        ⟨A + 3 * K + 4, 6 * K + 4, rfl, by omega, by omega⟩, odd_trans⟩
  · exact ⟨2, 1, rfl, by omega, by omega⟩
