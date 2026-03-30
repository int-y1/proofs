import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1101: [5/6, 4/105, 539/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
 2 -1 -1 -1  0
-1  0  0  2  1
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1101

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: move d to b.
theorem d_to_b : ∀ k, ∀ b d, ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- b_drain: each round of 5 steps reduces b by 4 and e by 1, increases c by 2.
theorem b_drain : ∀ k, ∀ B c E, ⟨(0 : ℕ), B + 4 * k, c, 0, E + k⟩ [fm]⊢* ⟨0, B, c + 2 * k, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro B c E
  · exists 0
  · rw [show B + 4 * (k + 1) = (B + 4 * k) + 4 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    show ⟨0, (B + 4 * k) + 4, c, 0, (E + k) + 1⟩ [fm]⊢* _
    step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih B (c + 2) E)
    ring_nf; finish

-- b_final_3: finish draining b=3 remainder.
theorem b_final_3 : ⟨(0 : ℕ), 3, c, 0, E + 1⟩ [fm]⊢* ⟨0, 0, c, 4, E + 3⟩ := by
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; finish

-- intermediate: set up d for c_drain when b fully drained to 0.
theorem intermediate : ⟨(0 : ℕ), 0, c, 0, E + 1⟩ [fm]⊢* ⟨0, 0, c, 3, E + 1⟩ := by
  step fm; step fm; finish

-- c_drain: each round of 4 steps reduces c by 1, increases d by 2 and e by 2.
theorem c_drain : ∀ k, ∀ c D E, ⟨(0 : ℕ), 0, c + k, D + 2, E⟩ [fm]⊢* ⟨0, 0, c, D + 2 + 2 * k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c D E
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    show ⟨0, 0, (c + k) + 1, D + 2, E⟩ [fm]⊢* _
    step fm; step fm; step fm; step fm
    rw [show D + 4 = (D + 2) + 2 from by ring]
    apply stepStar_trans (ih c (D + 2) (E + 2))
    ring_nf; finish

-- Transition A -> B: canonical state (4m, 3m^2-m) to (4m+3, 3m^2+2m), parameterized as m = n+1.
theorem trans_AB (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, 4 * n + 4, 3 * n * n + 5 * n + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * n + 7, 3 * n * n + 8 * n + 5⟩ := by
  -- First R4 step for ⊢⁺
  rw [show (4 * n + 4 : ℕ) = (4 * n + 3) + 1 from by ring]
  step fm
  -- d_to_b for remaining d
  rw [show (4 * n + 3 : ℕ) = 0 + (4 * n + 3) from by ring]
  apply stepStar_trans (d_to_b (4 * n + 3) 1 0 (e := 3 * n * n + 5 * n + 2))
  -- Now at (0, 4n+4, 0, 0, 3n^2+5n+2)
  rw [show 1 + (4 * n + 3) = 0 + 4 * (n + 1) from by ring,
      show (3 * n * n + 5 * n + 2 : ℕ) = (3 * n * n + 4 * n + 1) + (n + 1) from by ring]
  apply stepStar_trans (b_drain (n + 1) 0 0 (3 * n * n + 4 * n + 1))
  -- Now at (0, 0, 2n+2, 0, 3n^2+4n+1)
  rw [show (0 : ℕ) + 2 * (n + 1) = 2 * n + 2 from by ring,
      show (3 * n * n + 4 * n + 1 : ℕ) = (3 * n * n + 4 * n) + 1 from by ring]
  apply stepStar_trans (intermediate (c := 2 * n + 2) (E := 3 * n * n + 4 * n))
  -- Now at (0, 0, 2n+2, 3, 3n^2+4n+1)
  rw [show (2 * n + 2 : ℕ) = 0 + (2 * n + 2) from by ring,
      show (3 : ℕ) = 1 + 2 from by ring]
  apply stepStar_trans (c_drain (2 * n + 2) 0 1 (3 * n * n + 4 * n + 1))
  ring_nf; finish

-- Transition B -> A: canonical state (4m+3, 3m^2+2m) to (4(m+1), 3(m+1)^2-(m+1)), parameterized as m = n+1.
theorem trans_BA (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, 4 * n + 7, 3 * n * n + 8 * n + 5⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * n + 8, 3 * n * n + 11 * n + 10⟩ := by
  -- First R4 step for ⊢⁺
  rw [show (4 * n + 7 : ℕ) = (4 * n + 6) + 1 from by ring]
  step fm
  -- d_to_b for remaining d
  rw [show (4 * n + 6 : ℕ) = 0 + (4 * n + 6) from by ring]
  apply stepStar_trans (d_to_b (4 * n + 6) 1 0 (e := 3 * n * n + 8 * n + 5))
  -- Now at (0, 4n+7, 0, 0, 3n^2+8n+5)
  rw [show 1 + (4 * n + 6) = 3 + 4 * (n + 1) from by ring,
      show (3 * n * n + 8 * n + 5 : ℕ) = (3 * n * n + 7 * n + 4) + (n + 1) from by ring]
  apply stepStar_trans (b_drain (n + 1) 3 0 (3 * n * n + 7 * n + 4))
  -- Now at (0, 3, 2n+2, 0, 3n^2+7n+4)
  rw [show (0 : ℕ) + 2 * (n + 1) = 2 * n + 2 from by ring,
      show (3 * n * n + 7 * n + 4 : ℕ) = (3 * n * n + 7 * n + 3) + 1 from by ring]
  apply stepStar_trans (b_final_3 (c := 2 * n + 2) (E := 3 * n * n + 7 * n + 3))
  -- Now at (0, 0, 2n+2, 4, 3n^2+7n+6)
  rw [show (2 * n + 2 : ℕ) = 0 + (2 * n + 2) from by ring,
      show (4 : ℕ) = 2 + 2 from by ring,
      show (3 * n * n + 7 * n + 3 + 3 : ℕ) = 3 * n * n + 7 * n + 6 from by ring]
  apply stepStar_trans (c_drain (2 * n + 2) 0 2 (3 * n * n + 7 * n + 6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 2⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 0, 0, 4 * n + 4, 3 * n * n + 5 * n + 2⟩ ∨
                        q = ⟨0, 0, 0, 4 * n + 7, 3 * n * n + 8 * n + 5⟩)
  · intro c ⟨n, hn⟩
    rcases hn with rfl | rfl
    · exact ⟨⟨0, 0, 0, 4 * n + 7, 3 * n * n + 8 * n + 5⟩,
        ⟨n, Or.inr rfl⟩, trans_AB n⟩
    · refine ⟨⟨0, 0, 0, 4 * (n + 1) + 4, 3 * (n + 1) * (n + 1) + 5 * (n + 1) + 2⟩,
        ⟨n + 1, Or.inl rfl⟩, ?_⟩
      show ⟨(0 : ℕ), 0, 0, 4 * n + 7, 3 * n * n + 8 * n + 5⟩ [fm]⊢⁺
        ⟨0, 0, 0, 4 * (n + 1) + 4, 3 * (n + 1) * (n + 1) + 5 * (n + 1) + 2⟩
      rw [show 4 * (n + 1) + 4 = 4 * n + 8 from by ring,
          show 3 * (n + 1) * (n + 1) + 5 * (n + 1) + 2 = 3 * n * n + 11 * n + 10 from by ring]
      exact trans_BA n
  · exact ⟨0, Or.inl rfl⟩

end Sz22_2003_unofficial_1101
