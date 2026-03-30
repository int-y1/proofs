import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1129: [5/6, 44/35, 49/2, 27/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  3  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1129

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem e_to_b : ∀ k, ∀ b D, ⟨0, b, 0, D, k⟩ [fm]⊢* ⟨0, b + 3 * k, 0, D, 0⟩ := by
  intro k; induction' k with k ih <;> intro b D
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 3) D)
    ring_nf; finish

theorem r3_drain : ∀ A, ∀ D E, ⟨A, 0, 0, D, E⟩ [fm]⊢* ⟨0, 0, 0, D + 2 * A, E⟩ := by
  intro A; induction' A with A ih <;> intro D E
  · exists 0
  · step fm
    apply stepStar_trans (ih (D + 2) E)
    ring_nf; finish

theorem interleaved : ∀ K, ∀ B C D E,
    ⟨0, B + 2 * K, C + 1, D + K + 1, E⟩ [fm]⊢* ⟨0, B, C + K + 1, D + 1, E + K⟩ := by
  intro K; induction' K with K ih <;> intro B C D E
  · ring_nf; exists 0
  · rw [show B + 2 * (K + 1) = (B + 2 * K) + 2 from by ring,
        show D + (K + 1) + 1 = (D + K + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show C + (K + 1) + 1 = (C + 1) + K + 1 from by ring,
        show E + (K + 1) = (E + 1) + K from by ring]
    exact ih B (C + 1) D (E + 1)

theorem tail_gen : ∀ C, ∀ A D E,
    ⟨A, 0, C, D + 1, E⟩ [fm]⊢* ⟨0, 0, 0, 2 * A + 3 * C + D + 1, E + C⟩ := by
  intro C; induction' C with C ih <;> intro A D E
  · apply stepStar_trans (r3_drain A (D + 1) E)
    ring_nf; finish
  · step fm
    rcases D with _ | D
    · step fm
      rw [show (2 : ℕ) = 1 + 1 from by ring]
      apply stepStar_trans (ih (A + 1) 1 (E + 1))
      ring_nf; finish
    · apply stepStar_trans (ih (A + 2) D (E + 1))
      ring_nf; finish

theorem tail_d0 : ∀ C, ∀ A E,
    ⟨A + 1, 0, C, 0, E⟩ [fm]⊢* ⟨0, 0, 0, 2 * A + 3 * C + 2, E + C⟩ := by
  intro C A E
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (tail_gen C A 1 E)
  ring_nf; finish

theorem main_e0 : ⟨0, 0, 0, D + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, D + 4, 1⟩ := by
  execute fm 4

-- E = 2(m+1), D offset = 3(m+1)+2 = 3m+5
theorem main_even (m : ℕ) :
    ⟨0, 0, 0, D + 3 * m + 5, 2 * m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, D + 9 * m + 13, 6 * m + 7⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, D + 3 * m + 5, 2 * m + 2⟩ =
        some ⟨0, 3, 0, D + 3 * m + 5, 2 * m + 1⟩
    simp [fm]
  apply stepStar_trans (e_to_b (2 * m + 1) 3 (D + 3 * m + 5))
  rw [show 3 + 3 * (2 * m + 1) = (6 * m + 4) + 1 + 1 from by ring,
      show D + 3 * m + 5 = (D + 3 * m + 3) + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show 6 * m + 4 = 0 + 2 * (3 * m + 2) from by ring,
      show D + 3 * m + 3 = D + (3 * m + 2) + 1 from by ring]
  apply stepStar_trans (interleaved (3 * m + 2) 0 1 D 1)
  rw [show 1 + (3 * m + 2) + 1 = 3 * m + 4 from by ring,
      show 1 + (3 * m + 2) = 3 * m + 3 from by ring]
  apply stepStar_trans (tail_gen (3 * m + 4) 0 D (3 * m + 3))
  ring_nf; finish

-- E = 2m+1, D offset = 3m+3
theorem main_odd (m : ℕ) :
    ⟨0, 0, 0, D + 3 * m + 3, 2 * m + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, D + 9 * m + 8, 6 * m + 4⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, D + 3 * m + 3, 2 * m + 1⟩ =
        some ⟨0, 3, 0, D + 3 * m + 3, 2 * m⟩
    simp [fm]
  apply stepStar_trans (e_to_b (2 * m) 3 (D + 3 * m + 3))
  rw [show 3 + 3 * (2 * m) = (6 * m + 1) + 1 + 1 from by ring,
      show D + 3 * m + 3 = (D + 3 * m + 1) + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show 6 * m + 1 = 1 + 2 * (3 * m) from by ring,
      show D + 3 * m + 1 = D + (3 * m) + 1 from by ring]
  apply stepStar_trans (interleaved (3 * m) 1 1 D 1)
  rw [show 1 + 3 * m + 1 = 3 * m + 2 from by ring,
      show 1 + 3 * m = 3 * m + 1 from by ring]
  step fm; step fm
  rcases D with _ | D
  · apply stepStar_trans (tail_d0 (3 * m + 2) 0 (3 * m + 2))
    ring_nf; finish
  · apply stepStar_trans (tail_gen (3 * m + 2) 1 D (3 * m + 2))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ 2 * D ≥ 3 * E + 4)
  · intro c ⟨D, E, hq, hinv⟩; subst hq
    rcases Nat.even_or_odd E with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- E even: E = m + m
      rw [show m + m = 2 * m from by ring] at hm; subst hm
      rcases m with _ | m
      · -- m = 0, E = 0
        obtain ⟨D', rfl⟩ : ∃ D', D = D' + 2 := ⟨D - 2, by omega⟩
        exact ⟨⟨0, 0, 0, D' + 4, 1⟩, ⟨D' + 4, 1, rfl, by omega⟩, main_e0⟩
      · -- m ≥ 1, E = 2(m+1) = 2m+2
        obtain ⟨D', rfl⟩ : ∃ D', D = D' + 3 * m + 5 := ⟨D - (3 * m + 5), by omega⟩
        exact ⟨⟨0, 0, 0, D' + 9 * m + 13, 6 * m + 7⟩,
          ⟨D' + 9 * m + 13, 6 * m + 7, rfl, by omega⟩, main_even m⟩
    · -- E odd: E = 2m + 1
      subst hm
      obtain ⟨D', rfl⟩ : ∃ D', D = D' + 3 * m + 3 := ⟨D - (3 * m + 3), by omega⟩
      exact ⟨⟨0, 0, 0, D' + 9 * m + 8, 6 * m + 4⟩,
        ⟨D' + 9 * m + 8, 6 * m + 4, rfl, by omega⟩, main_odd m⟩
  · exact ⟨2, 0, rfl, by omega⟩
