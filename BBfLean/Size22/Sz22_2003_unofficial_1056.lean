import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1056: [5/18, 4/35, 539/2, 3/7, 14/11]

Vector representation:
```
-1 -2  1  0  0
 2  0 -1 -1  0
-1  0  0  2  1
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1056

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

private theorem r3_drain_b0 : ∀ k D E,
    ⟨(k : ℕ), 0, 0, D, E⟩ [fm]⊢* ⟨0, 0, 0, D + 2 * k, E + k⟩ := by
  intro k; induction' k with k ih <;> intro D E
  · ring_nf; finish
  · rw [show D + 2 * (k + 1) = (D + 2) + 2 * k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    step fm; exact ih (D + 2) (E + 1)

private theorem r3_drain_b1 : ∀ k D E,
    ⟨(k : ℕ), 1, 0, D, E⟩ [fm]⊢* ⟨0, 1, 0, D + 2 * k, E + k⟩ := by
  intro k; induction' k with k ih <;> intro D E
  · ring_nf; finish
  · rw [show D + 2 * (k + 1) = (D + 2) + 2 * k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    step fm; exact ih (D + 2) (E + 1)

private theorem r4_drain : ∀ k b E,
    ⟨(0 : ℕ), b, 0, k, E⟩ [fm]⊢* ⟨0, b + k, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro b E
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) E

private theorem process_b0 : ∀ C, ∀ A E,
    ⟨(A + 1 : ℕ), 0, C, 0, E⟩ [fm]⊢* ⟨0, 2 * A + 3 * C + 2, 0, 0, E + A + 2 * C + 1⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih; intro A E
  rcases C with _ | _ | C
  · apply stepStar_trans (r3_drain_b0 (A + 1) 0 E)
    convert r4_drain (2 * A + 2) 0 (E + A + 1) using 2; ring_nf
  · step fm; step fm; step fm
    apply stepStar_trans (r3_drain_b0 (A + 1) 3 (E + 2))
    convert r4_drain (2 * A + 5) 0 (E + A + 3) using 2; ring_nf
  · step fm; step fm; step fm
    rw [show A + 1 + 1 + 2 = (A + 3) + 1 from by ring]
    apply stepStar_trans (ih C (by omega) (A + 3) (E + 1))
    ring_nf; finish

private theorem process_b1 : ∀ C, ∀ A E,
    ⟨(A + 1 : ℕ), 1, C, 0, E⟩ [fm]⊢* ⟨0, 2 * A + 3 * C + 3, 0, 0, E + A + 2 * C + 1⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih; intro A E
  rcases C with _ | _ | C
  · apply stepStar_trans (r3_drain_b1 (A + 1) 0 E)
    convert r4_drain (2 * A + 2) 1 (E + A + 1) using 2; ring_nf
  · step fm; step fm; step fm
    apply stepStar_trans (r3_drain_b1 (A + 1) 3 (E + 2))
    convert r4_drain (2 * A + 5) 1 (E + A + 3) using 2; ring_nf
  · step fm; step fm; step fm
    rw [show A + 1 + 1 + 2 = (A + 3) + 1 from by ring]
    apply stepStar_trans (ih C (by omega) (A + 3) (E + 1))
    ring_nf; finish

-- Helper: one step via show+unfold for R5 when c position has a variable
private theorem step_r5 (b C E : ℕ) :
    ⟨(0 : ℕ), b, C, 0, E + 1⟩ [fm]⊢ ⟨1, b, C, 1, E⟩ := by
  show fm ⟨0, b, C, 0, E + 1⟩ = some ⟨1, b, C, 1, E⟩
  unfold fm; simp only

-- Outer round: (0, b+6, C, 0, E+1) ⊢* (0, b, C+2, 0, E) via R5,R1,R2,R1,R1
private theorem outer_round (b C E : ℕ) :
    ⟨(0 : ℕ), b + 6, C, 0, E + 1⟩ [fm]⊢* ⟨0, b, C + 2, 0, E⟩ := by
  apply stepStar_trans (step_stepStar (step_r5 (b + 6) C E))
  step fm; step fm; step fm; step fm
  ring_nf; finish

private theorem outer_chain : ∀ k, ∀ b C E,
    ⟨(0 : ℕ), b + 6 * (k + 1), C, 0, E + (k + 1)⟩ [fm]⊢* ⟨0, b, C + 2 * (k + 1), 0, E⟩ := by
  intro k; induction' k with k ih <;> intro b C E
  · rw [show 6 * 1 = 6 from by ring, show 2 * 1 = 2 from by ring,
        show E + 1 = E + 1 from rfl]
    exact outer_round b C E
  · apply stepStar_trans
    · rw [show 6 * (k + 1 + 1) = 6 * (k + 1) + 6 from by ring,
          show E + (k + 1 + 1) = (E + 1) + (k + 1) from by ring,
          show b + (6 * (k + 1) + 6) = (b + 6) + 6 * (k + 1) from by ring]
      exact ih (b + 6) C (E + 1)
    · show ⟨(0 : ℕ), b + 6, C + 2 * (k + 1), 0, E + 1⟩ [fm]⊢*
          ⟨0, b, C + 2 * (k + 1 + 1), 0, E⟩
      rw [show C + 2 * (k + 1 + 1) = (C + 2 * (k + 1)) + 2 from by ring]
      exact outer_round b (C + 2 * (k + 1)) E

-- Tail lemmas: process (0, r, 2*K, 0, E+1) for each remainder r ∈ {0..5}
-- R5 step handled via step_r5 since 2*K in c position is problematic for step fm
private theorem tail_r0 (K E : ℕ) :
    ⟨(0 : ℕ), 0, 2 * K, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 6 * K + 3, 0, 0, E + 4 * K + 1⟩ := by
  apply step_stepStar_stepPlus (step_r5 0 (2 * K) E)
  rcases K with _ | K
  · step fm
    apply stepStar_trans (r4_drain 3 0 (E + 1))
    ring_nf; finish
  · -- (1, 0, 2K+2, 1, E): c = 2K+2 >= 1, d = 1 >= 1, so R2 fires
    step fm
    rw [show (3 : ℕ) = 2 + 1 from by ring]
    apply stepStar_trans (process_b0 (2 * K + 1) 2 E)
    ring_nf; finish

private theorem tail_r1 (K E : ℕ) :
    ⟨(0 : ℕ), 1, 2 * K, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 6 * K + 4, 0, 0, E + 4 * K + 1⟩ := by
  apply step_stepStar_stepPlus (step_r5 1 (2 * K) E)
  rcases K with _ | K
  · -- (1, 1, 0, 1, E): R3 fires (a=1, b=1<2)
    step fm
    apply stepStar_trans (r4_drain 3 1 (E + 1))
    ring_nf; finish
  · -- (1, 1, 2K+2, 1, E): R2 fires (c >= 1, d >= 1)
    step fm
    rw [show (3 : ℕ) = 2 + 1 from by ring]
    apply stepStar_trans (process_b1 (2 * K + 1) 2 E)
    ring_nf; finish

private theorem tail_r2 (K E : ℕ) :
    ⟨(0 : ℕ), 2, 2 * K, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 6 * K + 4, 0, 0, E + 4 * K + 2⟩ := by
  apply step_stepStar_stepPlus (step_r5 2 (2 * K) E)
  -- (1, 2, 2K, 1, E): R1 fires (a=1, b=2)
  step fm
  rcases K with _ | K
  · -- (0, 0, 1, 1, E): R2 -> (2, 0, 0, 0, E) -> R3x2 -> R4x4
    step fm; step fm; step fm
    apply stepStar_trans (r4_drain 4 0 (E + 2))
    ring_nf; finish
  · -- (0, 0, 2K+3, 1, E): R2 -> (2, 0, 2K+2, 0, E) = (1+1, 0, 2K+2, 0, E)
    step fm
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (process_b0 (2 * (K + 1)) 1 E)
    ring_nf; finish

private theorem tail_r3 (K E : ℕ) :
    ⟨(0 : ℕ), 3, 2 * K, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 6 * K + 5, 0, 0, E + 4 * K + 2⟩ := by
  apply step_stepStar_stepPlus (step_r5 3 (2 * K) E)
  -- (1, 3, 2K, 1, E): R1 fires
  step fm
  rcases K with _ | K
  · step fm; step fm; step fm
    apply stepStar_trans (r4_drain 4 1 (E + 2))
    ring_nf; finish
  · step fm
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (process_b1 (2 * (K + 1)) 1 E)
    ring_nf; finish

private theorem tail_r4 (K E : ℕ) :
    ⟨(0 : ℕ), 4, 2 * K, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 6 * K + 5, 0, 0, E + 4 * K + 3⟩ := by
  apply step_stepStar_stepPlus (step_r5 4 (2 * K) E)
  -- (1, 4, 2K, 1, E): R1 -> (0, 2, 2K+1, 1, E) -> R2 -> (2, 2, 2K, 0, E)
  -- -> R1 -> (1, 0, 2K+1, 0, E)
  step fm
  rcases K with _ | K
  · -- (0, 2, 1, 1, E) -> R2 -> (2, 2, 0, 0, E) -> R1 -> (1, 0, 1, 0, E)
    -- -> R3 -> (0, 0, 1, 2, E+1) -> R2 -> (2, 0, 0, 1, E+1)
    -- -> R3 -> (1, 0, 0, 3, E+2) -> R3 -> (0, 0, 0, 5, E+3) -> R4x5
    step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (r4_drain 5 0 (E + 3))
    ring_nf; finish
  · -- (0, 2, 2K+3, 1, E) -> R2 -> (2, 2, 2K+2, 0, E) -> R1 -> (1, 0, 2K+3, 0, E)
    -- -> R3 -> (0, 0, 2K+3, 2, E+1) -> R2 -> (2, 0, 2K+2, 1, E+1)
    -- -> R2 -> (4, 0, 2K+1, 0, E+1) = (3+1, 0, 2K+1, 0, E+1)
    step fm; step fm; step fm; step fm; step fm
    rw [show (4 : ℕ) = 3 + 1 from by ring]
    apply stepStar_trans (process_b0 (2 * K + 1) 3 (E + 1))
    ring_nf; finish

private theorem tail_r5 (K E : ℕ) :
    ⟨(0 : ℕ), 5, 2 * K, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 6 * K + 6, 0, 0, E + 4 * K + 3⟩ := by
  apply step_stepStar_stepPlus (step_r5 5 (2 * K) E)
  step fm
  rcases K with _ | K
  · step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (r4_drain 5 1 (E + 3))
    ring_nf; finish
  · step fm; step fm; step fm; step fm; step fm
    rw [show (4 : ℕ) = 3 + 1 from by ring]
    apply stepStar_trans (process_b1 (2 * K + 1) 3 (E + 1))
    ring_nf; finish

private theorem full_trans (b e : ℕ) (hb : b ≥ 2) (he : e ≥ 1) (hbe : 2 * e ≥ b) :
    ∃ b' e', ⟨(0 : ℕ), b, 0, 0, e⟩ [fm]⊢⁺ ⟨0, b', 0, 0, e'⟩ ∧
    b' ≥ 2 ∧ e' ≥ 1 ∧ 2 * e' ≥ b' := by
  -- Decompose b = 6*j + r
  obtain ⟨j, r, rfl, hr6⟩ : ∃ j r, b = 6 * j + r ∧ r < 6 :=
    ⟨b / 6, b % 6, (Nat.div_add_mod b 6).symm, Nat.mod_lt _ (by omega)⟩
  have hej : e ≥ j + 1 := by omega
  obtain ⟨w, rfl⟩ : ∃ w, e = w + j + 1 := ⟨e - j - 1, by omega⟩
  -- After j outer rounds: (0, r, 2j, 0, w+1) via outer_chain
  have hoc_star : j ≥ 1 → ⟨(0 : ℕ), 6 * j + r, 0, 0, w + j + 1⟩ [fm]⊢*
      ⟨0, r, 2 * j, 0, w + 1⟩ := by
    intro hj1
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [show 6 * (j' + 1) + r = r + 6 * (j' + 1) from by ring,
        show w + (j' + 1) + 1 = (w + 1) + (j' + 1) from by ring]
    convert outer_chain j' r 0 (w + 1) using 2; ring_nf
  -- Dispatch on r
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
  rcases hr_cases with rfl | rfl | rfl | rfl | rfl | rfl
  -- r = 0
  · have hj1 : j ≥ 1 := by omega
    exact ⟨6 * j + 3, w + 4 * j + 1, stepStar_stepPlus_stepPlus (hoc_star hj1)
      (tail_r0 j w), by omega, by omega, by omega⟩
  -- r = 1
  · have hj1 : j ≥ 1 := by omega
    exact ⟨6 * j + 4, w + 4 * j + 1, stepStar_stepPlus_stepPlus (hoc_star hj1)
      (tail_r1 j w), by omega, by omega, by omega⟩
  -- r = 2
  · refine ⟨6 * j + 4, w + 4 * j + 2, ?_, by omega, by omega, by omega⟩
    rcases j.eq_zero_or_pos with rfl | hj1
    · exact tail_r2 0 w
    · exact stepStar_stepPlus_stepPlus (hoc_star hj1) (tail_r2 j w)
  -- r = 3
  · refine ⟨6 * j + 5, w + 4 * j + 2, ?_, by omega, by omega, by omega⟩
    rcases j.eq_zero_or_pos with rfl | hj1
    · exact tail_r3 0 w
    · exact stepStar_stepPlus_stepPlus (hoc_star hj1) (tail_r3 j w)
  -- r = 4
  · refine ⟨6 * j + 5, w + 4 * j + 3, ?_, by omega, by omega, by omega⟩
    rcases j.eq_zero_or_pos with rfl | hj1
    · exact tail_r4 0 w
    · exact stepStar_stepPlus_stepPlus (hoc_star hj1) (tail_r4 j w)
  -- r = 5
  · refine ⟨6 * j + 6, w + 4 * j + 3, ?_, by omega, by omega, by omega⟩
    rcases j.eq_zero_or_pos with rfl | hj1
    · exact tail_r5 0 w
    · exact stepStar_stepPlus_stepPlus (hoc_star hj1) (tail_r5 j w)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b e, q = ⟨0, b, 0, 0, e⟩ ∧ b ≥ 2 ∧ e ≥ 1 ∧ 2 * e ≥ b)
  · intro q ⟨b, e, hq, hb, he, hbe⟩; subst hq
    obtain ⟨b', e', hstep, hb', he', hbe'⟩ := full_trans b e hb he hbe
    exact ⟨⟨0, b', 0, 0, e'⟩, ⟨b', e', rfl, hb', he', hbe'⟩, hstep⟩
  · exact ⟨2, 1, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_1056
