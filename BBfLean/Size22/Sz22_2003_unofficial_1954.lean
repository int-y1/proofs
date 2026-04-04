import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1954: [9/70, 7/15, 275/7, 2/11, 49/2]

Vector representation:
```
-1  2 -1 -1  0
 0 -1 -1  1  0
 0  0  2 -1  1
 1  0  0  0 -1
-1  0  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1954

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | _ => none

theorem nine_step : ⟨a + 3, b, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 2, b + 2, 0, 0, 0⟩ := by
  execute fm 9

theorem r3_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro c d e; exists 0
  · intro c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 2) d (e + 1))
    ring_nf; finish

theorem e_to_a : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a + k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c e; exists 0
  · intro a c e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c e)
    ring_nf; finish

theorem drain : ∀ j, ∀ B D, ⟨0, B + 2 * j, 0, D + 1, D + 1⟩ [fm]⊢* ⟨0, B, 0, D + j + 1, D + j + 1⟩ := by
  intro j; induction' j with j ih
  · intro B D; exists 0
  · intro B D
    rw [show B + 2 * (j + 1) = (B + 2) + 2 * j from by ring]
    apply stepStar_trans (ih (B + 2) D)
    rw [show D + j + 1 = (D + j) + 1 from by ring]
    step fm; step fm; step fm
    rw [show D + j + 2 = D + (j + 1) + 1 from by ring]
    finish

theorem r2r1_chain : ∀ j, ∀ A B C, ⟨A + j, B + 1, C + 2 * j, 0, 0⟩ [fm]⊢* ⟨A, B + 1 + j, C, 0, 0⟩ := by
  intro j; induction' j with j ih
  · intro A B C; exists 0
  · intro A B C
    rw [show A + (j + 1) = (A + j) + 1 from by ring,
        show C + 2 * (j + 1) = (C + 2 * j) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih A (B + 1) C)
    rw [show B + 1 + 1 + j = B + 1 + (j + 1) from by ring]
    finish

theorem cleanup : ⟨k + 1, k + 5, 1, 0, 0⟩ [fm]⊢⁺ ⟨k + 1, k + 5, 0, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Combined R3 + e->a: (0, 0, c, D, E) -> (E+D, 0, c+2D, 0, 0)
-- with explicit d offset for r3_chain
theorem r3_e2a : ∀ D, ∀ c E, ⟨0, 0, c, 0 + D, E⟩ [fm]⊢* ⟨E + D, 0, c + 2 * D, 0, 0⟩ := by
  intro D; induction' D with D ih
  · intro c E
    simp only [Nat.add_zero, Nat.mul_zero]
    rw [show E = 0 + E from by ring]
    apply stepStar_trans (e_to_a E 0 c 0)
    ring_nf; finish
  · intro c E
    rw [show 0 + (D + 1) = (0 + D) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 2) (E + 1))
    ring_nf; finish

-- (0, 1, 0, D+1, D+1) -> (2D+3, 0, 2D+3, 0, 0)
theorem phase_mid_even : ∀ D, ⟨0, 1, 0, D + 1, D + 1⟩ [fm]⊢* ⟨2 * D + 3, 0, 2 * D + 3, 0, 0⟩ := by
  intro D
  apply stepStar_trans
  · show ⟨0, 1, 0, D + 1, D + 1⟩ [fm]⊢* ⟨0, 0, 1, D + 1, D + 2⟩
    step fm; step fm; ring_nf; finish
  rw [show D + 1 = 0 + (D + 1) from by ring]
  apply stepStar_trans (r3_e2a (D + 1) 1 (D + 2))
  ring_nf; finish

-- (0, 0, 0, D+1, D+1) -> (2D+2, 0, 2D+2, 0, 0)
theorem phase_mid_odd : ∀ D, ⟨0, 0, 0, D + 1, D + 1⟩ [fm]⊢* ⟨2 * D + 2, 0, 2 * D + 2, 0, 0⟩ := by
  intro D
  rw [show D + 1 = 0 + (D + 1) from by ring]
  apply stepStar_trans (r3_e2a (D + 1) 0 (0 + (D + 1)))
  ring_nf; finish

-- (2(M+1)+3, 0, 2(M+1)+3, 0, 0) ⊢⁺ (M+1, M+5, 0, 0, 0)
theorem tail_odd : ∀ M, ⟨2 * (M + 1) + 3, 0, 2 * (M + 1) + 3, 0, 0⟩ [fm]⊢⁺ ⟨M + 1, M + 5, 0, 0, 0⟩ := by
  intro M
  rw [show 2 * (M + 1) + 3 = (2 * (M + 1) + 2) + 1 from by ring]
  step fm
  rw [show 2 * (M + 1) + 3 = (2 * (M + 1) + 1) + 1 + 1 from by ring,
      show 2 * (M + 1) + 2 = (2 * (M + 1) + 1) + 1 from by ring]
  step fm
  rw [show 2 * (M + 1) + 1 = (2 * M + 2) + 1 from by ring]
  step fm
  -- Now at (2*M+2, 4, 2*(M+1)+1, 0, 0).
  rw [show 2 * (M + 1) + 1 = 1 + 2 * (M + 1) from by ring,
      show 2 * M + 2 = (M + 1) + (M + 1) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r2r1_chain (M + 1) (M + 1) 3 1)
  rw [show 3 + 1 + (M + 1) = M + 5 from by ring,
      show M + 1 + 4 = M + 5 from by ring]
  exact stepPlus_stepStar (cleanup (k := M))

-- (2M+4, 0, 2M+4, 0, 0) ⊢⁺ (M, M+5, 0, 0, 0)
theorem tail_even : ∀ M, ⟨2 * M + 4, 0, 2 * M + 4, 0, 0⟩ [fm]⊢⁺ ⟨M, M + 5, 0, 0, 0⟩ := by
  intro M
  -- 3 opening steps: R5, R1, R1
  rw [show 2 * M + 4 = (2 * M + 3) + 1 from by ring]
  step fm
  rw [show 2 * M + 4 = (2 * M + 2) + 1 + 1 from by ring,
      show 2 * M + 3 = (2 * M + 2) + 1 from by ring]
  step fm
  rw [show 2 * M + 2 = (2 * M + 1) + 1 from by ring]
  step fm
  -- Now at (2M+1, 4, 2M+2, 0, 0)
  rw [show 2 * M + 1 = M + (M + 1) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring,
      show 2 * M + 2 = 0 + 2 * (M + 1) from by ring]
  apply stepStar_trans (r2r1_chain (M + 1) M 3 0)
  rw [show 3 + 1 + (M + 1) = M + 5 from by ring]
  finish

-- Even b: (2, 2*(k+2), 0, 0, 0) ⊢⁺ (k+2, k+6, 0, 0, 0)
theorem even_trans : ⟨2, 2 * (k + 2), 0, 0, 0⟩ [fm]⊢⁺ ⟨k + 2, k + 6, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · show ⟨2, 2 * (k + 2), 0, 0, 0⟩ [fm]⊢* ⟨0, 1 + 2 * (k + 2), 0, 1, 1⟩
    rw [show 2 * (k + 2) = k + k + 4 from by ring]
    step fm; step fm; step fm
    rw [show k + k + 4 + 2 = (1 + 2 * (k + 2)) + 1 from by ring]
    step fm; ring_nf; finish
  apply stepStar_stepPlus_stepPlus (drain (k + 2) 1 0)
  simp only [Nat.zero_add]
  apply stepStar_stepPlus_stepPlus (phase_mid_even (k + 2))
  rw [show 2 * (k + 2) + 3 = 2 * (k + 1 + 1) + 3 from by ring]
  exact tail_odd (k + 1)

-- Odd b: (2, 2*(k+2)+1, 0, 0, 0) ⊢⁺ (k+2, k+7, 0, 0, 0)
theorem odd_trans : ⟨2, 2 * (k + 2) + 1, 0, 0, 0⟩ [fm]⊢⁺ ⟨k + 2, k + 7, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · show ⟨2, 2 * (k + 2) + 1, 0, 0, 0⟩ [fm]⊢* ⟨0, 0 + 2 * (k + 3), 0, 1, 1⟩
    rw [show 2 * (k + 2) + 1 = k + k + 5 from by ring]
    step fm; step fm; step fm
    rw [show k + k + 5 + 2 = (0 + 2 * (k + 3)) + 1 from by ring]
    step fm; ring_nf; finish
  apply stepStar_stepPlus_stepPlus (drain (k + 3) 0 0)
  simp only [Nat.zero_add]
  apply stepStar_stepPlus_stepPlus (phase_mid_odd (k + 3))
  rw [show 2 * (k + 3) + 2 = 2 * (k + 2) + 4 from by ring]
  exact tail_even (k + 2)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 8, 0, 0, 0⟩) (by execute fm 211)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a b, q = ⟨a, b, 0, 0, 0⟩ ∧ a ≥ 2 ∧ b ≥ 4)
  · intro c ⟨a, b, hq, ha, hb⟩; subst hq
    rcases (show a = 2 ∨ a ≥ 3 from by omega) with rfl | ha3
    · rcases Nat.even_or_odd b with ⟨K, hK⟩ | ⟨K, hK⟩
      · rw [show K + K = 2 * K from by ring] at hK; subst hK
        obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
        exact ⟨⟨k + 2, k + 6, 0, 0, 0⟩, ⟨k + 2, k + 6, rfl, by omega, by omega⟩, even_trans⟩
      · subst hK
        obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
        exact ⟨⟨k + 2, k + 7, 0, 0, 0⟩, ⟨k + 2, k + 7, rfl, by omega, by omega⟩, odd_trans⟩
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
      exact ⟨⟨a' + 2, b + 2, 0, 0, 0⟩, ⟨a' + 2, b + 2, rfl, by omega, by omega⟩, nine_step⟩
  · exact ⟨4, 8, rfl, by omega, by omega⟩
