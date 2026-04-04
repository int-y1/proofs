import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1693: [77/15, 9/14, 8/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 3 -1  0  0  0
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1693

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih A (C + 1))
    rw [show C + 1 + k = C + (k + 1) from by omega]; finish

theorem r2_chain : ∀ D, ∀ A B E,
    ⟨A + D, B, 0, D, E⟩ [fm]⊢* ⟨A, B + 2 * D, 0, 0, E⟩ := by
  intro D; induction' D with D ih <;> intro A B E
  · simp; exists 0
  · rw [show A + (D + 1) = (A + D) + 1 from by omega,
        show D + 1 = D + 1 from rfl]
    step fm
    apply stepStar_trans (ih A (B + 2) E)
    rw [show B + 2 + 2 * D = B + 2 * (D + 1) from by omega]; finish

theorem r3_chain : ∀ B, ∀ A E,
    ⟨A, B, 0, 0, E⟩ [fm]⊢* ⟨A + 3 * B, 0, 0, 0, E⟩ := by
  intro B; induction' B with B ih <;> intro A E
  · simp; exists 0
  · rw [show B + 1 = B + 1 from rfl]
    step fm
    apply stepStar_trans (ih (A + 3) E)
    rw [show A + 3 + 3 * B = A + 3 * (B + 1) from by omega]; finish

theorem drain : ∀ C, ∀ F B D E, B ≥ 1 →
    ⟨F + C + D, B, C, D, E⟩ [fm]⊢* ⟨F, B + C + 2 * D, 0, 0, E + C⟩ := by
  intro C; induction' C with C ih <;> intro F B D E hB
  · -- C = 0: R2 chain
    simp
    have h := r2_chain D F B E
    rw [show B + 2 * D = B + 0 + 2 * D from by omega] at h
    exact h
  · -- C + 1: R1 step
    rw [show B = (B - 1) + 1 from by omega,
        show C + 1 = C + 1 from rfl]
    step fm
    -- State: (F+C+1+D, B-1, C, D+1, E+1)
    rcases B, hB with ⟨_ | _ | B', _⟩
    · omega
    · -- B = 1, so B-1 = 0
      simp
      -- State: (F+C+1+D, 0, C, D+1, E+1). R2 fires.
      rw [show F + (C + 1) + D = (F + C + D) + 1 from by omega,
          show D + 1 = D + 1 from rfl]
      step fm
      -- State: (F+C+D, 2, C, D, E+1). Apply IH with B=2.
      have hih := ih F 2 D (E + 1) (by omega)
      rw [show 2 + C + 2 * D = 1 + (C + 1) + 2 * D from by omega,
          show E + 1 + C = E + (C + 1) from by omega] at hih
      exact hih
    · -- B = B' + 2, so B-1 = B'+1 >= 1
      simp
      -- State: (F+C+1+D, B'+1, C, D+1, E+1). Apply IH with B=B'+1.
      rw [show F + (C + 1) + D = F + C + (D + 1) from by omega]
      have hih := ih F (B' + 1) (D + 1) (E + 1) (by omega)
      rw [show B' + 1 + C + 2 * (D + 1) = (B' + 2) + (C + 1) + 2 * D from by omega,
          show E + 1 + C = E + (C + 1) from by omega] at hih
      exact hih

theorem main_trans (n : ℕ) :
    ⟨n * n + n + 1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n * n + 3 * n + 3, 0, 0, 0, n + 1⟩ := by
  have p1 : ⟨n * n + n + 1, 0, 0, 0, n⟩ [fm]⊢*
      ⟨n * n + n + 1, 0, n, 0, 0⟩ := by
    have := r4_chain n (n * n + n + 1) 0
    simp only [Nat.zero_add] at this; exact this
  have p2 : ⟨n * n + n + 1, 0, n, 0, 0⟩ [fm]⊢⁺
      ⟨n * n + n, 1, n, 0, 1⟩ := by
    rw [show n * n + n + 1 = (n * n + n) + 1 from by omega]
    step fm; finish
  have p3 : ⟨n * n + n, 1, n, 0, 1⟩ [fm]⊢*
      ⟨n * n, 1 + n, 0, 0, 1 + n⟩ := by
    have hd := drain n (n * n) 1 0 1 (by omega)
    simp only [Nat.add_zero, Nat.mul_zero] at hd; exact hd
  have p4 : ⟨n * n, 1 + n, 0, 0, 1 + n⟩ [fm]⊢*
      ⟨n * n + 3 * n + 3, 0, 0, 0, n + 1⟩ := by
    rw [show 1 + n = n + 1 from by omega]
    have := r3_chain (n + 1) (n * n) (n + 1)
    rw [show n * n + 3 * (n + 1) = n * n + 3 * n + 3 from by omega] at this
    exact this
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus p2 (stepStar_trans p3 p4))

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n * n + n + 1, 0, 0, 0, n⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨n * n + n + 1, 0, 0, 0, n⟩ [fm]⊢⁺
    ⟨(n + 1) * (n + 1) + (n + 1) + 1, 0, 0, 0, n + 1⟩
  rw [show (n + 1) * (n + 1) + (n + 1) + 1 = n * n + 3 * n + 3 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1693
