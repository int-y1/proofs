import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1666: [77/15, 52/3, 9/91, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1  0
 2 -1  0  0  0  1
 0  2  0 -1  0 -1
 0  0  1  0 -1  0
-1  1  0  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1666

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ A C F,
    ⟨A, 0, C, 0, k, F⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0, F⟩ := by
  intro k; induction' k with k ih <;> intro A C F
  · simp; exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    rw [show C + (k + 1) = (C + 1) + k from by ring]
    exact ih A (C + 1) F

theorem r2_chain : ∀ k, ∀ A D E F,
    ⟨A, k, 0, D, E, F⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, D, E, F + k⟩ := by
  intro k; induction' k with k ih <;> intro A D E F
  · simp; exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (A + 2) D E (F + 1))
    ring_nf; finish

theorem interleave : ∀ M, ∀ A B C D E F,
    2 * C + D = M → 2 * F + B ≥ C →
    ⟨A, B + 1, C, D, E, F⟩ [fm]⊢*
      ⟨A + 2 * C + 2 * B + 2 + 4 * D, 0, 0, 0, E + C, F + B + 1 + D⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih; intro A B C D E F hM hFBC
  rcases C with _ | C
  · -- C = 0
    rcases D with _ | D
    · -- C = 0, D = 0: just R2 chain
      simp
      have := r2_chain (B + 1) A 0 E F
      rw [show A + 2 * (B + 1) = A + 2 * B + 2 from by ring,
          show F + (B + 1) = F + B + 1 from by ring] at this
      exact this
    · -- C = 0, D >= 1: R2 chain then R3, recurse
      have phase1 := r2_chain (B + 1) A (D + 1) E F
      rw [show A + 2 * (B + 1) = A + 2 * B + 2 from by ring,
          show F + (B + 1) = F + B + 1 from by ring] at phase1
      apply stepStar_trans phase1
      rw [show D + 1 = D + 1 from rfl,
          show F + B + 1 = (F + B) + 1 from by ring]
      step fm
      have hlt : 2 * 0 + D < M := by omega
      have hFBC' : 2 * (F + B) + 1 ≥ 0 := by omega
      have h := ih (2 * 0 + D) hlt (A + 2 * B + 2) 1 0 D E (F + B) rfl hFBC'
      rw [show (A + 2 * B + 2) + 2 * 0 + 2 * 1 + 2 + 4 * D =
            A + 2 * 0 + 2 * B + 2 + 4 * (D + 1) from by ring,
          show E + 0 = E + 0 from rfl,
          show (F + B) + 1 + 1 + D = F + B + 1 + (D + 1) from by ring] at h
      exact h
  · -- C >= 1
    rcases B with _ | B
    · -- C >= 1, B = 0: R1 then R3, recurse
      -- From hypothesis: 2 * F + 0 >= C + 1, so F >= 1
      rcases F with _ | F
      · omega
      · show ⟨A, 0 + 1, C + 1, D, E, F + 1⟩ [fm]⊢*
          ⟨A + 2 * (C + 1) + 2 * 0 + 2 + 4 * D, 0, 0, 0, E + (C + 1), F + 1 + 0 + 1 + D⟩
        rw [show (C + 1 : ℕ) = C + 1 from rfl]
        step fm
        rw [show D + 1 = D + 1 from rfl]
        step fm
        have hlt : 2 * C + D < M := by omega
        have hFBC' : 2 * F + 1 ≥ C := by omega
        have h := ih (2 * C + D) hlt A 1 C D (E + 1) F rfl hFBC'
        rw [show A + 2 * C + 2 * 1 + 2 + 4 * D =
              A + 2 * (C + 1) + 2 * 0 + 2 + 4 * D from by ring,
            show (E + 1) + C = E + (C + 1) from by ring,
            show F + 1 + 1 + D = F + 1 + 0 + 1 + D from by ring] at h
        exact h
    · -- C >= 1, B >= 1: R1, recurse
      show ⟨A, (B + 1) + 1, C + 1, D, E, F⟩ [fm]⊢*
        ⟨A + 2 * (C + 1) + 2 * (B + 1) + 2 + 4 * D, 0, 0, 0, E + (C + 1),
         F + (B + 1) + 1 + D⟩
      rw [show (C + 1 : ℕ) = C + 1 from rfl]
      step fm
      have hlt : 2 * C + (D + 1) < M := by omega
      have hFBC' : 2 * F + B ≥ C := by omega
      have h := ih (2 * C + (D + 1)) hlt A B C (D + 1) (E + 1) F rfl hFBC'
      rw [show A + 2 * C + 2 * B + 2 + 4 * (D + 1) =
            A + 2 * (C + 1) + 2 * (B + 1) + 2 + 4 * D from by ring,
          show (E + 1) + C = E + (C + 1) from by ring,
          show F + B + 1 + (D + 1) = F + (B + 1) + 1 + D from by ring] at h
      exact h

theorem main_trans (n : ℕ) :
    ⟨n * n + 1, 0, 0, 0, n, n⟩ [fm]⊢⁺ ⟨(n + 1) * (n + 1) + 1, 0, 0, 0, n + 1, n + 1⟩ := by
  -- Phase 1: R4 chain drains e to c
  have p1 : ⟨n * n + 1, 0, 0, 0, n, n⟩ [fm]⊢*
      ⟨n * n + 1, 0, n, 0, 0, n⟩ := by
    have h := r4_chain n (n * n + 1) 0 n
    rw [show 0 + n = n from by ring] at h
    exact h
  -- Phase 2: R5 step
  have p2 : ⟨n * n + 1, 0, n, 0, 0, n⟩ [fm]⊢⁺
      ⟨n * n, 1, n, 0, 1, n⟩ := by
    rw [show n * n + 1 = (n * n) + 1 from by ring]
    step fm; finish
  -- Phase 3: interleave
  have p3 : ⟨n * n, 1, n, 0, 1, n⟩ [fm]⊢*
      ⟨n * n + 2 * n + 2, 0, 0, 0, 1 + n, n + 0 + 1 + 0⟩ := by
    exact interleave (2 * n) (n * n) 0 n 0 1 n rfl (by omega)
  -- Rewrite to target form
  rw [show n * n + 2 * n + 2 = (n + 1) * (n + 1) + 1 from by ring,
      show (1 : ℕ) + n = n + 1 from by ring,
      show n + 0 + 1 + 0 = n + 1 from by ring] at p3
  exact stepStar_stepPlus_stepPlus p1 (stepPlus_stepStar_stepPlus p2 p3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n * n + 1, 0, 0, 0, n, n⟩) 1
  intro n
  exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1666
