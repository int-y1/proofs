import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1657: [77/15, 4/3, 27/14, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1
 2 -1  0  0  0
-1  3  0 -1  0
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1657

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · simp; exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    rw [show C + (k + 1) = (C + 1) + k from by ring]
    exact ih A (C + 1)

theorem r2_chain : ∀ k, ∀ A D E,
    ⟨A, k, 0, D, E⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, D, E⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · simp; exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (A + 2) D E)
    ring_nf; finish

theorem interleave : ∀ M, ∀ A B C D E,
    3 * C + D = M → A ≥ C + D →
    ⟨A, B + 1, C, D, E⟩ [fm]⊢* ⟨A + 2 * B + 2 + 3 * C + 5 * D, 0, 0, 0, E + C⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih; intro A B C D E hM hA
  rcases C with _ | C
  · rcases D with _ | D
    · simp
      have := r2_chain (B + 1) A 0 E
      rw [show A + 2 * (B + 1) = A + 2 * B + 2 from by ring] at this
      exact this
    · have phase1 := r2_chain (B + 1) A (D + 1) E
      rw [show A + 2 * (B + 1) = A + 2 * B + 2 from by ring] at phase1
      apply stepStar_trans phase1
      rw [show A + 2 * B + 2 = (A + 2 * B + 1) + 1 from by ring, show D + 1 = D + 1 from rfl]
      step fm
      have hlt : 3 * 0 + D < M := by omega
      have hA' : A + 2 * B + 1 ≥ 0 + D := by omega
      have := ih (3 * 0 + D) hlt (A + 2 * B + 1) 2 0 D E rfl hA'
      rw [show (A + 2 * B + 1) + 2 * 2 + 2 + 3 * 0 + 5 * D =
            A + 2 * B + 2 + 3 * 0 + 5 * (D + 1) from by ring,
          show E + 0 = E + 0 from rfl] at this
      exact this
  · rcases B with _ | B
    · obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
      show ⟨A' + 1, 0 + 1, C + 1, D, E⟩ [fm]⊢*
        ⟨A' + 1 + 2 * 0 + 2 + 3 * (C + 1) + 5 * D, 0, 0, 0, E + (C + 1)⟩
      rw [show (C + 1 : ℕ) = C + 1 from rfl]
      step fm
      rw [show D + 1 = D + 1 from rfl]
      step fm
      have hlt : 3 * C + D < M := by omega
      have hA' : A' ≥ C + D := by omega
      have h := ih (3 * C + D) hlt A' 2 C D (E + 1) rfl hA'
      rw [show A' + 2 * 2 + 2 + 3 * C + 5 * D =
            A' + 1 + 2 * 0 + 2 + 3 * (C + 1) + 5 * D from by ring,
          show E + 1 + C = E + (C + 1) from by ring,
          show (2 : ℕ) + 1 = 3 from by ring] at h
      exact h
    · show ⟨A, (B + 1) + 1, C + 1, D, E⟩ [fm]⊢*
        ⟨A + 2 * (B + 1) + 2 + 3 * (C + 1) + 5 * D, 0, 0, 0, E + (C + 1)⟩
      rw [show (B + 1) + 1 = (B + 1) + 1 from rfl, show (C + 1 : ℕ) = C + 1 from rfl]
      step fm
      have hlt : 3 * C + (D + 1) < M := by omega
      have hA' : A ≥ C + (D + 1) := by omega
      have h := ih (3 * C + (D + 1)) hlt A B C (D + 1) (E + 1) rfl hA'
      rw [show A + 2 * B + 2 + 3 * C + 5 * (D + 1) =
            A + 2 * (B + 1) + 2 + 3 * (C + 1) + 5 * D from by ring,
          show E + 1 + C = E + (C + 1) from by ring] at h
      exact h

theorem main_trans (a n : ℕ) :
    ⟨a + n + 2, 0, n + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * n + 6, 0, n + 2, 0, 0⟩ := by
  have p1 : ⟨a + n + 2, 0, n + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + n + 1, 1, n + 1, 0, 1⟩ := by
    rw [show a + n + 2 = (a + n + 1) + 1 from by ring,
        show n + 1 = 0 + (n + 1) from by ring]
    step fm; finish
  have p2 : ⟨a + n + 1, 1, n + 1, 0, 1⟩ [fm]⊢* ⟨a + n + 1, 0, n, 1, 2⟩ := by
    rw [show n + 1 = n + 1 from rfl]
    step fm; ring_nf; finish
  have p3 : ⟨a + n + 1, 0, n, 1, 2⟩ [fm]⊢* ⟨a + n, 3, n, 0, 2⟩ := by
    rw [show a + n + 1 = (a + n) + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    step fm; ring_nf; finish
  have p4 : ⟨a + n, 3, n, 0, 2⟩ [fm]⊢* ⟨a + 4 * n + 6, 0, 0, 0, n + 2⟩ := by
    rw [show (3 : ℕ) = 2 + 1 from by ring]
    have h := interleave (3 * n + 0) (a + n) 2 n 0 2 (by ring) (by omega)
    rw [show (a + n) + 2 * 2 + 2 + 3 * n + 5 * 0 = a + 4 * n + 6 from by ring,
        show 2 + n = n + 2 from by ring] at h
    exact h
  have p5 : ⟨a + 4 * n + 6, 0, 0, 0, n + 2⟩ [fm]⊢* ⟨a + 4 * n + 6, 0, n + 2, 0, 0⟩ := by
    have h := r4_chain (n + 2) (a + 4 * n + 6) 0
    rw [show 0 + (n + 2) = n + 2 from by ring] at h
    exact h
  exact stepPlus_stepStar_stepPlus p1
    (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4 p5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a + n + 2, 0, n + 1, 0, 0⟩) ⟨0, 0⟩
  intro ⟨a, n⟩
  refine ⟨⟨a + 3 * n + 3, n + 1⟩, ?_⟩
  show ⟨a + n + 2, 0, n + 1, 0, 0⟩ [fm]⊢⁺
    ⟨(a + 3 * n + 3) + (n + 1) + 2, 0, (n + 1) + 1, 0, 0⟩
  rw [show (a + 3 * n + 3) + (n + 1) + 2 = a + 4 * n + 6 from by ring]
  exact main_trans a n

end Sz22_2003_unofficial_1657
