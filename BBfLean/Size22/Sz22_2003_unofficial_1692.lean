import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1692: [77/15, 9/14, 484/3, 5/11, 3/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 2 -1  0  0  2
 0  0  1  0 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1692

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih A (C + 1))
    rw [show C + 1 + k = C + (k + 1) from by ring]; finish

theorem r112_chain : ∀ k, ∀ A C D E,
    ⟨A + k, 2, C + 2 * k, D, E⟩ [fm]⊢* ⟨A, 2, C, D + k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k) + 1 + 1 from by ring]
    step fm; step fm
    rw [show (A + k) + 1 = (A + k) + 1 from rfl]
    step fm
    apply stepStar_trans (ih A C (D + 1) (E + 2))
    rw [show D + 1 + k = D + (k + 1) from by ring,
        show E + 2 + 2 * k = E + 2 * (k + 1) from by ring]; finish

theorem drain : ∀ M, ∀ A B D E, 3 * D + B = M →
    ⟨A, B + 1, 0, D, E⟩ [fm]⊢* ⟨A + 2 * B + 2 + 3 * D, 0, 0, 0, E + 2 * B + 2 + 4 * D⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih; intro A B D E hM
  rcases D with _ | D
  · rcases B with _ | B
    · step fm; ring_nf; finish
    · rw [show (B + 1) + 1 = (B + 1) + 1 from rfl]
      step fm
      have := ih (3 * 0 + B) (by omega) (A + 2) B 0 (E + 2) rfl
      rw [show (A + 2) + 2 * B + 2 + 3 * 0 = A + 2 * (B + 1) + 2 + 3 * 0 from by ring,
          show E + 2 + 2 * B + 2 + 4 * 0 = E + 2 * (B + 1) + 2 + 4 * 0 from by ring] at this
      exact this
  · rcases A with _ | A
    · rcases B with _ | B
      · step fm
        rw [show D + 1 = D + 1 from rfl]
        step fm
        have := ih (3 * D + 1) (by omega) 1 1 D (E + 2) (by ring)
        rw [show 1 + 2 * 1 + 2 + 3 * D = 0 + 2 * 0 + 2 + 3 * (D + 1) from by ring,
            show E + 2 + 2 * 1 + 2 + 4 * D = E + 2 * 0 + 2 + 4 * (D + 1) from by ring] at this
        exact this
      · rw [show (B + 1) + 1 = (B + 1) + 1 from rfl]
        step fm
        have := ih (3 * (D + 1) + B) (by omega) 2 B (D + 1) (E + 2) (by ring)
        rw [show 2 + 2 * B + 2 + 3 * (D + 1) = 0 + 2 * (B + 1) + 2 + 3 * (D + 1) from by ring,
            show E + 2 + 2 * B + 2 + 4 * (D + 1) = E + 2 * (B + 1) + 2 + 4 * (D + 1) from by ring] at this
        exact this
    · rw [show A + 1 = A + 1 from rfl, show D + 1 = D + 1 from rfl]
      step fm
      have := ih (3 * D + (B + 2)) (by omega) A (B + 2) D E (by ring)
      rw [show A + 2 * (B + 2) + 2 + 3 * D = (A + 1) + 2 * B + 2 + 3 * (D + 1) from by ring,
          show E + 2 * (B + 2) + 2 + 4 * D = E + 2 * B + 2 + 4 * (D + 1) from by ring] at this
      exact this

theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, 0, 0, 2 * n⟩ [fm]⊢⁺ ⟨3 * n + 2, 0, 0, 0, 6 * n + 2⟩ := by
  rcases n with _ | n
  · step fm; step fm; finish
  · have p1 : ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢*
        ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ := by
      have := r4_chain (2 * n + 2) (n + 2) 0
      simp only [Nat.zero_add] at this; exact this
    have p2 : ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ [fm]⊢⁺
        ⟨n + 1, 1, 2 * n + 2, 0, 0⟩ := by
      rw [show n + 2 = (n + 1) + 1 from by ring]
      step fm; finish
    have p3 : ⟨n + 1, 1, 2 * n + 2, 0, 0⟩ [fm]⊢*
        ⟨n + 1, 0, 2 * n + 1, 1, 1⟩ := by
      rw [show (1 : ℕ) = 0 + 1 from rfl,
          show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
      step fm; ring_nf; finish
    have p4 : ⟨n + 1, 0, 2 * n + 1, 1, 1⟩ [fm]⊢*
        ⟨n, 2, 2 * n + 1, 0, 1⟩ := by
      rw [show n + 1 = n + 1 from rfl,
          show (1 : ℕ) = 0 + 1 from rfl]
      step fm; ring_nf; finish
    have p5 : ⟨n, 2, 2 * n + 1, 0, 1⟩ [fm]⊢*
        ⟨0, 2, 1, n, 2 * n + 1⟩ := by
      have := r112_chain n 0 1 0 1
      simp only [Nat.zero_add] at this
      rw [show 1 + 2 * n = 2 * n + 1 from by ring] at this
      exact this
    have p6 : ⟨0, 2, 1, n, 2 * n + 1⟩ [fm]⊢*
        ⟨0, 1, 0, n + 1, 2 * n + 2⟩ := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
      step fm; ring_nf; finish
    have p7 : ⟨0, 1, 0, n + 1, 2 * n + 2⟩ [fm]⊢*
        ⟨2, 0, 0, n + 1, 2 * n + 4⟩ := by
      rw [show (1 : ℕ) = 0 + 1 from rfl]
      step fm; ring_nf; finish
    have p8 : ⟨2, 0, 0, n + 1, 2 * n + 4⟩ [fm]⊢*
        ⟨1, 2, 0, n, 2 * n + 4⟩ := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, show n + 1 = n + 1 from rfl]
      step fm; ring_nf; finish
    have p9 : ⟨1, 2, 0, n, 2 * n + 4⟩ [fm]⊢*
        ⟨3 * n + 5, 0, 0, 0, 6 * n + 8⟩ := by
      rw [show (2 : ℕ) = 1 + 1 from rfl]
      have := drain (3 * n + 1) 1 1 n (2 * n + 4) (by ring)
      rw [show 1 + 2 * 1 + 2 + 3 * n = 3 * n + 5 from by ring,
          show 2 * n + 4 + 2 * 1 + 2 + 4 * n = 6 * n + 8 from by ring] at this
      exact this
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring,
        show 3 * (n + 1) + 2 = 3 * n + 5 from by ring,
        show 6 * (n + 1) + 2 = 6 * n + 8 from by ring]
    exact stepStar_stepPlus_stepPlus p1
      (stepPlus_stepStar_stepPlus p2
        (stepStar_trans p3 (stepStar_trans p4 (stepStar_trans p5
          (stepStar_trans p6 (stepStar_trans p7 (stepStar_trans p8 p9)))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0, 2 * n⟩) 1
  intro n
  refine ⟨3 * n + 1, ?_⟩
  show ⟨n + 1, 0, 0, 0, 2 * n⟩ [fm]⊢⁺
    ⟨3 * n + 1 + 1, 0, 0, 0, 2 * (3 * n + 1)⟩
  rw [show 3 * n + 1 + 1 = 3 * n + 2 from by ring,
      show 2 * (3 * n + 1) = 6 * n + 2 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1692
