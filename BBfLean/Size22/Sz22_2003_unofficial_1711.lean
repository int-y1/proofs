import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1711: [77/15, 9/91, 52/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1  0
 0  2  0 -1  0 -1
 2 -1  0  0  0  1
 0  0  1  0 -1  0
-1  1  0  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1711

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ A C F,
    ⟨A, 0, C, 0, k, F⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0, F⟩ := by
  intro k; induction' k with k ih <;> intro A C F
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih A (C + 1) F)
    rw [show C + 1 + k = C + (k + 1) from by ring]; finish

theorem r3_chain : ∀ k, ∀ A E F,
    ⟨A, k, 0, 0, E, F⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, 0, E, F + k⟩ := by
  intro k; induction' k with k ih <;> intro A E F
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (A + 2) E (F + 1))
    rw [show A + 2 + 2 * k = A + 2 * (k + 1) from by ring,
        show F + 1 + k = F + (k + 1) from by ring]; finish

theorem combined_drain : ∀ M, ∀ X B C D E F, 2 * C + D = M →
    (B + D ≥ 1 ∨ C = 0) →
    ⟨X, B, C, D, E, F + C + D⟩ [fm]⊢* ⟨X, B + C + 2 * D, 0, 0, E + C, F⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih; intro X B C D E F hM hpre
  rcases C with _ | C
  · rcases D with _ | D
    · simp; exists 0
    · rw [show D + 1 = D + 1 from rfl,
          show F + 0 + (D + 1) = (F + 0 + D) + 1 from by ring]
      step fm
      have := ih (2 * 0 + D) (by omega) X (B + 2) 0 D E F (by ring) (by left; omega)
      rw [show B + 2 + 0 + 2 * D = B + 0 + 2 * (D + 1) from by ring,
          show E + 0 = E + 0 from rfl] at this
      exact this
  · rcases D with _ | D
    · rcases B with _ | B
      · simp at hpre
      · rw [show B + 1 = B + 1 from rfl, show C + 1 = C + 1 from rfl]
        step fm
        have := ih (2 * C + 1) (by omega) X B C 1 (E + 1) F (by ring) (by left; omega)
        rw [show B + C + 2 * 1 = (B + 1) + (C + 1) + 2 * 0 from by ring,
            show E + 1 + C = E + (C + 1) from by ring,
            show F + C + 1 = F + (C + 1) + 0 from by ring] at this
        exact this
    · rcases B with _ | B
      · rw [show D + 1 = D + 1 from rfl,
            show F + (C + 1) + (D + 1) = (F + (C + 1) + D) + 1 from by ring]
        step fm
        have := ih (2 * (C + 1) + D) (by omega) X 2 (C + 1) D E F (by ring)
          (by left; omega)
        rw [show 2 + (C + 1) + 2 * D = 0 + (C + 1) + 2 * (D + 1) from by ring,
            show E + (C + 1) = E + (C + 1) from rfl] at this
        exact this
      · rw [show B + 1 = B + 1 from rfl, show C + 1 = C + 1 from rfl]
        step fm
        have := ih (2 * C + (D + 2)) (by omega) X B C (D + 2) (E + 1) F (by ring)
          (by left; omega)
        rw [show B + C + 2 * (D + 2) = (B + 1) + (C + 1) + 2 * (D + 1) from by ring,
            show E + 1 + C = E + (C + 1) from by ring,
            show F + C + (D + 2) = F + (C + 1) + (D + 1) from by ring] at this
        exact this

theorem main_trans (n : ℕ) :
    ⟨n * n + 2 * n + 2, 0, n + 1, 0, 0, n + 1⟩ [fm]⊢⁺
    ⟨n * n + 4 * n + 5, 0, n + 2, 0, 0, n + 2⟩ := by
  have p1 : ⟨n * n + 2 * n + 2, 0, n + 1, 0, 0, n + 1⟩ [fm]⊢⁺
      ⟨n * n + 2 * n + 1, 1, n + 1, 0, 1, n + 1⟩ := by
    rw [show n * n + 2 * n + 2 = (n * n + 2 * n + 1) + 1 from by ring,
        show n + 1 = 0 + (n + 1) from by ring]
    step fm; ring_nf; finish
  have p2 : ⟨n * n + 2 * n + 1, 1, n + 1, 0, 1, n + 1⟩ [fm]⊢*
      ⟨n * n + 2 * n + 1, 0, n, 1, 2, n + 1⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, show n + 1 = n + 1 from rfl]
    step fm; ring_nf; finish
  have p3 : ⟨n * n + 2 * n + 1, 0, n, 1, 2, n + 1⟩ [fm]⊢*
      ⟨n * n + 2 * n + 1, 2, n, 0, 2, n⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, show n + 1 = n + 1 from rfl]
    step fm; ring_nf; finish
  have p4 : ⟨n * n + 2 * n + 1, 2, n, 0, 2, n⟩ [fm]⊢*
      ⟨n * n + 2 * n + 1, n + 2, 0, 0, n + 2, 0⟩ := by
    have key := combined_drain (2 * n + 0) (n * n + 2 * n + 1) 2 n 0 2 0 (by ring)
      (by left; omega)
    simp only [Nat.zero_add, Nat.add_zero] at key
    rw [show 2 + n = n + 2 from by ring] at key
    exact key
  have p5 : ⟨n * n + 2 * n + 1, n + 2, 0, 0, n + 2, 0⟩ [fm]⊢*
      ⟨n * n + 4 * n + 5, 0, 0, 0, n + 2, n + 2⟩ := by
    have := r3_chain (n + 2) (n * n + 2 * n + 1) (n + 2) 0
    rw [show n * n + 2 * n + 1 + 2 * (n + 2) = n * n + 4 * n + 5 from by ring,
        show 0 + (n + 2) = n + 2 from by ring] at this
    exact this
  have p6 : ⟨n * n + 4 * n + 5, 0, 0, 0, n + 2, n + 2⟩ [fm]⊢*
      ⟨n * n + 4 * n + 5, 0, n + 2, 0, 0, n + 2⟩ := by
    have := r4_chain (n + 2) (n * n + 4 * n + 5) 0 (n + 2)
    simp only [Nat.zero_add] at this; exact this
  exact stepPlus_stepStar_stepPlus p1
    (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4 (stepStar_trans p5 p6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n * n + 2 * n + 2, 0, n + 1, 0, 0, n + 1⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨n * n + 2 * n + 2, 0, n + 1, 0, 0, n + 1⟩ [fm]⊢⁺
    ⟨(n + 1) * (n + 1) + 2 * (n + 1) + 2, 0, (n + 1) + 1, 0, 0, (n + 1) + 1⟩
  rw [show (n + 1) * (n + 1) + 2 * (n + 1) + 2 = n * n + 4 * n + 5 from by ring,
      show (n + 1) + 1 = n + 2 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1711
