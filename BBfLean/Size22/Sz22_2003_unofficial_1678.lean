import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1678: [77/15, 9/14, 2/3, 5/11, 495/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 1 -1  0  0  0
 0  0  1  0 -1
-1  2  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1678

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e+1⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, (0 : ℕ), 0⟩ := by
  intro k; induction k with
  | zero => intro A C; simp; exists 0
  | succ k ih =>
    intro A C; step fm
    rw [show C + (k + 1) = (C + 1) + k from by ring]
    exact ih A (C + 1)

theorem b_to_a : ∀ k, ∀ A E,
    ⟨A, k, 0, 0, E⟩ [fm]⊢* ⟨A + k, 0, 0, (0 : ℕ), E⟩ := by
  intro k; induction k with
  | zero => intro A E; simp; exists 0
  | succ k ih =>
    intro A E; step fm
    apply stepStar_trans (ih (A + 1) E); ring_nf; finish

theorem r3r2_chain : ∀ K, ∀ B E,
    ⟨0, B + 1, 0, K, E⟩ [fm]⊢* ⟨0, B + 1 + K, 0, (0 : ℕ), E⟩ := by
  intro K; induction K with
  | zero => intro B E; simp; exists 0
  | succ K ih =>
    intro B E
    rw [show (K + 1 : ℕ) = K + 1 from rfl]
    step fm; step fm
    rw [show B + 1 + (K + 1) = (B + 1) + 1 + K from by ring]
    exact ih (B + 1) E

theorem r1r1r2_chain : ∀ K, ∀ A C D E,
    ⟨A + K, 2, C + 2 * K, D, E⟩ [fm]⊢* ⟨A, 2, C, D + K, E + 2 * K⟩ := by
  intro K; induction K with
  | zero => intro A C D E; simp; exists 0
  | succ K ih =>
    intro A C D E
    rw [show A + (K + 1) = (A + K) + 1 from by ring,
        show C + 2 * (K + 1) = (C + 2 * K + 1) + 1 from by ring]
    step fm
    rw [show (C + 2 * K + 1 : ℕ) = (C + 2 * K) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    rw [show (A + K + 1 : ℕ) = (A + K) + 1 from by ring,
        show D + 2 = (D + 1) + 1 from by ring]
    step fm
    rw [show D + (K + 1) = (D + 1) + K from by ring,
        show E + 2 * (K + 1) = (E + 2) + 2 * K from by ring]
    exact ih A C (D + 1) (E + 2)

theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 2 * n + 2, 0, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨n + 3, 0, 2 * n + 4, (0 : ℕ), 0⟩ := by
  have p1 : ⟨n + 2, 0, 2 * n + 2, 0, (0 : ℕ)⟩ [fm]⊢⁺
      ⟨n + 1, 2, 2 * n + 3, 0, (1 : ℕ)⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]
    step fm; finish
  have p2 : ⟨n + 1, 2, 2 * n + 3, 0, (1 : ℕ)⟩ [fm]⊢*
      ⟨0, 2, 1, n + 1, 2 * n + 3⟩ := by
    have h := r1r1r2_chain (n + 1) 0 1 0 1
    rw [show 1 + 2 * (n + 1) = 2 * n + 3 from by ring] at h
    simp at h; exact h
  have p3 : ⟨0, 2, 1, n + 1, 2 * n + 3⟩ [fm]⊢*
      ⟨0, 1, 0, n + 2, 2 * n + 4⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    step fm; ring_nf; finish
  have p4 : ⟨0, 1, 0, n + 2, 2 * n + 4⟩ [fm]⊢*
      ⟨1, 0, 0, n + 2, 2 * n + 4⟩ := by
    step fm; finish
  have p5 : ⟨1, 0, 0, n + 2, 2 * n + 4⟩ [fm]⊢*
      ⟨0, 2, 0, n + 1, 2 * n + 4⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]
    step fm; finish
  have p6 : ⟨0, 2, 0, n + 1, 2 * n + 4⟩ [fm]⊢*
      ⟨0, n + 3, 0, (0 : ℕ), 2 * n + 4⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    have h := r3r2_chain (n + 1) 1 (2 * n + 4)
    rw [show 1 + 1 + (n + 1) = n + 3 from by ring] at h
    exact h
  have p7 : ⟨0, n + 3, 0, 0, 2 * n + 4⟩ [fm]⊢*
      ⟨n + 3, 0, 0, (0 : ℕ), 2 * n + 4⟩ := by
    have h := b_to_a (n + 3) 0 (2 * n + 4)
    rw [show 0 + (n + 3) = n + 3 from by ring] at h
    exact h
  have p8 : ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ [fm]⊢*
      ⟨n + 3, 0, 2 * n + 4, (0 : ℕ), 0⟩ := by
    have h := e_to_c (2 * n + 4) (n + 3) 0
    rw [show 0 + (2 * n + 4) = 2 * n + 4 from by ring] at h
    exact h
  exact stepPlus_stepStar_stepPlus p1
    (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4
      (stepStar_trans p5 (stepStar_trans p6 (stepStar_trans p7 p8))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 2, 0, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 2 * n + 2, 0, 0⟩) 0
  intro n
  exists n + 1
  rw [show n + 1 + 2 = n + 3 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1678
