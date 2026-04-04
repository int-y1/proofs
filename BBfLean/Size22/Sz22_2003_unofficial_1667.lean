import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1667: [77/15, 56/3, 9/22, 5/7, 3/2]

Vector representation:
```
 0 -1 -1  1  1
 3 -1  0  1  0
-1  2  0  0 -1
 0  0  1 -1  0
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1667

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+3, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k A C, ⟨A, (0 : ℕ), C, k, (0 : ℕ)⟩ [fm]⊢* ⟨A, (0 : ℕ), C + k, 0, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · step fm
    apply stepStar_trans (ih A (C + 1))
    ring_nf; finish

theorem r3r1r1_loop : ∀ K, ∀ A D E,
    ⟨A + K, (0 : ℕ), 2 * K, D, E + 1⟩ [fm]⊢* ⟨A, (0 : ℕ), 0, D + 2 * K, E + K + 1⟩ := by
  intro K; induction' K with K ih <;> intro A D E
  · exists 0
  · rw [show A + (K + 1) = (A + K) + 1 from by ring,
        show 2 * (K + 1) = (2 * K) + 1 + 1 from by ring,
        show E + 1 = E + 1 from rfl]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show (2 * K) + 1 = (2 * K) + 1 from rfl]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show D + 1 + 1 = D + 2 from by ring,
        show E + 1 + 1 = (E + 1) + 1 from by ring]
    apply stepStar_trans (ih A (D + 2) (E + 1))
    ring_nf; finish

theorem r3r2r2_loop : ∀ K, ∀ A D E,
    ⟨A + 1, (0 : ℕ), 0, D, E + K⟩ [fm]⊢* ⟨A + 5 * K + 1, (0 : ℕ), 0, D + 2 * K, E⟩ := by
  intro K; induction' K with K ih <;> intro A D E
  · exists 0
  · rw [show E + (K + 1) = (E + K) + 1 from by ring]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show A + 3 + 3 = (A + 5) + 1 from by ring,
        show D + 1 + 1 = D + 2 from by ring]
    apply stepStar_trans (ih (A + 5) (D + 2) E)
    ring_nf; finish

theorem main_trans (m : ℕ) :
    ⟨4 * m + 3, (0 : ℕ), 2 * m + 1, 0, 0⟩ [fm]⊢⁺
    ⟨8 * m + 7, (0 : ℕ), 4 * m + 3, 0, 0⟩ := by
  have p1 : ⟨4 * m + 3, (0 : ℕ), 2 * m + 1, 0, 0⟩ [fm]⊢⁺
            ⟨4 * m + 2, (0 : ℕ), 2 * m, 1, 1⟩ := by
    rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring,
        show 2 * m + 1 = (2 * m) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm; finish
  have p2 : ⟨4 * m + 2, (0 : ℕ), 2 * m, 1, 1⟩ [fm]⊢*
            ⟨3 * m + 2, (0 : ℕ), 0, 2 * m + 1, m + 1⟩ := by
    rw [show 4 * m + 2 = (3 * m + 2) + m from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    have h := r3r1r1_loop m (3 * m + 2) 1 0
    rw [show 1 + 2 * m = 2 * m + 1 from by ring,
        show 0 + m + 1 = m + 1 from by ring] at h
    exact h
  have p3 : ⟨3 * m + 2, (0 : ℕ), 0, 2 * m + 1, m + 1⟩ [fm]⊢*
            ⟨8 * m + 7, (0 : ℕ), 0, 4 * m + 3, 0⟩ := by
    rw [show 3 * m + 2 = (3 * m + 1) + 1 from by ring,
        show m + 1 = 0 + (m + 1) from by ring]
    have h := r3r2r2_loop (m + 1) (3 * m + 1) (2 * m + 1) 0
    rw [show (3 * m + 1) + 5 * (m + 1) + 1 = 8 * m + 7 from by ring,
        show (2 * m + 1) + 2 * (m + 1) = 4 * m + 3 from by ring] at h
    exact h
  have p4 : ⟨8 * m + 7, (0 : ℕ), 0, 4 * m + 3, 0⟩ [fm]⊢*
            ⟨8 * m + 7, (0 : ℕ), 4 * m + 3, 0, 0⟩ := by
    have h := r4_chain (4 * m + 3) (8 * m + 7) 0
    simp at h; exact h
  exact stepPlus_stepStar_stepPlus p1 (stepStar_trans p2 (stepStar_trans p3 p4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 1, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨4 * m + 3, 0, 2 * m + 1, 0, 0⟩) 0
  intro m
  refine ⟨2 * m + 1, ?_⟩
  show ⟨4 * m + 3, (0 : ℕ), 2 * m + 1, 0, 0⟩ [fm]⊢⁺
    ⟨4 * (2 * m + 1) + 3, (0 : ℕ), 2 * (2 * m + 1) + 1, 0, 0⟩
  rw [show 4 * (2 * m + 1) + 3 = 8 * m + 7 from by ring,
      show 2 * (2 * m + 1) + 1 = 4 * m + 3 from by ring]
  exact main_trans m

end Sz22_2003_unofficial_1667
