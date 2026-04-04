import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1668: [77/15, 6/7, 1/3, 125/2, 1/55, 3/5]

Vector representation:
```
 0 -1 -1  1  1
 1  1  0 -1  0
 0 -1  0  0  0
-1  0  3  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1668

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ A C E, ⟨A + k, (0 : ℕ), C, (0 : ℕ), E⟩ [fm]⊢* ⟨A, (0 : ℕ), C + 3 * k, (0 : ℕ), E⟩ := by
  intro k; induction' k with k ih <;> intro A C E
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih A (C + 3) E)
    ring_nf; finish

theorem r5_chain : ∀ k, ∀ C E, ⟨(0 : ℕ), (0 : ℕ), C + k, (0 : ℕ), E + k⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), C, (0 : ℕ), E⟩ := by
  intro k; induction' k with k ih <;> intro C E
  · exists 0
  · rw [show C + (k + 1) = (C + k) + 1 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    step fm
    exact ih C E

theorem r2r1_loop : ∀ k, ∀ A E, ⟨A, (0 : ℕ), k, 1, E⟩ [fm]⊢* ⟨A + k, (0 : ℕ), 0, 1, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  · rw [show (k + 1) = k + 1 from rfl]
    step fm
    rw [show A + 1 = A + 1 from rfl]
    step fm
    apply stepStar_trans (ih (A + 1) (E + 1))
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨n + 2, (0 : ℕ), 0, (0 : ℕ), n + 2⟩ [fm]⊢⁺
    ⟨2 * n + 3, (0 : ℕ), 0, (0 : ℕ), 2 * n + 3⟩ := by
  have p1 : ⟨n + 2, (0 : ℕ), 0, (0 : ℕ), n + 2⟩ [fm]⊢*
            ⟨(0 : ℕ), (0 : ℕ), 3 * (n + 2), (0 : ℕ), n + 2⟩ := by
    have h := r4_chain (n + 2) 0 0 (n + 2)
    simp at h; exact h
  have p2 : ⟨(0 : ℕ), (0 : ℕ), 3 * (n + 2), (0 : ℕ), n + 2⟩ [fm]⊢*
            ⟨(0 : ℕ), (0 : ℕ), 2 * (n + 2), (0 : ℕ), 0⟩ := by
    have h := r5_chain (n + 2) (2 * (n + 2)) 0
    rw [show 2 * (n + 2) + (n + 2) = 3 * (n + 2) from by ring,
        show 0 + (n + 2) = n + 2 from by ring] at h
    exact h
  have p3 : ⟨(0 : ℕ), (0 : ℕ), 2 * (n + 2), (0 : ℕ), 0⟩ [fm]⊢⁺
            ⟨(0 : ℕ), 1, 2 * n + 3, (0 : ℕ), 0⟩ := by
    rw [show 2 * (n + 2) = (2 * n + 3) + 1 from by ring]
    step fm; finish
  have p4a : ⟨(0 : ℕ), 1, 2 * n + 3, (0 : ℕ), 0⟩ [fm]⊢*
             ⟨(0 : ℕ), (0 : ℕ), 2 * n + 2, 1, 1⟩ := by
    rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm; finish
  have p4b : ⟨(0 : ℕ), (0 : ℕ), 2 * n + 2, 1, 1⟩ [fm]⊢*
             ⟨2 * n + 2, (0 : ℕ), 0, 1, 2 * n + 3⟩ := by
    have h := r2r1_loop (2 * n + 2) 0 1
    rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring,
        show 1 + (2 * n + 2) = 2 * n + 3 from by ring] at h
    exact h
  have p4c : ⟨2 * n + 2, (0 : ℕ), 0, 1, 2 * n + 3⟩ [fm]⊢*
             ⟨2 * n + 3, (0 : ℕ), 0, (0 : ℕ), 2 * n + 3⟩ := by
    step fm; step fm; finish
  exact stepPlus_stepStar_stepPlus
    (stepStar_stepPlus_stepPlus (stepStar_trans p1 p2) p3)
    (stepStar_trans p4a (stepStar_trans p4b p4c))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, n + 2⟩) 0
  intro n
  refine ⟨2 * n + 1, ?_⟩
  show ⟨n + 2, (0 : ℕ), 0, (0 : ℕ), n + 2⟩ [fm]⊢⁺
    ⟨(2 * n + 1) + 2, (0 : ℕ), 0, (0 : ℕ), (2 * n + 1) + 2⟩
  rw [show (2 * n + 1) + 2 = 2 * n + 3 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1668
