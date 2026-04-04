import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1604: [77/15, 14/3, 9/154, 5/7, 9/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  1  0
-1  2  0 -1 -1
 0  0  1 -1  0
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1604

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

theorem tail_chain : ∀ K, ∀ A D,
    ⟨A + 1, 0, 0, D + 1, K + 1⟩ [fm]⊢* ⟨A + K + 2, 0, 0, D + K + 2, 0⟩ := by
  intro K; induction' K with K ih <;> intro A D
  · step fm; step fm; step fm; ring_nf; finish
  · step fm; step fm; step fm
    rw [show A + 1 + 1 = (A + 1) + 1 from by ring,
        show D + 1 + 1 = (D + 1) + 1 from by ring]
    apply stepStar_trans (ih (A + 1) (D + 1))
    ring_nf; finish

theorem d_to_c : ∀ k c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 1)); ring_nf; finish

theorem drain_phase : ∀ K, ∀ D E,
    ⟨K + 1, 2, 2 * K + 2, D, E⟩ [fm]⊢* ⟨1, 0, 0, D + K + 2, E + K + 2⟩ := by
  intro K; induction' K with K ih <;> intro D E
  · step fm; step fm; ring_nf; finish
  · rw [show 2 * (K + 1) + 2 = (2 * K + 2 + 1) + 1 from by ring,
        show K + 1 + 1 = K + 1 + 1 from rfl]
    step fm
    rw [show 2 * K + 2 + 1 = (2 * K + 2) + 1 from by ring]
    step fm
    rw [show K + 1 + 1 = (K + 1) + 1 from by ring,
        show D + 1 + 1 = (D + 1) + 1 from by ring,
        show E + 1 + 1 = (E + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (D + 1) (E + 1))
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨1, 0, 0, n + 1, n + 1⟩ [fm]⊢⁺ ⟨1, 0, 0, n + 2, n + 2⟩ := by
  have p1 : ⟨1, 0, 0, n + 1, n + 1⟩ [fm]⊢* ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ := by
    have h := tail_chain n 0 n
    rw [show 0 + n + 2 = n + 2 from by omega,
        show n + n + 2 = 2 * n + 2 from by omega,
        show 0 + 1 = 1 from by omega] at h
    exact h
  have p2 : ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢* ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ := by
    have := d_to_c (a := n + 2) (2 * n + 2) 0; simpa using this
  have p3 : ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ [fm]⊢* ⟨n + 1, 2, 2 * n + 2, 0, 0⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]; step fm; finish
  have p4 : ⟨n + 1, 2, 2 * n + 2, 0, 0⟩ [fm]⊢* ⟨1, 0, 0, n + 2, n + 2⟩ := by
    have := drain_phase n 0 0
    rw [show 0 + n + 2 = n + 2 from by ring] at this
    exact this
  have p_all : ⟨1, 0, 0, n + 1, n + 1⟩ [fm]⊢* ⟨1, 0, 0, n + 2, n + 2⟩ :=
    stepStar_trans (stepStar_trans (stepStar_trans p1 p2) p3) p4
  exact stepStar_stepPlus p_all (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 2⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, n + 2, n + 2⟩) 0
  intro n; exists n + 1
  rw [show (n + 1) + 2 = n + 3 from by omega]
  exact main_trans (n + 1)

end Sz22_2003_unofficial_1604
