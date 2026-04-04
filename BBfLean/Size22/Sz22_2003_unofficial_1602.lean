import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1602: [77/15, 14/3, 9/110, 5/7, 9/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  1  0
-1  2 -1  0 -1
 0  0  1 -1  0
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1602

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c+1, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

theorem d_to_c : ∀ k c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 1)); ring_nf; finish

theorem tail_chain : ∀ K, ∀ A D,
    ⟨A + 1, 0, 0, D + 1, K⟩ [fm]⊢* ⟨A + K + 1, 0, 0, D + K + 1, 0⟩ := by
  intro K; induction' K with K ih <;> intro A D
  · simp; exists 0
  · step fm; step fm; step fm; step fm
    rw [show A + (K + 1) + 1 = (A + 1) + K + 1 from by ring,
        show D + (K + 1) + 1 = (D + 1) + K + 1 from by ring]
    exact ih (A + 1) (D + 1)

theorem drain_tail : ∀ C, ∀ A D E, C ≤ 2 * A + 1 →
    ⟨A + 1, 0, C + 1, D, E + 1⟩ [fm]⊢* ⟨A + E + 2, 0, 0, D + C + E + 2, 0⟩ := by
  intro C; induction' C using Nat.strongRecOn with C IH; intro A D E hC
  rcases C with _ | _ | C
  · step fm; step fm; step fm
    rw [show A + E + 2 = (A + 1) + E + 1 from by ring,
        show D + 0 + E + 2 = (D + 1) + E + 1 from by ring]
    exact tail_chain E (A + 1) (D + 1)
  · step fm; step fm; step fm
    rw [show A + E + 2 = A + (E + 1) + 1 from by ring,
        show D + 1 + E + 2 = (D + 1) + (E + 1) + 1 from by ring]
    exact tail_chain (E + 1) A (D + 1)
  · rw [show C + 2 + 1 = (C + 1 + 1) + 1 from by ring]
    step fm
    rw [show C + 1 + 1 = (C + 1) + 1 from by ring]
    step fm; step fm
    rcases A with _ | A'
    · omega
    · rcases C with _ | C'
      · rw [show A' + 1 + E + 2 = A' + (E + 2) + 1 from by ring,
            show D + (0 + 2) + E + 2 = (D + 1) + (E + 2) + 1 from by ring,
            show A' + 1 = A' + 1 from rfl,
            show D + 2 = (D + 1) + 1 from by ring]
        exact tail_chain (E + 2) A' (D + 1)
      · have hC' : C' ≤ 2 * A' + 1 := by omega
        rw [show E + 2 = (E + 1) + 1 from by ring]
        have ih := IH C' (by omega) A' (D + 2) (E + 1) hC'
        rw [show A' + 1 + E + 2 = A' + (E + 1) + 2 from by ring,
            show D + (C' + 1 + 2) + E + 2 = D + 2 + C' + (E + 1) + 2 from by ring]
        exact ih

theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 2 * n + 4, 0⟩ := by
  have p1 : ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢* ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ := by
    have := d_to_c (a := n + 2) (2 * n + 2) 0; simpa using this
  have p2 : ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ [fm]⊢* ⟨n + 1, 2, 2 * n + 2, 0, 0⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]; step fm; finish
  have p3 : ⟨n + 1, 2, 2 * n + 2, 0, 0⟩ [fm]⊢* ⟨n + 1, 0, 2 * n, 2, 2⟩ := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
    step fm
    rw [show 2 * n + 1 = 2 * n + 1 from rfl]
    step fm; ring_nf; finish
  have p4 : ⟨n + 1, 0, 2 * n, 2, 2⟩ [fm]⊢* ⟨n + 3, 0, 0, 2 * n + 4, 0⟩ := by
    rcases n with _ | n
    · simp
      rw [show (3 : ℕ) = 0 + 2 + 1 from by ring,
          show (4 : ℕ) = 1 + 2 + 1 from by ring]
      exact tail_chain 2 0 1
    · rw [show n + 1 + 1 = (n + 1) + 1 from by ring,
          show 2 * (n + 1) = (2 * n + 1) + 1 from by ring,
          show (2 : ℕ) = 1 + 1 from rfl]
      have hC : 2 * n + 1 ≤ 2 * (n + 1) + 1 := by omega
      have := drain_tail (2 * n + 1) (n + 1) 2 1 hC
      rw [show n + 1 + 1 + 2 = n + 1 + 3 from by ring,
          show 2 + (2 * n + 1) + 1 + 2 = 2 * (n + 1) + 4 from by ring] at this
      exact this
  have p_all : ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢* ⟨n + 3, 0, 0, 2 * n + 4, 0⟩ :=
    stepStar_trans (stepStar_trans (stepStar_trans p1 p2) p3) p4
  exact stepStar_stepPlus p_all (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 2 * n + 2, 0⟩) 0
  intro n; exists n + 1
  rw [show (n + 1) + 2 = n + 3 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1602
