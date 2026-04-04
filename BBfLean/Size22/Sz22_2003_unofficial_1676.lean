import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1676: [77/15, 9/14, 2/3, 5/11, 315/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 1 -1  0  0  0
 0  0  1  0 -1
-1  2  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1676

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d+1, e⟩
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

theorem r2_drain : ∀ D, ∀ A B E,
    ⟨A + D, B, 0, D, E⟩ [fm]⊢* ⟨A, B + 2 * D, 0, (0 : ℕ), E⟩ := by
  intro D; induction D with
  | zero => intro A B E; simp; exists 0
  | succ D ih =>
    intro A B E
    rw [show A + (D + 1) = (A + D) + 1 from by ring,
        show (D + 1 : ℕ) = D + 1 from rfl]
    step fm
    apply stepStar_trans (ih A (B + 2) E); ring_nf; finish

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

theorem main_trans_even (m : ℕ) :
    ⟨4 * m + 5, 0, 2 * m + 2, 0, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨4 * m + 7, 0, 2 * m + 3, (0 : ℕ), 0⟩ := by
  have p1 : ⟨4 * m + 5, 0, 2 * m + 2, 0, (0 : ℕ)⟩ [fm]⊢⁺
      ⟨4 * m + 4, 2, 2 * m + 3, 1, (0 : ℕ)⟩ := by
    rw [show 4 * m + 5 = (4 * m + 4) + 1 from by ring]
    step fm; finish
  have p2 : ⟨4 * m + 4, 2, 2 * m + 3, 1, (0 : ℕ)⟩ [fm]⊢*
      ⟨3 * m + 3, 2, 1, m + 2, 2 * m + 2⟩ := by
    have h := r1r1r2_chain (m + 1) (3 * m + 3) 1 1 0
    rw [show 3 * m + 3 + (m + 1) = 4 * m + 4 from by ring,
        show 1 + 2 * (m + 1) = 2 * m + 3 from by ring,
        show 1 + (m + 1) = m + 2 from by ring,
        show 0 + 2 * (m + 1) = 2 * m + 2 from by ring] at h
    exact h
  have p3 : ⟨3 * m + 3, 2, 1, m + 2, 2 * m + 2⟩ [fm]⊢*
      ⟨3 * m + 3, 1, 0, m + 3, 2 * m + 3⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    step fm; ring_nf; finish
  have p4 : ⟨3 * m + 3, 1, 0, m + 3, 2 * m + 3⟩ [fm]⊢*
      ⟨2 * m, 2 * m + 7, 0, (0 : ℕ), 2 * m + 3⟩ := by
    rw [show 3 * m + 3 = 2 * m + (m + 3) from by ring]
    have h := r2_drain (m + 3) (2 * m) 1 (2 * m + 3)
    rw [show 1 + 2 * (m + 3) = 2 * m + 7 from by ring] at h
    exact h
  have p5 : ⟨2 * m, 2 * m + 7, 0, 0, 2 * m + 3⟩ [fm]⊢*
      ⟨4 * m + 7, 0, 0, (0 : ℕ), 2 * m + 3⟩ := by
    have h := b_to_a (2 * m + 7) (2 * m) (2 * m + 3)
    rw [show 2 * m + (2 * m + 7) = 4 * m + 7 from by ring] at h
    exact h
  have p6 : ⟨4 * m + 7, 0, 0, 0, 2 * m + 3⟩ [fm]⊢*
      ⟨4 * m + 7, 0, 2 * m + 3, (0 : ℕ), 0⟩ := by
    have h := e_to_c (2 * m + 3) (4 * m + 7) 0
    rw [show 0 + (2 * m + 3) = 2 * m + 3 from by ring] at h
    exact h
  exact stepPlus_stepStar_stepPlus p1
    (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4 (stepStar_trans p5 p6))))

theorem main_trans_odd (m : ℕ) :
    ⟨4 * m + 7, 0, 2 * m + 3, 0, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨4 * m + 9, 0, 2 * m + 4, (0 : ℕ), 0⟩ := by
  have p1 : ⟨4 * m + 7, 0, 2 * m + 3, 0, (0 : ℕ)⟩ [fm]⊢⁺
      ⟨4 * m + 6, 2, 2 * m + 4, 1, (0 : ℕ)⟩ := by
    rw [show 4 * m + 7 = (4 * m + 6) + 1 from by ring]
    step fm; finish
  have p2 : ⟨4 * m + 6, 2, 2 * m + 4, 1, (0 : ℕ)⟩ [fm]⊢*
      ⟨3 * m + 4, 2, 0, m + 3, 2 * m + 4⟩ := by
    have h := r1r1r2_chain (m + 2) (3 * m + 4) 0 1 0
    rw [show 3 * m + 4 + (m + 2) = 4 * m + 6 from by ring,
        show 0 + 2 * (m + 2) = 2 * m + 4 from by ring,
        show 1 + (m + 2) = m + 3 from by ring] at h
    exact h
  have p3 : ⟨3 * m + 4, 2, 0, m + 3, 2 * m + 4⟩ [fm]⊢*
      ⟨2 * m + 1, 2 * m + 8, 0, (0 : ℕ), 2 * m + 4⟩ := by
    rw [show 3 * m + 4 = (2 * m + 1) + (m + 3) from by ring]
    have h := r2_drain (m + 3) (2 * m + 1) 2 (2 * m + 4)
    rw [show 2 + 2 * (m + 3) = 2 * m + 8 from by ring] at h
    exact h
  have p4 : ⟨2 * m + 1, 2 * m + 8, 0, 0, 2 * m + 4⟩ [fm]⊢*
      ⟨4 * m + 9, 0, 0, (0 : ℕ), 2 * m + 4⟩ := by
    have h := b_to_a (2 * m + 8) (2 * m + 1) (2 * m + 4)
    rw [show 2 * m + 1 + (2 * m + 8) = 4 * m + 9 from by ring] at h
    exact h
  have p5 : ⟨4 * m + 9, 0, 0, 0, 2 * m + 4⟩ [fm]⊢*
      ⟨4 * m + 9, 0, 2 * m + 4, (0 : ℕ), 0⟩ := by
    have h := e_to_c (2 * m + 4) (4 * m + 9) 0
    rw [show 0 + (2 * m + 4) = 2 * m + 4 from by ring] at h
    exact h
  exact stepPlus_stepStar_stepPlus p1
    (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4 p5)))

theorem main_trans (n : ℕ) :
    ⟨2 * n + 1, 0, n, 0, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨2 * n + 3, 0, n + 1, (0 : ℕ), 0⟩ := by
  rcases n with _ | _ | n
  · execute fm 10
  · execute fm 14
  · rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      rw [show 2 * (m + m + 2) + 1 = 4 * m + 5 from by ring,
          show 2 * (m + m + 2) + 3 = 4 * m + 7 from by ring,
          show m + m + 2 + 1 = 2 * m + 3 from by ring,
          show (m + m + 2 : ℕ) = 2 * m + 2 from by ring]
      exact main_trans_even m
    · subst hm
      rw [show 2 * (2 * m + 1 + 2) + 1 = 4 * m + 7 from by ring,
          show 2 * (2 * m + 1 + 2) + 3 = 4 * m + 9 from by ring,
          show 2 * m + 1 + 2 + 1 = 2 * m + 4 from by ring,
          show (2 * m + 1 + 2 : ℕ) = 2 * m + 3 from by ring]
      exact main_trans_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 1, 0, n, 0, 0⟩) 0
  intro n; exists n + 1
  exact main_trans n

end Sz22_2003_unofficial_1676
