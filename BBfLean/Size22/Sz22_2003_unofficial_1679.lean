import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1679

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e+1⟩
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

theorem r2_drain_d : ∀ D, ∀ A B E,
    ⟨A + D, B, 0, D, E⟩ [fm]⊢* ⟨A, B + 2 * D, 0, (0 : ℕ), E⟩ := by
  intro D; induction D with
  | zero => intro A B E; simp; exists 0
  | succ D ih =>
    intro A B E
    rw [show A + (D + 1) = (A + D) + 1 from by ring,
        show (D + 1 : ℕ) = D + 1 from rfl]
    step fm
    rw [show B + 2 * (D + 1) = (B + 2) + 2 * D from by ring]
    exact ih A (B + 2) E

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
    ⟨4 * m + 3, 0, 2 * m + 1, 0, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨4 * m + 5, 0, 2 * m + 2, (0 : ℕ), 0⟩ := by
  -- R5: (4m+3, 0, 2m+1, 0, 0) -> (4m+2, 2, 2m+1, 1, 1)
  have p1 : ⟨4 * m + 3, 0, 2 * m + 1, 0, (0 : ℕ)⟩ [fm]⊢⁺
      ⟨4 * m + 2, 2, 2 * m + 1, 1, (1 : ℕ)⟩ := by
    rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring]
    step fm; finish
  -- r1r1r2_chain with K=m: (4m+2, 2, 2m+1, 1, 1) = ((3m+2)+m, 2, 1+2m, 1, 1)
  -- -> (3m+2, 2, 1, m+1, 2m+1)
  have p2 : ⟨4 * m + 2, 2, 2 * m + 1, 1, (1 : ℕ)⟩ [fm]⊢*
      ⟨3 * m + 2, 2, 1, m + 1, 2 * m + 1⟩ := by
    have h := r1r1r2_chain m (3 * m + 2) 1 1 1
    rw [show 3 * m + 2 + m = 4 * m + 2 from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring,
        show 1 + m = m + 1 from by ring] at h
    exact h
  -- R1: (3m+2, 2, 1, m+1, 2m+1) -> (3m+2, 1, 0, m+2, 2m+2)
  have p3 : ⟨3 * m + 2, 2, 1, m + 1, 2 * m + 1⟩ [fm]⊢*
      ⟨3 * m + 2, 1, 0, m + 2, 2 * m + 2⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm; ring_nf; finish
  -- R2: (3m+2, 1, 0, m+2, 2m+2) -> (3m+1, 3, 0, m+1, 2m+2)
  have p4 : ⟨3 * m + 2, 1, 0, m + 2, 2 * m + 2⟩ [fm]⊢*
      ⟨3 * m + 1, 3, 0, m + 1, 2 * m + 2⟩ := by
    rw [show 3 * m + 2 = (3 * m + 1) + 1 from by ring,
        show m + 2 = (m + 1) + 1 from by ring]
    step fm; ring_nf; finish
  -- r2_drain_d with D=m+1: (3m+1, 3, 0, m+1, 2m+2) = ((2m)+m+1, 3, 0, m+1, 2m+2)
  -- -> (2m, 2m+5, 0, 0, 2m+2)
  have p5 : ⟨3 * m + 1, 3, 0, m + 1, 2 * m + 2⟩ [fm]⊢*
      ⟨2 * m, 2 * m + 5, 0, (0 : ℕ), 2 * m + 2⟩ := by
    have h := r2_drain_d (m + 1) (2 * m) 3 (2 * m + 2)
    rw [show 2 * m + (m + 1) = 3 * m + 1 from by ring,
        show 3 + 2 * (m + 1) = 2 * m + 5 from by ring] at h
    exact h
  -- b_to_a: (2m, 2m+5, 0, 0, 2m+2) -> (4m+5, 0, 0, 0, 2m+2)
  have p6 : ⟨2 * m, 2 * m + 5, 0, 0, 2 * m + 2⟩ [fm]⊢*
      ⟨4 * m + 5, 0, 0, (0 : ℕ), 2 * m + 2⟩ := by
    have h := b_to_a (2 * m + 5) (2 * m) (2 * m + 2)
    rw [show 2 * m + (2 * m + 5) = 4 * m + 5 from by ring] at h
    exact h
  -- e_to_c: (4m+5, 0, 0, 0, 2m+2) -> (4m+5, 0, 2m+2, 0, 0)
  have p7 : ⟨4 * m + 5, 0, 0, 0, 2 * m + 2⟩ [fm]⊢*
      ⟨4 * m + 5, 0, 2 * m + 2, (0 : ℕ), 0⟩ := by
    have h := e_to_c (2 * m + 2) (4 * m + 5) 0
    rw [show 0 + (2 * m + 2) = 2 * m + 2 from by ring] at h
    exact h
  exact stepPlus_stepStar_stepPlus p1
    (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4
      (stepStar_trans p5 (stepStar_trans p6 p7)))))

theorem main_trans_odd (m : ℕ) :
    ⟨4 * m + 5, 0, 2 * m + 2, 0, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨4 * m + 7, 0, 2 * m + 3, (0 : ℕ), 0⟩ := by
  -- R5: (4m+5, 0, 2m+2, 0, 0) -> (4m+4, 2, 2m+2, 1, 1)
  have p1 : ⟨4 * m + 5, 0, 2 * m + 2, 0, (0 : ℕ)⟩ [fm]⊢⁺
      ⟨4 * m + 4, 2, 2 * m + 2, 1, (1 : ℕ)⟩ := by
    rw [show 4 * m + 5 = (4 * m + 4) + 1 from by ring]
    step fm; finish
  -- r1r1r2_chain with K=m+1: (4m+4, 2, 2m+2, 1, 1) = ((3m+3)+(m+1), 2, 0+2*(m+1), 1, 1)
  -- -> (3m+3, 2, 0, m+2, 2m+3)
  have p2 : ⟨4 * m + 4, 2, 2 * m + 2, 1, (1 : ℕ)⟩ [fm]⊢*
      ⟨3 * m + 3, 2, 0, m + 2, 2 * m + 3⟩ := by
    have h := r1r1r2_chain (m + 1) (3 * m + 3) 0 1 1
    rw [show 3 * m + 3 + (m + 1) = 4 * m + 4 from by ring,
        show 0 + 2 * (m + 1) = 2 * m + 2 from by ring,
        show 1 + (m + 1) = m + 2 from by ring,
        show 1 + 2 * (m + 1) = 2 * m + 3 from by ring] at h
    exact h
  -- r2_drain_d with D=m+2: (3m+3, 2, 0, m+2, 2m+3) = ((2m+1)+(m+2), 2, 0, m+2, 2m+3)
  -- -> (2m+1, 2m+6, 0, 0, 2m+3)
  have p3 : ⟨3 * m + 3, 2, 0, m + 2, 2 * m + 3⟩ [fm]⊢*
      ⟨2 * m + 1, 2 * m + 6, 0, (0 : ℕ), 2 * m + 3⟩ := by
    have h := r2_drain_d (m + 2) (2 * m + 1) 2 (2 * m + 3)
    rw [show 2 * m + 1 + (m + 2) = 3 * m + 3 from by ring,
        show 2 + 2 * (m + 2) = 2 * m + 6 from by ring] at h
    exact h
  -- b_to_a: (2m+1, 2m+6, 0, 0, 2m+3) -> (4m+7, 0, 0, 0, 2m+3)
  have p4 : ⟨2 * m + 1, 2 * m + 6, 0, 0, 2 * m + 3⟩ [fm]⊢*
      ⟨4 * m + 7, 0, 0, (0 : ℕ), 2 * m + 3⟩ := by
    have h := b_to_a (2 * m + 6) (2 * m + 1) (2 * m + 3)
    rw [show 2 * m + 1 + (2 * m + 6) = 4 * m + 7 from by ring] at h
    exact h
  -- e_to_c: (4m+7, 0, 0, 0, 2m+3) -> (4m+7, 0, 2m+3, 0, 0)
  have p5 : ⟨4 * m + 7, 0, 0, 0, 2 * m + 3⟩ [fm]⊢*
      ⟨4 * m + 7, 0, 2 * m + 3, (0 : ℕ), 0⟩ := by
    have h := e_to_c (2 * m + 3) (4 * m + 7) 0
    rw [show 0 + (2 * m + 3) = 2 * m + 3 from by ring] at h
    exact h
  exact stepPlus_stepStar_stepPlus p1
    (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4 p5)))

theorem main_trans (n : ℕ) :
    ⟨2 * n + 3, 0, n + 1, 0, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨2 * n + 5, 0, n + 2, (0 : ℕ), 0⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show 2 * (m + m) + 3 = 4 * m + 3 from by ring,
        show (m + m) + 1 = 2 * m + 1 from by ring,
        show 2 * (m + m) + 5 = 4 * m + 5 from by ring,
        show (m + m) + 2 = 2 * m + 2 from by ring]
    exact main_trans_even m
  · subst hm
    rw [show 2 * (2 * m + 1) + 3 = 4 * m + 5 from by ring,
        show (2 * m + 1) + 1 = 2 * m + 2 from by ring,
        show 2 * (2 * m + 1) + 5 = 4 * m + 7 from by ring,
        show (2 * m + 1) + 2 = 2 * m + 3 from by ring]
    exact main_trans_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 1, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, n + 1, 0, 0⟩) 0
  intro n
  exists n + 1
  rw [show 2 * (n + 1) + 3 = 2 * n + 5 from by ring,
      show (n + 1) + 1 = n + 2 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1679
