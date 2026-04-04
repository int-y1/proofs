import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1671: [77/15, 9/14, 2/3, 5/11, 135/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 1 -1  0  0  0
 0  0  1  0 -1
-1  3  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1671

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c+1, d, e⟩
  | _ => none

theorem e_to_c : ∀ k A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, (0 : ℕ), 0⟩ := by
  intro k; induction k with
  | zero => intro A C; simp; exists 0
  | succ k ih =>
    intro A C; step fm
    rw [show C + (k + 1) = (C + 1) + k from by ring]
    exact ih A (C + 1)

theorem b_to_a : ∀ k A E,
    ⟨A, k, 0, 0, E⟩ [fm]⊢* ⟨A + k, 0, 0, (0 : ℕ), E⟩ := by
  intro k; induction k with
  | zero => intro A E; simp; exists 0
  | succ k ih =>
    intro A E; step fm
    apply stepStar_trans (ih (A + 1) E)
    ring_nf; finish

theorem r1_triple : ∀ A C D E,
    ⟨A, 3, C + 3, D, E⟩ [fm]⊢* ⟨A, 0, C, D + 3, E + 3⟩ := by
  intro A C D E
  rw [show (3 : ℕ) = 2 + 1 from by ring, show C + 3 = (C + 2) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring, show C + 2 = (C + 1) + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring, show C + 1 = C + 1 from rfl]
  step fm
  ring_nf; finish

theorem r1r1r2_round : ∀ A C D E,
    ⟨A + 1, 2, C + 2, D, E⟩ [fm]⊢* ⟨A, 2, C, D + 1, E + 2⟩ := by
  intro A C D E
  rw [show (2 : ℕ) = 1 + 1 from by ring, show C + 2 = (C + 1) + 1 from by ring]
  step fm
  rw [show (C + 1 : ℕ) = C + 1 from rfl]
  step fm
  rw [show (A + 1 : ℕ) = A + 1 from rfl, show D + 2 = (D + 1) + 1 from by ring]
  step fm
  ring_nf; finish

theorem r1r1r2_chain : ∀ k A C D E,
    ⟨A + k, 2, C + 2 * k, D, E⟩ [fm]⊢* ⟨A, 2, C, D + k, E + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro A C D E; simp; exists 0
  | succ k ih =>
    intro A C D E
    rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k) + 2 from by ring]
    apply stepStar_trans (r1r1r2_round (A + k) (C + 2 * k) D E)
    apply stepStar_trans (ih A C (D + 1) (E + 2))
    ring_nf; finish

theorem r2_drain : ∀ k A B E,
    ⟨A + k, B, 0, k, E⟩ [fm]⊢* ⟨A, B + 2 * k, 0, (0 : ℕ), E⟩ := by
  intro k; induction k with
  | zero => intro A B E; simp; exists 0
  | succ k ih =>
    intro A B E
    rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih A (B + 2) E)
    ring_nf; finish

theorem main_trans_even (K : ℕ) :
    ⟨4 * K + 5, 0, 0, 0, 2 * K + 2⟩ [fm]⊢⁺
    ⟨4 * K + 7, 0, 0, (0 : ℕ), 2 * K + 3⟩ := by
  have p1 : ⟨4 * K + 5, 0, 0, 0, 2 * K + 2⟩ [fm]⊢*
            ⟨4 * K + 5, 0, 2 * K + 2, (0 : ℕ), 0⟩ := by
    have h := e_to_c (2 * K + 2) (4 * K + 5) 0; simp at h; exact h
  have p2 : ⟨4 * K + 5, 0, 2 * K + 2, 0, 0⟩ [fm]⊢⁺
            ⟨4 * K + 4, 3, 2 * K + 3, (0 : ℕ), 0⟩ := by
    rw [show 4 * K + 5 = (4 * K + 4) + 1 from by ring,
        show 2 * K + 3 = (2 * K + 2) + 1 from by ring]
    step fm; finish
  have p3 : ⟨4 * K + 4, 3, 2 * K + 3, 0, 0⟩ [fm]⊢*
            ⟨4 * K + 4, 0, 2 * K, 3, 3⟩ := by
    rw [show 2 * K + 3 = 2 * K + 3 from rfl]
    exact r1_triple (4 * K + 4) (2 * K) 0 0
  have p4 : ⟨4 * K + 4, 0, 2 * K, 3, 3⟩ [fm]⊢*
            ⟨4 * K + 3, 2, 2 * K, 2, 3⟩ := by
    rw [show 4 * K + 4 = (4 * K + 3) + 1 from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    step fm; ring_nf; finish
  have p5 : ⟨4 * K + 3, 2, 2 * K, 2, 3⟩ [fm]⊢*
            ⟨3 * K + 3, 2, 0, K + 2, 2 * K + 3⟩ := by
    have h := r1r1r2_chain K (3 * K + 3) 0 2 3
    rw [show 3 * K + 3 + K = 4 * K + 3 from by ring,
        show 0 + 2 * K = 2 * K from by ring,
        show 2 + K = K + 2 from by ring,
        show 3 + 2 * K = 2 * K + 3 from by ring] at h
    exact h
  have p6 : ⟨3 * K + 3, 2, 0, K + 2, 2 * K + 3⟩ [fm]⊢*
            ⟨2 * K + 1, 2 * K + 6, 0, (0 : ℕ), 2 * K + 3⟩ := by
    rw [show 3 * K + 3 = (2 * K + 1) + (K + 2) from by ring]
    have h := r2_drain (K + 2) (2 * K + 1) 2 (2 * K + 3)
    rw [show 2 + 2 * (K + 2) = 2 * K + 6 from by ring] at h
    exact h
  have p7 : ⟨2 * K + 1, 2 * K + 6, 0, 0, 2 * K + 3⟩ [fm]⊢*
            ⟨4 * K + 7, 0, 0, (0 : ℕ), 2 * K + 3⟩ := by
    have h := b_to_a (2 * K + 6) (2 * K + 1) (2 * K + 3)
    rw [show (2 * K + 1) + (2 * K + 6) = 4 * K + 7 from by ring] at h
    exact h
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus p2
      (stepStar_trans p3 (stepStar_trans p4 (stepStar_trans p5 (stepStar_trans p6 p7)))))

theorem main_trans_odd (K : ℕ) :
    ⟨4 * K + 7, 0, 0, 0, 2 * K + 3⟩ [fm]⊢⁺
    ⟨4 * K + 9, 0, 0, (0 : ℕ), 2 * K + 4⟩ := by
  have p1 : ⟨4 * K + 7, 0, 0, 0, 2 * K + 3⟩ [fm]⊢*
            ⟨4 * K + 7, 0, 2 * K + 3, (0 : ℕ), 0⟩ := by
    have h := e_to_c (2 * K + 3) (4 * K + 7) 0; simp at h; exact h
  have p2 : ⟨4 * K + 7, 0, 2 * K + 3, 0, 0⟩ [fm]⊢⁺
            ⟨4 * K + 6, 3, 2 * K + 4, (0 : ℕ), 0⟩ := by
    rw [show 4 * K + 7 = (4 * K + 6) + 1 from by ring,
        show 2 * K + 4 = (2 * K + 3) + 1 from by ring]
    step fm; finish
  have p3 : ⟨4 * K + 6, 3, 2 * K + 4, 0, 0⟩ [fm]⊢*
            ⟨4 * K + 6, 0, 2 * K + 1, 3, 3⟩ := by
    rw [show 2 * K + 4 = (2 * K + 1) + 3 from by ring]
    exact r1_triple (4 * K + 6) (2 * K + 1) 0 0
  have p4 : ⟨4 * K + 6, 0, 2 * K + 1, 3, 3⟩ [fm]⊢*
            ⟨4 * K + 5, 2, 2 * K + 1, 2, 3⟩ := by
    rw [show 4 * K + 6 = (4 * K + 5) + 1 from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    step fm; ring_nf; finish
  have p5 : ⟨4 * K + 5, 2, 2 * K + 1, 2, 3⟩ [fm]⊢*
            ⟨3 * K + 5, 2, 1, K + 2, 2 * K + 3⟩ := by
    rw [show 4 * K + 5 = (3 * K + 5) + K from by ring,
        show 2 * K + 1 = 1 + 2 * K from by ring]
    have h := r1r1r2_chain K (3 * K + 5) 1 2 3
    rw [show 2 + K = K + 2 from by ring, show 3 + 2 * K = 2 * K + 3 from by ring] at h
    exact h
  have p6 : ⟨3 * K + 5, 2, 1, K + 2, 2 * K + 3⟩ [fm]⊢*
            ⟨3 * K + 5, 1, 0, K + 3, 2 * K + 4⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    step fm; ring_nf; finish
  have p7 : ⟨3 * K + 5, 1, 0, K + 3, 2 * K + 4⟩ [fm]⊢*
            ⟨3 * K + 4, 3, 0, K + 2, 2 * K + 4⟩ := by
    rw [show 3 * K + 5 = (3 * K + 4) + 1 from by ring,
        show K + 3 = (K + 2) + 1 from by ring]
    step fm; ring_nf; finish
  have p8 : ⟨3 * K + 4, 3, 0, K + 2, 2 * K + 4⟩ [fm]⊢*
            ⟨2 * K + 2, 2 * K + 7, 0, (0 : ℕ), 2 * K + 4⟩ := by
    rw [show 3 * K + 4 = (2 * K + 2) + (K + 2) from by ring]
    have h := r2_drain (K + 2) (2 * K + 2) 3 (2 * K + 4)
    rw [show 3 + 2 * (K + 2) = 2 * K + 7 from by ring] at h
    exact h
  have p9 : ⟨2 * K + 2, 2 * K + 7, 0, 0, 2 * K + 4⟩ [fm]⊢*
            ⟨4 * K + 9, 0, 0, (0 : ℕ), 2 * K + 4⟩ := by
    have h := b_to_a (2 * K + 7) (2 * K + 2) (2 * K + 4)
    rw [show (2 * K + 2) + (2 * K + 7) = 4 * K + 9 from by ring] at h
    exact h
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus p2
      (stepStar_trans p3 (stepStar_trans p4 (stepStar_trans p5
        (stepStar_trans p6 (stepStar_trans p7 (stepStar_trans p8 p9)))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 2⟩) (by execute fm 18)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ K, q = ⟨4 * K + 5, 0, 0, 0, 2 * K + 2⟩ ∨
                        q = ⟨4 * K + 7, 0, 0, 0, 2 * K + 3⟩)
  · intro q ⟨K, hK⟩
    rcases hK with hq | hq
    · rw [hq]
      exact ⟨⟨4 * K + 7, 0, 0, 0, 2 * K + 3⟩, ⟨K, Or.inr rfl⟩, main_trans_even K⟩
    · rw [hq]
      exact ⟨⟨4 * K + 9, 0, 0, 0, 2 * K + 4⟩, ⟨K + 1, Or.inl (by ring_nf)⟩, main_trans_odd K⟩
  · exact ⟨0, Or.inl rfl⟩

end Sz22_2003_unofficial_1671
