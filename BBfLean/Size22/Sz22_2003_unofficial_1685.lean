import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1685: [77/15, 9/14, 4/3, 5/11, 363/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 2 -1  0  0  0
 0  0  1  0 -1
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1685

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · simp; exists 0
  · rw [show C + (k + 1) = (C + 1) + k from by ring]
    step fm; exact ih A (C + 1)

theorem r2r1r1_chain : ∀ k, ∀ A C D E,
    ⟨A + k, 0, C + 2 * k, D + 1, E⟩ [fm]⊢* ⟨A, 0, C, D + 1 + k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih A C (D + 1) (E + 2))
    rw [show D + 1 + 1 + k = D + 1 + (k + 1) from by ring,
        show E + 2 + 2 * k = E + 2 * (k + 1) from by ring]; finish

theorem drain : ∀ M, ∀ A B D E, 3 * D + B = M →
    ⟨A, B + 1, 0, D, E⟩ [fm]⊢* ⟨A + 2 * B + 2 + 3 * D, 0, 0, 0, E⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih; intro A B D E hM
  rcases D with _ | D
  · rcases B with _ | B
    · step fm; ring_nf; finish
    · rw [show (B + 1) + 1 = (B + 1) + 1 from rfl]
      step fm
      have := ih (3 * 0 + B) (by omega) (A + 2) B 0 E rfl
      rw [show (A + 2) + 2 * B + 2 + 3 * 0 = A + 2 * (B + 1) + 2 + 3 * 0 from by ring] at this
      exact this
  · rcases A with _ | A
    · rcases B with _ | B
      · step fm
        rw [show D + 1 = D + 1 from rfl]
        step fm
        have := ih (3 * D + 1) (by omega) 1 1 D E (by ring)
        rw [show 1 + 2 * 1 + 2 + 3 * D = 0 + 2 * 0 + 2 + 3 * (D + 1) from by ring] at this
        exact this
      · rw [show (B + 1) + 1 = (B + 1) + 1 from rfl]
        step fm
        have := ih (3 * (D + 1) + B) (by omega) 2 B (D + 1) E (by ring)
        rw [show 2 + 2 * B + 2 + 3 * (D + 1) = 0 + 2 * (B + 1) + 2 + 3 * (D + 1) from by ring] at this
        exact this
    · rw [show A + 1 = A + 1 from rfl, show D + 1 = D + 1 from rfl]
      step fm
      have := ih (3 * D + (B + 2)) (by omega) A (B + 2) D E (by ring)
      rw [show A + 2 * (B + 2) + 2 + 3 * D = (A + 1) + 2 * B + 2 + 3 * (D + 1) from by ring] at this
      exact this

-- Even c case: (a+2k+2, 0, 2k+2, 0, 0) ⊢⁺ (a+4k+5, 0, 2k+4, 0, 0)
theorem main_trans_even (a k : ℕ) :
    ⟨a + 2 * k + 2, 0, 2 * k + 2, 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * k + 5, 0, 2 * k + 4, 0, 0⟩ := by
  -- R5+R1
  have p1 : ⟨a + 2 * k + 2, 0, 2 * k + 2, 0, 0⟩ [fm]⊢⁺
      ⟨a + 2 * k + 1, 0, 2 * k + 1, 1, 3⟩ := by
    rw [show a + 2 * k + 2 = (a + 2 * k + 1) + 1 from by ring,
        show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm; finish
  -- R2R1R1 chain (k rounds)
  have p2 : ⟨a + 2 * k + 1, 0, 2 * k + 1, 1, 3⟩ [fm]⊢*
      ⟨a + k + 1, 0, 1, k + 1, 2 * k + 3⟩ := by
    have h := r2r1r1_chain k (a + k + 1) 1 0 3
    rw [show (a + k + 1) + k = a + 2 * k + 1 from by ring,
        show 1 + 2 * k = 2 * k + 1 from by ring,
        show 0 + 1 + k = k + 1 from by ring,
        show 3 + 2 * k = 2 * k + 3 from by ring] at h
    exact h
  -- R2+R1: handle remainder c=1
  have p3 : ⟨a + k + 1, 0, 1, k + 1, 2 * k + 3⟩ [fm]⊢*
      ⟨a + k, 1, 0, k + 1, 2 * k + 4⟩ := by
    rw [show k + 1 = k + 1 from rfl,
        show a + k + 1 = (a + k) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm; step fm
    rw [show 2 * k + 3 + 1 = 2 * k + 4 from by ring]; finish
  -- Drain
  have p4 : ⟨a + k, 1, 0, k + 1, 2 * k + 4⟩ [fm]⊢*
      ⟨a + 4 * k + 5, 0, 0, 0, 2 * k + 4⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    have h := drain (3 * (k + 1) + 0) (a + k) 0 (k + 1) (2 * k + 4) (by ring)
    rw [show a + k + 2 * 0 + 2 + 3 * (k + 1) = a + 4 * k + 5 from by ring] at h
    exact h
  -- R4 chain
  have p5 : ⟨a + 4 * k + 5, 0, 0, 0, 2 * k + 4⟩ [fm]⊢*
      ⟨a + 4 * k + 5, 0, 2 * k + 4, 0, 0⟩ := by
    have h := r4_chain (2 * k + 4) (a + 4 * k + 5) 0
    simp only [Nat.zero_add] at h; exact h
  exact stepPlus_stepStar_stepPlus p1
    (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4 p5)))

-- Odd c case: (a+2k+3, 0, 2k+3, 0, 0) ⊢⁺ (a+4k+7, 0, 2k+5, 0, 0)
theorem main_trans_odd (a k : ℕ) :
    ⟨a + 2 * k + 3, 0, 2 * k + 3, 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * k + 7, 0, 2 * k + 5, 0, 0⟩ := by
  -- R5+R1
  have p1 : ⟨a + 2 * k + 3, 0, 2 * k + 3, 0, 0⟩ [fm]⊢⁺
      ⟨a + 2 * k + 2, 0, 2 * k + 2, 1, 3⟩ := by
    rw [show a + 2 * k + 3 = (a + 2 * k + 2) + 1 from by ring,
        show 2 * k + 3 = (2 * k + 2) + 1 from by ring]
    step fm; step fm; finish
  -- R2R1R1 chain (k+1 rounds)
  have p2 : ⟨a + 2 * k + 2, 0, 2 * k + 2, 1, 3⟩ [fm]⊢*
      ⟨a + k + 1, 0, 0, k + 2, 2 * k + 5⟩ := by
    have h := r2r1r1_chain (k + 1) (a + k + 1) 0 0 3
    rw [show (a + k + 1) + (k + 1) = a + 2 * k + 2 from by ring,
        show 0 + 2 * (k + 1) = 2 * k + 2 from by ring,
        show 0 + 1 + (k + 1) = k + 2 from by ring,
        show 3 + 2 * (k + 1) = 2 * k + 5 from by ring] at h
    exact h
  -- R2 + drain
  have p3 : ⟨a + k + 1, 0, 0, k + 2, 2 * k + 5⟩ [fm]⊢*
      ⟨a + 4 * k + 7, 0, 0, 0, 2 * k + 5⟩ := by
    rw [show k + 2 = (k + 1) + 1 from by ring,
        show a + k + 1 = (a + k) + 1 from by ring]
    step fm
    have h := drain (3 * (k + 1) + 1) (a + k) 1 (k + 1) (2 * k + 5) (by ring)
    rw [show a + k + 2 * 1 + 2 + 3 * (k + 1) = a + 4 * k + 7 from by ring] at h
    exact h
  -- R4 chain
  have p4 : ⟨a + 4 * k + 7, 0, 0, 0, 2 * k + 5⟩ [fm]⊢*
      ⟨a + 4 * k + 7, 0, 2 * k + 5, 0, 0⟩ := by
    have h := r4_chain (2 * k + 5) (a + 4 * k + 7) 0
    simp only [Nat.zero_add] at h; exact h
  exact stepPlus_stepStar_stepPlus p1
    (stepStar_trans p2 (stepStar_trans p3 p4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 2, 0, 0⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a + c + 2, 0, c + 2, 0, 0⟩)
  · intro q ⟨a, c, hq⟩
    subst hq
    rcases Nat.even_or_odd c with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      refine ⟨⟨a + 4 * k + 5, 0, 2 * k + 4, 0, 0⟩,
             ⟨a + 2 * k + 1, 2 * k + 2, ?_⟩, ?_⟩
      · show (a + 4 * k + 5, 0, 2 * k + 4, 0, 0) =
              ((a + 2 * k + 1) + (2 * k + 2) + 2, 0, (2 * k + 2) + 2, 0, 0)
        ring_nf
      · show ⟨a + (k + k) + 2, 0, (k + k) + 2, 0, 0⟩ [fm]⊢⁺ _
        rw [show a + (k + k) + 2 = a + 2 * k + 2 from by ring,
            show (k + k) + 2 = 2 * k + 2 from by ring]
        exact main_trans_even a k
    · subst hk
      refine ⟨⟨a + 4 * k + 7, 0, 2 * k + 5, 0, 0⟩,
             ⟨a + 2 * k + 2, 2 * k + 3, ?_⟩, ?_⟩
      · show (a + 4 * k + 7, 0, 2 * k + 5, 0, 0) =
              ((a + 2 * k + 2) + (2 * k + 3) + 2, 0, (2 * k + 3) + 2, 0, 0)
        ring_nf
      · show ⟨a + (2 * k + 1) + 2, 0, (2 * k + 1) + 2, 0, 0⟩ [fm]⊢⁺ _
        rw [show a + (2 * k + 1) + 2 = a + 2 * k + 3 from by ring,
            show (2 * k + 1) + 2 = 2 * k + 3 from by ring]
        exact main_trans_odd a k
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_1685
