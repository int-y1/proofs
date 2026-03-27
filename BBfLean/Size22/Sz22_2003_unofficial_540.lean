import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #540: [28/15, 9/22, 5/2, 11/7, 42/5]

Vector representation:
```
 2 -1 -1  1  0
-1  2  0  0 -1
-1  0  1  0  0
 0  0  0 -1  1
 1  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_540

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d+1, e⟩
  | _ => none

theorem a_to_c : ∀ k c, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _); ring_nf; finish

theorem d_to_e : ∀ k c d, ⟨0, 0, c, d+k, 0⟩ [fm]⊢* ⟨0, 0, c, d, k⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show d + (k + 1) = (d + 1) + k from by ring]
  apply stepStar_trans (h c (d + 1)); step fm; finish

theorem opening : ⟨0, 0, c+2, 0, e+1⟩ [fm]⊢* ⟨2, 2, c, 2, e⟩ := by
  step fm; step fm; step fm; finish

theorem r1r1r2_chain : ∀ k A D E, ⟨A, 2, 2*k+c, D, E+k⟩ [fm]⊢* ⟨A+3*k, 2, c, D+2*k, E⟩ := by
  intro k; induction' k with k h <;> intro A D E
  · simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]; exists 0
  rw [show 2 * (k + 1) + c = (2 * k + c) + 2 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

theorem r1_odd : ⟨A, 2, 1, D, E⟩ [fm]⊢* ⟨A+2, 1, 0, D+1, E⟩ := by
  step fm; finish

theorem r2_drain : ∀ k X Y, ⟨X+k, Y, 0, D, k⟩ [fm]⊢* ⟨X, Y+2*k, 0, D, 0⟩ := by
  intro k; induction' k with k h <;> intro X Y
  · simp only [Nat.add_zero, Nat.mul_zero]; exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

theorem r3r1_chain : ∀ k a d,
    ⟨a+1, k, 0, d, 0⟩ [fm]⊢* ⟨a+1+k, 0, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  step fm; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

theorem phases12 (a n : ℕ) :
    ⟨a, 0, 0, a+n, 0⟩ [fm]⊢* ⟨0, 0, a, 0, a+n⟩ := by
  have h1 : ⟨0+a, 0, 0, a+n, 0⟩ [fm]⊢* ⟨0, 0, 0+a, a+n, 0⟩ := a_to_c a 0
  simp only [Nat.zero_add] at h1
  have h2 : ⟨0, 0, a, 0+(a+n), 0⟩ [fm]⊢* ⟨0, 0, a, 0, a+n⟩ := d_to_e (a+n) a 0
  simp only [Nat.zero_add] at h2
  exact stepStar_trans h1 h2

-- Combine all ⊢* phases from (0,0,a,0,a+n) to final state
-- for even a = 2m+2
theorem inner_even (m n g : ℕ) (hg : n + g = 2 * m) :
    ⟨0, 0, 2*m+2, 0, 2*m+2+n⟩ [fm]⊢* ⟨4*m+n+5, 0, 0, 4*m+2*n+6, 0⟩ := by
  -- opening
  have h1 : ⟨0, 0, 2*m+2, 0, 2*m+2+n⟩ [fm]⊢* ⟨2, 2, 2*m, 2, 2*m+1+n⟩ := by
    rw [show 2*m+2 = 2*m + 2 from by ring,
        show 2*m+2+n = (2*m+1+n) + 1 from by ring]; exact opening
  -- r1r1r2_chain
  have h2 : ⟨2, 2, 2*m, 2, 2*m+1+n⟩ [fm]⊢* ⟨2+3*m, 2, 0, 2+2*m, m+1+n⟩ := by
    have := @r1r1r2_chain 0 m 2 2 (m+1+n)
    rw [show 2*m+0 = 2*m from by ring,
        show (m+1+n)+m = 2*m+1+n from by ring] at this; exact this
  -- r2_drain
  have h3 : ⟨2+3*m, 2, 0, 2+2*m, m+1+n⟩ [fm]⊢* ⟨g+1, 2*m+2*n+4, 0, 2+2*m, 0⟩ := by
    have := @r2_drain (2+2*m) (m+1+n) (g+1) 2
    rw [show (g+1)+(m+1+n) = 2+3*m from by omega,
        show 2+2*(m+1+n) = 2*m+2*n+4 from by ring] at this; exact this
  -- r3r1_chain
  have h4 : ⟨g+1, 2*m+2*n+4, 0, 2+2*m, 0⟩ [fm]⊢*
      ⟨g+1+(2*m+2*n+4), 0, 0, (2+2*m)+(2*m+2*n+4), 0⟩ :=
    r3r1_chain (2*m+2*n+4) g (2+2*m)
  have he1 : g+1+(2*m+2*n+4) = 4*m+n+5 := by omega
  have he2 : (2+2*m)+(2*m+2*n+4) = 4*m+2*n+6 := by ring
  rw [he1, he2] at h4
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4))

-- for odd a = 2m+3
theorem inner_odd (m n g : ℕ) (hg : n + g = 2 * m + 1) :
    ⟨0, 0, 2*m+3, 0, 2*m+3+n⟩ [fm]⊢* ⟨4*m+n+7, 0, 0, 4*m+2*n+8, 0⟩ := by
  -- opening
  have h1 : ⟨0, 0, 2*m+3, 0, 2*m+3+n⟩ [fm]⊢* ⟨2, 2, 2*m+1, 2, 2*m+2+n⟩ := by
    rw [show 2*m+3 = (2*m+1) + 2 from by ring,
        show 2*m+3+n = (2*m+2+n) + 1 from by ring]; exact opening
  -- r1r1r2_chain
  have h2 : ⟨2, 2, 2*m+1, 2, 2*m+2+n⟩ [fm]⊢* ⟨2+3*m, 2, 1, 2+2*m, m+2+n⟩ := by
    have := @r1r1r2_chain 1 m 2 2 (m+2+n)
    rw [show (m+2+n)+m = 2*m+2+n from by ring] at this; exact this
  -- r1_odd
  have h3 : ⟨2+3*m, 2, 1, 2+2*m, m+2+n⟩ [fm]⊢* ⟨3*m+4, 1, 0, 2*m+3, m+2+n⟩ := by
    have := @r1_odd (2+3*m) (2+2*m) (m+2+n)
    rw [show 2+3*m+2 = 3*m+4 from by ring, show 2+2*m+1 = 2*m+3 from by ring] at this
    exact this
  -- r2_drain
  have h4 : ⟨3*m+4, 1, 0, 2*m+3, m+2+n⟩ [fm]⊢* ⟨g+1, 2*m+2*n+5, 0, 2*m+3, 0⟩ := by
    have := @r2_drain (2*m+3) (m+2+n) (g+1) 1
    rw [show (g+1)+(m+2+n) = 3*m+4 from by omega,
        show 1+2*(m+2+n) = 2*m+2*n+5 from by ring] at this; exact this
  -- r3r1_chain
  have h5 : ⟨g+1, 2*m+2*n+5, 0, 2*m+3, 0⟩ [fm]⊢*
      ⟨g+1+(2*m+2*n+5), 0, 0, (2*m+3)+(2*m+2*n+5), 0⟩ :=
    r3r1_chain (2*m+2*n+5) g (2*m+3)
  have he1 : g+1+(2*m+2*n+5) = 4*m+n+7 := by omega
  have he2 : (2*m+3)+(2*m+2*n+5) = 4*m+2*n+8 := by ring
  rw [he1, he2] at h5
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem main_even (m n : ℕ) (hn : n ≤ 2*m) :
    ⟨2*m+2, 0, 0, 2*m+2+n, 0⟩ [fm]⊢⁺ ⟨4*m+n+5, 0, 0, 4*m+2*n+6, 0⟩ := by
  obtain ⟨g, hg⟩ : ∃ g, n + g = 2 * m := ⟨2*m - n, by omega⟩
  exact step_stepStar_stepPlus (show ⟨2*m+2, 0, 0, 2*m+2+n, 0⟩ [fm]⊢ ⟨2*m+1, 0, 1, 2*m+2+n, 0⟩ from rfl)
    (stepStar_trans (by
      have := @a_to_c 0 (2*m+2+n) (2*m+1) 1
      simp only [Nat.zero_add] at this
      rw [show 1 + (2*m+1) = 2*m+2 from by ring] at this; exact this)
    (stepStar_trans (by
      have := d_to_e (2*m+2+n) (2*m+2) 0
      simp only [Nat.zero_add] at this; exact this)
    (inner_even m n g hg)))

theorem main_odd (m n : ℕ) (hn : n ≤ 2*m+1) :
    ⟨2*m+3, 0, 0, 2*m+3+n, 0⟩ [fm]⊢⁺ ⟨4*m+n+7, 0, 0, 4*m+2*n+8, 0⟩ := by
  obtain ⟨g, hg⟩ : ∃ g, n + g = 2 * m + 1 := ⟨2*m+1 - n, by omega⟩
  exact step_stepStar_stepPlus (show ⟨2*m+3, 0, 0, 2*m+3+n, 0⟩ [fm]⊢ ⟨2*m+2, 0, 1, 2*m+3+n, 0⟩ from rfl)
    (stepStar_trans (by
      have := @a_to_c 0 (2*m+3+n) (2*m+2) 1
      simp only [Nat.zero_add] at this
      rw [show 1 + (2*m+2) = 2*m+3 from by ring] at this; exact this)
    (stepStar_trans (by
      have := d_to_e (2*m+3+n) (2*m+3) 0
      simp only [Nat.zero_add] at this; exact this)
    (inner_odd m n g hg)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩)
  · execute fm 4
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a n, q = ⟨a, 0, 0, a+n, 0⟩ ∧ a ≥ n + 2)
  · intro c ⟨a, n, hq, ha⟩; subst hq
    rcases Nat.even_or_odd a with ⟨K, hK⟩ | ⟨K, hK⟩
    · obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
      rw [show (m + 1) + (m + 1) = 2 * m + 2 from by ring] at hK; subst hK
      exact ⟨⟨4*m+n+5, 0, 0, 4*m+2*n+6, 0⟩,
        ⟨4*m+n+5, n+1, by ring_nf, by omega⟩,
        main_even m n (by omega)⟩
    · obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring] at hK; subst hK
      exact ⟨⟨4*m+n+7, 0, 0, 4*m+2*n+8, 0⟩,
        ⟨4*m+n+7, n+1, by ring_nf, by omega⟩,
        main_odd m n (by omega)⟩
  · exact ⟨2, 0, rfl, by omega⟩

end Sz22_2003_unofficial_540
