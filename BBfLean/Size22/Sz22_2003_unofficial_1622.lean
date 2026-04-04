import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1622: [77/15, 2/3, 9/14, 5/11, 45/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  0  0
-1  2  0 -1  0
 0  0  1  0 -1
-1  2  1  0  0
```

This Fractran program doesn't halt.

Author: Claude
-/

namespace Sz22_2003_unofficial_1622

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ A C, ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · step fm; apply stepStar_trans (ih A (C + 1)); ring_nf; finish

theorem r3r2r2_drain : ∀ k, ∀ A E,
    ⟨A + 1, 0, 0, k + 1, E⟩ [fm]⊢* ⟨A + k + 2, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show A + (k + 1) + 2 = (A + 1) + k + 2 from by ring]
    exact ih (A + 1) E

theorem r1r1r3_chain : ∀ k, ∀ A C D E,
    ⟨A + k, 2, C + 2 * k, D, E⟩ [fm]⊢* ⟨A, 2, C, D + k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k + 1) + 1 from by ring]
    step fm
    rw [show C + 2 * k + 1 = (C + 2 * k) + 1 from by ring]
    step fm
    rw [show D + 1 + 1 = (D + 1) + 1 from by ring,
        show E + 1 + 1 = (E + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih A C (D + 1) (E + 2))
    ring_nf; finish

theorem odd_tail : ∀ A D E,
    ⟨A + 1, 0, 1, D + 1, E⟩ [fm]⊢* ⟨A + 1, 0, 0, D + 1, E + 1⟩ := by
  intro A D E
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm; ring_nf; finish

theorem trans_odd (k : ℕ) :
    ⟨2 * k + 2, 0, 2 * k + 1, 0, 0⟩ [fm]⊢⁺ ⟨2 * k + 3, 0, 2 * k + 2, 0, 0⟩ := by
  have p1 : ⟨2 * k + 2, 0, 2 * k + 1, 0, 0⟩ [fm]⊢*
      ⟨2 * k + 1, 2, 2 * k + 2, 0, 0⟩ := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]; step fm; ring_nf; finish
  have p2 : ⟨2 * k + 1, 2, 2 * k + 2, 0, 0⟩ [fm]⊢*
      ⟨k + 1, 2, 2, k, 2 * k⟩ := by
    rw [show 2 * k + 1 = (k + 1) + k from by ring,
        show 2 * k + 2 = 2 + 2 * k from by ring]
    have h := r1r1r3_chain k (k + 1) 2 0 0
    rw [show 0 + k = k from by ring, show 0 + 2 * k = 2 * k from by ring] at h
    exact h
  have p3 : ⟨k + 1, 2, 2, k, 2 * k⟩ [fm]⊢*
      ⟨k + 1, 0, 0, k + 2, 2 * k + 2⟩ := by
    rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
    step fm; step fm; ring_nf; finish
  have p4 : ⟨k + 1, 0, 0, k + 2, 2 * k + 2⟩ [fm]⊢*
      ⟨2 * k + 3, 0, 0, 0, 2 * k + 2⟩ := by
    rw [show k + 1 = k + 1 from by ring,
        show k + 2 = (k + 1) + 1 from by ring]
    have h := r3r2r2_drain (k + 1) k (2 * k + 2)
    rw [show k + (k + 1) + 2 = 2 * k + 3 from by ring] at h
    exact h
  have p5 : ⟨2 * k + 3, 0, 0, 0, 2 * k + 2⟩ [fm]⊢*
      ⟨2 * k + 3, 0, 2 * k + 2, 0, 0⟩ := by
    have h := e_to_c (2 * k + 2) (2 * k + 3) 0; simp at h; exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3
    (stepStar_trans p4 p5)))) (by simp [Q])

theorem trans_even (k : ℕ) :
    ⟨2 * k + 3, 0, 2 * k + 2, 0, 0⟩ [fm]⊢⁺ ⟨2 * k + 4, 0, 2 * k + 3, 0, 0⟩ := by
  have p1 : ⟨2 * k + 3, 0, 2 * k + 2, 0, 0⟩ [fm]⊢*
      ⟨2 * k + 2, 2, 2 * k + 3, 0, 0⟩ := by
    rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring]; step fm; ring_nf; finish
  have p2 : ⟨2 * k + 2, 2, 2 * k + 3, 0, 0⟩ [fm]⊢*
      ⟨k + 2, 2, 3, k, 2 * k⟩ := by
    rw [show 2 * k + 2 = (k + 2) + k from by ring,
        show 2 * k + 3 = 3 + 2 * k from by ring]
    have h := r1r1r3_chain k (k + 2) 3 0 0
    rw [show 0 + k = k from by ring, show 0 + 2 * k = 2 * k from by ring] at h
    exact h
  have p3 : ⟨k + 2, 2, 3, k, 2 * k⟩ [fm]⊢*
      ⟨k + 2, 0, 1, k + 2, 2 * k + 2⟩ := by
    rw [show (3 : ℕ) = 1 + 1 + 1 from by ring]
    step fm; step fm; ring_nf; finish
  have p4 : ⟨k + 2, 0, 1, k + 2, 2 * k + 2⟩ [fm]⊢*
      ⟨k + 2, 0, 0, k + 2, 2 * k + 3⟩ := by
    rw [show k + 2 = (k + 1) + 1 from by ring,
        show k + 2 = (k + 1) + 1 from by ring]
    have h := odd_tail (k + 1) (k + 1) (2 * k + 2)
    rw [show k + 1 + 1 = k + 2 from by ring,
        show 2 * k + 2 + 1 = 2 * k + 3 from by ring] at h
    exact h
  have p5 : ⟨k + 2, 0, 0, k + 2, 2 * k + 3⟩ [fm]⊢*
      ⟨2 * k + 4, 0, 0, 0, 2 * k + 3⟩ := by
    rw [show k + 2 = (k + 1) + 1 from by ring,
        show k + 2 = (k + 1) + 1 from by ring]
    have h := r3r2r2_drain (k + 1) (k + 1) (2 * k + 3)
    rw [show k + 1 + (k + 1) + 2 = 2 * k + 4 from by ring] at h
    exact h
  have p6 : ⟨2 * k + 4, 0, 0, 0, 2 * k + 3⟩ [fm]⊢*
      ⟨2 * k + 4, 0, 2 * k + 3, 0, 0⟩ := by
    have h := e_to_c (2 * k + 3) (2 * k + 4) 0; simp at h; exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3
    (stepStar_trans p4 (stepStar_trans p5 p6))))) (by simp [Q])

theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, n + 1, 0, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, n + 2, 0, 0⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    show ⟨k + k + 2, 0, k + k + 1, 0, 0⟩ [fm]⊢⁺ ⟨k + k + 3, 0, k + k + 2, 0, 0⟩
    rw [show k + k + 2 = 2 * k + 2 from by ring,
        show k + k + 1 = 2 * k + 1 from by ring,
        show k + k + 3 = 2 * k + 3 from by ring]
    exact trans_odd k
  · subst hk
    show ⟨2 * k + 1 + 2, 0, 2 * k + 1 + 1, 0, 0⟩ [fm]⊢⁺ ⟨2 * k + 1 + 3, 0, 2 * k + 1 + 2, 0, 0⟩
    rw [show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
        show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
        show 2 * k + 1 + 3 = 2 * k + 4 from by ring]
    exact trans_even k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, n + 1, 0, 0⟩) 0
  intro n; exists n + 1
  exact main_trans n

end Sz22_2003_unofficial_1622
