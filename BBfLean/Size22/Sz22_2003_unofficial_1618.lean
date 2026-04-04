import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1618: [77/15, 2/3, 9/14, 5/11, 231/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  0  0
-1  2  0 -1  0
 0  0  1  0 -1
-1  1  0  1  1
```

This Fractran program doesn't halt.

Canonical states: (n+1, 0, 0, 0, n) with linear growth.
Transition: (n+1, 0, 0, 0, n) -> (n+2, 0, 0, 0, n+1).

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1618

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e+1⟩
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

theorem middle_even : ∀ k, ∀ A D E,
    ⟨A + k + 1, 0, 2 * k, D + 1, E⟩ [fm]⊢* ⟨A + 1, 0, 0, D + k + 1, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · simp; exists 0
  · rw [show A + (k + 1) + 1 = (A + k + 1) + 1 from by ring,
        show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih A (D + 1) (E + 2))
    ring_nf; finish

theorem middle_odd : ∀ k, ∀ A D E,
    ⟨A + k + 1, 0, 2 * k + 1, D + 1, E⟩ [fm]⊢* ⟨A + 1, 0, 0, D + k + 1, E + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show A + (k + 1) + 1 = (A + k + 1) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 + 1 = (2 * k + 1) + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih A (D + 1) (E + 2))
    ring_nf; finish

-- n odd: n = 2m+1, canonical (2m+2, 0, 0, 0, 2m+1)
-- Phase 1: e_to_c: (2m+2, 0, 0, 0, 2m+1) -> (2m+2, 0, 2m+1, 0, 0)
-- Phase 2: R5: (2m+2, 0, 2m+1, 0, 0) -> (2m+1, 1, 2m+1, 1, 1)
-- Phase 3: R1: (2m+1, 1, 2m+1, 1, 1) -> (2m+1, 0, 2m, 2, 2)
-- Phase 4: middle_even m: (2m+1, 0, 2m, 2, 2) -> (m+1, 0, 0, m+2, 2m+2)
-- Phase 5: r3r2r2_drain: (m+1, 0, 0, m+2, 2m+2) -> (2m+3, 0, 0, 0, 2m+2)
theorem trans_odd_n (m : ℕ) :
    ⟨2 * m + 2, 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺ ⟨2 * m + 3, 0, 0, 0, 2 * m + 2⟩ := by
  have p1 : ⟨2 * m + 2, 0, 0, 0, 2 * m + 1⟩ [fm]⊢*
      ⟨2 * m + 2, 0, 2 * m + 1, 0, 0⟩ := by
    have h := e_to_c (2 * m + 1) (2 * m + 2) 0; simp at h; exact h
  have p2 : ⟨2 * m + 2, 0, 2 * m + 1, 0, 0⟩ [fm]⊢*
      ⟨2 * m + 1, 1, 2 * m + 1, 1, 1⟩ := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]; step fm; finish
  have p3 : ⟨2 * m + 1, 1, 2 * m + 1, 1, 1⟩ [fm]⊢*
      ⟨2 * m + 1, 0, 2 * m, 2, 2⟩ := by
    rw [show 2 * m + 1 = (2 * m) + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    step fm; ring_nf; finish
  have p4 : ⟨2 * m + 1, 0, 2 * m, 2, 2⟩ [fm]⊢*
      ⟨m + 1, 0, 0, m + 2, 2 * m + 2⟩ := by
    rw [show 2 * m + 1 = m + m + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    have h := middle_even m m 1 2
    rw [show 1 + m + 1 = m + 2 from by ring,
        show 2 + 2 * m = 2 * m + 2 from by ring] at h
    exact h
  have p5 : ⟨m + 1, 0, 0, m + 2, 2 * m + 2⟩ [fm]⊢*
      ⟨2 * m + 3, 0, 0, 0, 2 * m + 2⟩ := by
    rw [show m + 2 = (m + 1) + 1 from by ring]
    have h := r3r2r2_drain (m + 1) m (2 * m + 2)
    rw [show m + (m + 1) + 2 = 2 * m + 3 from by ring] at h
    exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3
    (stepStar_trans p4 p5)))) (by simp [Q])

-- n even: n = 2m+2, canonical (2m+3, 0, 0, 0, 2m+2)
-- Phase 1: e_to_c: (2m+3, 0, 0, 0, 2m+2) -> (2m+3, 0, 2m+2, 0, 0)
-- Phase 2: R5: (2m+3, 0, 2m+2, 0, 0) -> (2m+2, 1, 2m+2, 1, 1)
-- Phase 3: R1: (2m+2, 1, 2m+2, 1, 1) -> (2m+2, 0, 2m+1, 2, 2)
-- Phase 4: middle_odd m: (2m+2, 0, 2m+1, 2, 2) -> (m+2, 0, 0, m+2, 2m+3)
-- Phase 5: r3r2r2_drain: (m+2, 0, 0, m+2, 2m+3) -> (2m+4, 0, 0, 0, 2m+3)
theorem trans_even_n (m : ℕ) :
    ⟨2 * m + 3, 0, 0, 0, 2 * m + 2⟩ [fm]⊢⁺ ⟨2 * m + 4, 0, 0, 0, 2 * m + 3⟩ := by
  have p1 : ⟨2 * m + 3, 0, 0, 0, 2 * m + 2⟩ [fm]⊢*
      ⟨2 * m + 3, 0, 2 * m + 2, 0, 0⟩ := by
    have h := e_to_c (2 * m + 2) (2 * m + 3) 0; simp at h; exact h
  have p2 : ⟨2 * m + 3, 0, 2 * m + 2, 0, 0⟩ [fm]⊢*
      ⟨2 * m + 2, 1, 2 * m + 2, 1, 1⟩ := by
    rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]; step fm; finish
  have p3 : ⟨2 * m + 2, 1, 2 * m + 2, 1, 1⟩ [fm]⊢*
      ⟨2 * m + 2, 0, 2 * m + 1, 2, 2⟩ := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    step fm; ring_nf; finish
  have p4 : ⟨2 * m + 2, 0, 2 * m + 1, 2, 2⟩ [fm]⊢*
      ⟨m + 2, 0, 0, m + 2, 2 * m + 3⟩ := by
    rw [show 2 * m + 2 = (m + 1) + m + 1 from by ring,
        show 2 * m + 1 = 2 * m + 1 from rfl,
        show (2 : ℕ) = 1 + 1 from by ring]
    have h := middle_odd m (m + 1) 1 2
    rw [show m + 1 + 1 = m + 2 from by ring,
        show 1 + m + 1 = m + 2 from by ring,
        show 2 + 2 * m + 1 = 2 * m + 3 from by ring] at h
    exact h
  have p5 : ⟨m + 2, 0, 0, m + 2, 2 * m + 3⟩ [fm]⊢*
      ⟨2 * m + 4, 0, 0, 0, 2 * m + 3⟩ := by
    rw [show m + 2 = (m + 1) + 1 from by ring,
        show m + 2 = (m + 1) + 1 from by ring]
    have h := r3r2r2_drain (m + 1) (m + 1) (2 * m + 3)
    rw [show m + 1 + (m + 1) + 2 = 2 * m + 4 from by ring] at h
    exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3
    (stepStar_trans p4 p5)))) (by simp [Q])

theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, n + 1⟩ := by
  rcases n with _ | _ | n
  · execute fm 5
  · execute fm 9
  · rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- n = 2m, so n+2 = 2m+2 (even)
      subst hm
      have : m + m + 1 + 1 + 1 = 2 * m + 3 := by ring
      have : m + m + 1 + 1 = 2 * m + 2 := by ring
      have : m + m + 1 + 1 + 2 = 2 * m + 4 := by ring
      simp only [*]; exact trans_even_n m
    · -- n = 2m+1, so n+2 = 2m+3 (odd)
      subst hm
      have : 2 * m + 1 + 1 + 1 + 1 = 2 * (m + 1) + 2 := by ring
      have : 2 * m + 1 + 1 + 1 = 2 * (m + 1) + 1 := by ring
      have : 2 * m + 1 + 1 + 1 + 2 = 2 * (m + 1) + 3 := by ring
      simp only [*]; exact trans_odd_n (m + 1)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0, n⟩) 0
  intro n; exists n + 1
  exact main_trans n

end Sz22_2003_unofficial_1618
