import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1625: [77/15, 2/3, 9/14, 5/11, 99/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  0  0
-1  2  0 -1  0
 0  0  1  0 -1
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1625

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ A C, ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · step fm; apply stepStar_trans (ih A (C + 1)); ring_nf; finish

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

theorem r3r2r2_drain : ∀ k, ∀ A E,
    ⟨A + 1, 0, 0, k + 1, E⟩ [fm]⊢* ⟨A + k + 2, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show A + (k + 1) + 2 = (A + 1) + k + 2 from by ring]
    exact ih (A + 1) E

theorem trans_even (m : ℕ) :
    ⟨2 * m + 1, 0, 2 * m, 0, 0⟩ [fm]⊢⁺ ⟨2 * m + 2, 0, 2 * m + 1, 0, 0⟩ := by
  have p1 : ⟨2 * m + 1, 0, 2 * m, 0, 0⟩ [fm]⊢*
      ⟨2 * m, 2, 2 * m, 0, 1⟩ := by
    rw [show 2 * m + 1 = (2 * m) + 1 from by ring]; step fm; finish
  have p2 : ⟨2 * m, 2, 2 * m, 0, 1⟩ [fm]⊢*
      ⟨m, 2, 0, m, 2 * m + 1⟩ := by
    have h := r1r1r3_chain m m 0 0 1
    rw [show m + m = 2 * m from by ring,
        show 0 + 2 * m = 2 * m from by ring,
        show 0 + m = m from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring] at h
    exact h
  have p3 : ⟨m, 2, 0, m, 2 * m + 1⟩ [fm]⊢*
      ⟨m + 2, 0, 0, m, 2 * m + 1⟩ := by
    step fm; step fm; ring_nf; finish
  have p4 : ⟨m + 2, 0, 0, m, 2 * m + 1⟩ [fm]⊢*
      ⟨2 * m + 2, 0, 0, 0, 2 * m + 1⟩ := by
    rcases m with _ | m'
    · simp; exists 0
    · rw [show (m' + 1) + 2 = (m' + 2) + 1 from by ring,
          show (m' + 1 : ℕ) = m' + 1 from rfl]
      have h := r3r2r2_drain m' (m' + 2) (2 * (m' + 1) + 1)
      rw [show m' + 2 + m' + 2 = 2 * (m' + 1) + 2 from by ring] at h
      exact h
  have p5 : ⟨2 * m + 2, 0, 0, 0, 2 * m + 1⟩ [fm]⊢*
      ⟨2 * m + 2, 0, 2 * m + 1, 0, 0⟩ := by
    have h := e_to_c (2 * m + 1) (2 * m + 2) 0; simp at h; exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3
    (stepStar_trans p4 p5)))) (by simp [Q])

theorem trans_odd (m : ℕ) :
    ⟨2 * m + 2, 0, 2 * m + 1, 0, 0⟩ [fm]⊢⁺ ⟨2 * m + 3, 0, 2 * m + 2, 0, 0⟩ := by
  have p1 : ⟨2 * m + 2, 0, 2 * m + 1, 0, 0⟩ [fm]⊢*
      ⟨2 * m + 1, 2, 2 * m + 1, 0, 1⟩ := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]; step fm; finish
  have p2 : ⟨2 * m + 1, 2, 2 * m + 1, 0, 1⟩ [fm]⊢*
      ⟨m + 1, 2, 1, m, 2 * m + 1⟩ := by
    have h := r1r1r3_chain m (m + 1) 1 0 1
    rw [show m + 1 + m = 2 * m + 1 from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring,
        show 0 + m = m from by ring] at h
    exact h
  have p3 : ⟨m + 1, 2, 1, m, 2 * m + 1⟩ [fm]⊢*
      ⟨m + 2, 0, 0, m + 1, 2 * m + 2⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm; step fm; ring_nf; finish
  have p4 : ⟨m + 2, 0, 0, m + 1, 2 * m + 2⟩ [fm]⊢*
      ⟨2 * m + 3, 0, 0, 0, 2 * m + 2⟩ := by
    rw [show m + 2 = (m + 1) + 1 from by ring]
    have h := r3r2r2_drain m (m + 1) (2 * m + 2)
    rw [show m + 1 + m + 2 = 2 * m + 3 from by ring] at h
    exact h
  have p5 : ⟨2 * m + 3, 0, 0, 0, 2 * m + 2⟩ [fm]⊢*
      ⟨2 * m + 3, 0, 2 * m + 2, 0, 0⟩ := by
    have h := e_to_c (2 * m + 2) (2 * m + 3) 0; simp at h; exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3
    (stepStar_trans p4 p5)))) (by simp [Q])

theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, n, 0, 0⟩ [fm]⊢⁺ ⟨n + 2, 0, n + 1, 0, 0⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have h := trans_even m
    rwa [show 2 * m + 1 = m + m + 1 from by omega,
         show 2 * m = m + m from by omega] at h
  · subst hm
    exact trans_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, n + 1, 0, 0⟩) 0
  intro n; exists n + 1
  exact main_trans (n + 1)

end Sz22_2003_unofficial_1625
