import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1664: [77/15, 4/3, 99/14, 5/11, 21/2]

Vector representation:
```
 0 -1 -1  1  1
 2 -1  0  0  0
-1  2  0 -1  1
 0  0  1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1664

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k A C, ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · step fm; rw [show C + (k + 1) = (C + 1) + k from by ring]; exact ih A (C + 1)

theorem r3r2r2_chain : ∀ k F E,
    ⟨F + 1, 0, 0, k, E⟩ [fm]⊢* ⟨F + 3 * k + 1, 0, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro F E
  · exists 0
  · step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show F + 2 + 2 = (F + 3) + 1 from by ring]
    apply stepStar_trans (ih (F + 3) (E + 1))
    ring_nf; finish

theorem interleave_even : ∀ K A D E,
    ⟨A + K + 1, 0, 2 * K, D + 1, E⟩ [fm]⊢*
    ⟨A + 1, 0, 0, D + K + 1, E + 3 * K⟩ := by
  intro K; induction' K with K ih <;> intro A D E
  · exists 0
  · rw [show A + (K + 1) + 1 = (A + K + 1) + 1 from by ring,
        show 2 * (K + 1) = (2 * K + 1) + 1 from by ring,
        show (D + 1 : ℕ) = D + 1 from rfl]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show 2 * K + 1 = (2 * K) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show D + 1 + 1 = (D + 1) + 1 from by ring,
        show E + 1 + 1 + 1 = E + 3 from by ring]
    apply stepStar_trans (ih A (D + 1) (E + 3))
    rw [show (D + 1) + K + 1 = D + (K + 1) + 1 from by ring,
        show (E + 3) + 3 * K = E + 3 * (K + 1) from by ring]
    finish

theorem interleave_odd : ∀ K A D E,
    ⟨A + K + 1, 0, 2 * K + 1, D + 1, E⟩ [fm]⊢*
    ⟨A + 2, 0, 0, D + K + 1, E + 3 * K + 2⟩ := by
  intro K; induction' K with K ih <;> intro A D E
  · rw [show A + 0 + 1 = A + 1 from by ring,
        show (D + 1 : ℕ) = D + 1 from rfl]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    ring_nf; finish
  · rw [show A + (K + 1) + 1 = (A + K + 1) + 1 from by ring,
        show 2 * (K + 1) + 1 = (2 * K + 1 + 1) + 1 from by ring,
        show (D + 1 : ℕ) = D + 1 from rfl]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show 2 * K + 1 + 1 = (2 * K + 1) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show D + 1 + 1 = (D + 1) + 1 from by ring,
        show E + 1 + 1 + 1 = E + 3 from by ring]
    apply stepStar_trans (ih A (D + 1) (E + 3))
    rw [show (D + 1) + K + 1 = D + (K + 1) + 1 from by ring,
        show (E + 3) + 3 * K + 2 = E + 3 * (K + 1) + 2 from by ring]
    finish

theorem main_trans (e F : ℕ) :
    ⟨e + F + 5, 0, 0, 0, e + 1⟩ [fm]⊢⁺
    ⟨2 * e + F + 10, 0, 0, 0, 2 * e + 3⟩ := by
  have p1 : ⟨e + F + 5, 0, 0, 0, e + 1⟩ [fm]⊢*
            ⟨e + F + 5, 0, e + 1, 0, 0⟩ := by
    have h := r4_chain (e + 1) (e + F + 5) 0; simp at h; exact h
  have p2 : ⟨e + F + 5, 0, e + 1, 0, 0⟩ [fm]⊢⁺
            ⟨e + F + 4, 1, e + 1, 1, 0⟩ := by
    rw [show e + F + 5 = (e + F + 4) + 1 from by ring]
    step fm; finish
  have p3 : ⟨e + F + 4, 1, e + 1, 1, 0⟩ [fm]⊢*
            ⟨e + F + 4, 0, e, 2, 1⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show e + 1 = e + 1 from rfl]
    step fm; ring_nf; finish
  rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
  · have p4 : ⟨e + F + 4, 0, e, 2, 1⟩ [fm]⊢*
              ⟨K + F + 4, 0, 0, K + 2, 3 * K + 1⟩ := by
      rw [show e + F + 4 = (K + F + 3) + K + 1 from by omega,
          show e = 2 * K from by omega,
          show (2 : ℕ) = 1 + 1 from rfl]
      have h := interleave_even K (K + F + 3) 1 1
      apply stepStar_trans h
      rw [show (K + F + 3) + 1 = K + F + 4 from by ring,
          show 1 + K + 1 = K + 2 from by ring,
          show 1 + 3 * K = 3 * K + 1 from by ring]
      finish
    have p5 : ⟨K + F + 4, 0, 0, K + 2, 3 * K + 1⟩ [fm]⊢*
              ⟨4 * K + F + 10, 0, 0, 0, 4 * K + 3⟩ := by
      rw [show K + F + 4 = (K + F + 3) + 1 from by ring]
      have h := r3r2r2_chain (K + 2) (K + F + 3) (3 * K + 1)
      apply stepStar_trans h
      rw [show (K + F + 3) + 3 * (K + 2) + 1 = 4 * K + F + 10 from by ring,
          show (3 * K + 1) + (K + 2) = 4 * K + 3 from by ring]
      finish
    rw [show 2 * e + F + 10 = 4 * K + F + 10 from by omega,
        show 2 * e + 3 = 4 * K + 3 from by omega]
    exact stepStar_stepPlus_stepPlus p1
      (stepPlus_stepStar_stepPlus p2 (stepStar_trans p3 (stepStar_trans p4 p5)))
  · have p4 : ⟨e + F + 4, 0, e, 2, 1⟩ [fm]⊢*
              ⟨K + F + 6, 0, 0, K + 2, 3 * K + 3⟩ := by
      rw [show e + F + 4 = (K + F + 4) + K + 1 from by omega,
          show e = 2 * K + 1 from by omega,
          show (2 : ℕ) = 1 + 1 from rfl]
      have h := interleave_odd K (K + F + 4) 1 1
      apply stepStar_trans h
      rw [show (K + F + 4) + 2 = K + F + 6 from by ring,
          show 1 + K + 1 = K + 2 from by ring,
          show 1 + 3 * K + 2 = 3 * K + 3 from by ring]
      finish
    have p5 : ⟨K + F + 6, 0, 0, K + 2, 3 * K + 3⟩ [fm]⊢*
              ⟨4 * K + F + 12, 0, 0, 0, 4 * K + 5⟩ := by
      rw [show K + F + 6 = (K + F + 5) + 1 from by ring]
      have h := r3r2r2_chain (K + 2) (K + F + 5) (3 * K + 3)
      apply stepStar_trans h
      rw [show (K + F + 5) + 3 * (K + 2) + 1 = 4 * K + F + 12 from by ring,
          show (3 * K + 3) + (K + 2) = 4 * K + 5 from by ring]
      finish
    rw [show 2 * e + F + 10 = 4 * K + F + 12 from by omega,
        show 2 * e + 3 = 4 * K + 5 from by omega]
    exact stepStar_stepPlus_stepPlus p1
      (stepPlus_stepStar_stepPlus p2 (stepStar_trans p3 (stepStar_trans p4 p5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 1⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + p.2 + 5, 0, 0, 0, p.1 + 1⟩) ⟨0, 0⟩
  intro ⟨e, F⟩
  refine ⟨⟨2 * e + 2, F + 3⟩, ?_⟩
  show ⟨e + F + 5, 0, 0, 0, e + 1⟩ [fm]⊢⁺
    ⟨(2 * e + 2) + (F + 3) + 5, 0, 0, 0, (2 * e + 2) + 1⟩
  rw [show (2 * e + 2) + (F + 3) + 5 = 2 * e + F + 10 from by ring,
      show (2 * e + 2) + 1 = 2 * e + 3 from by ring]
  exact main_trans e F

end Sz22_2003_unofficial_1664
