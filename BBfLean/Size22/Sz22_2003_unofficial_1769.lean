import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1769: [9/10, 245/33, 28/3, 11/7, 3/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1  2 -1
 2 -1  0  1  0
 0  0  0 -1  1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1769

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem d_to_e : ∀ k, ∀ d e, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    show ⟨a, 0, 0, d + k, e + 1⟩ [fm]⊢* ⟨a, 0, 0, d, e + (k + 1)⟩
    apply stepStar_trans (ih d (e + 1)); ring_nf; finish


theorem r2r1_chain : ∀ k, ∀ b D e,
    ⟨k + 1, b + 1, 0, D, e + k + 1⟩ [fm]⊢*
    ⟨0, b + k + 2, 0, D + 2 * k + 2, e⟩ := by
  intro k; induction' k with k ih <;> intro b D e
  · step fm; step fm; finish
  · show ⟨(k + 1) + 1, b + 1, 0, D, (e + (k + 1)) + 1⟩ [fm]⊢* _
    step fm; step fm
    show ⟨k + 1, (b + 1) + 1, 0, D + 2, e + k + 1⟩ [fm]⊢*
      ⟨0, b + (k + 1) + 2, 0, D + 2 * (k + 1) + 2, e⟩
    apply stepStar_trans (ih (b + 1) (D + 2) e); ring_nf; finish

theorem r2_drain : ∀ k, ∀ b c D,
    ⟨0, b + k + 1, c, D, k + 1⟩ [fm]⊢* ⟨0, b, c + k + 1, D + 2 * k + 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c D
  · step fm; finish
  · show ⟨0, (b + (k + 1)) + 1, c, D, (k + 1) + 1⟩ [fm]⊢* _
    step fm
    show ⟨0, b + k + 1, c + 1, D + 2, k + 1⟩ [fm]⊢*
      ⟨0, b, c + (k + 1) + 1, D + 2 * (k + 1) + 2, 0⟩
    apply stepStar_trans (ih b (c + 1) (D + 2)); ring_nf; finish

theorem r3r1r1_even : ∀ k, ∀ b D,
    ⟨0, b + 1, 2 * (k + 1), D, 0⟩ [fm]⊢* ⟨0, b + 3 * (k + 1) + 1, 0, D + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro b D
  · show ⟨0, b + 1, 1 + 1, D, 0⟩ [fm]⊢* _; step fm; step fm; step fm; ring_nf; finish
  · show ⟨0, b + 1, (2 * (k + 1) + 1) + 1, D, 0⟩ [fm]⊢* _
    step fm; step fm; step fm
    show ⟨0, (b + 3) + 1, 2 * (k + 1), D + 1, 0⟩ [fm]⊢*
      ⟨0, b + 3 * (k + 1 + 1) + 1, 0, D + (k + 1) + 1, 0⟩
    apply stepStar_trans (ih (b + 3) (D + 1)); ring_nf; finish

theorem r3r1r1_odd : ∀ k, ∀ b D,
    ⟨0, b + 1, 2 * k + 1, D, 0⟩ [fm]⊢* ⟨1, b + 3 * k + 2, 0, D + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro b D
  · step fm; step fm; finish
  · show ⟨0, b + 1, (2 * k + 1) + 1 + 1, D, 0⟩ [fm]⊢* _
    step fm; step fm; step fm
    show ⟨0, (b + 3) + 1, 2 * k + 1, D + 1, 0⟩ [fm]⊢*
      ⟨1, b + 3 * (k + 1) + 2, 0, D + (k + 1) + 1, 0⟩
    apply stepStar_trans (ih (b + 3) (D + 1)); ring_nf; finish

theorem r3_chain : ∀ k, ∀ a D,
    ⟨a + 1, k + 1, 0, D, 0⟩ [fm]⊢* ⟨a + 2 * k + 3, 0, 0, D + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a D
  · step fm; finish
  · step fm
    show ⟨(a + 2) + 1, k + 1, 0, D + 1, 0⟩ [fm]⊢*
      ⟨a + 2 * (k + 1) + 3, 0, 0, D + (k + 1) + 1, 0⟩
    apply stepStar_trans (ih (a + 2) (D + 1)); ring_nf; finish

theorem r3_chain0 : ∀ k, ∀ D,
    ⟨0, k + 1, 0, D, 0⟩ [fm]⊢* ⟨2 * k + 2, 0, 0, D + k + 1, 0⟩ := by
  intro k D; step fm
  show ⟨1 + 1, k, 0, D + 1, 0⟩ [fm]⊢* ⟨2 * k + 2, 0, 0, D + k + 1, 0⟩
  rcases k with _ | k
  · finish
  · show ⟨1 + 1, k + 1, 0, D + 1, 0⟩ [fm]⊢* _
    apply stepStar_trans (r3_chain k 1 (D + 1)); ring_nf; finish

theorem d_to_e_r5 : ∀ D, ⟨a + 1, 0, 0, D, 0⟩ [fm]⊢⁺ ⟨a, 1, 0, 0, D⟩ := by
  intro D
  rw [show D = 0 + D from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e D 0 0 (a := a + 1))
  step fm; finish

-- Main transition c0=0
theorem main_trans_c0 :
    ⟨f + 2, 0, 0, f + 1, 0⟩ [fm]⊢⁺ ⟨2 * f + 4, 0, 0, 3 * f + 4, 0⟩ := by
  rw [show f + 2 = (f + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (d_to_e_r5 (f + 1) (a := f + 1))
  -- (f+1, 1, 0, 0, f+1). Need to match r2r1_chain(f, 0, 0, 0).
  have h : ⟨f + 1, 1, 0, 0, f + 1⟩ [fm]⊢* ⟨0, f + 2, 0, 2 * f + 2, (0 : ℕ)⟩ := by
    have := r2r1_chain f 0 0 0
    simp only [Nat.zero_add] at this; exact this
  apply stepStar_trans h
  show ⟨0, (f + 1) + 1, 0, 2 * f + 2, 0⟩ [fm]⊢* _
  apply stepStar_trans (r3_chain0 (f + 1) (2 * f + 2))
  ring_nf; finish

-- Main transition c0 = 2k+1 (odd)
theorem main_trans_odd :
    ⟨f + 2 * k + 3, 0, 0, f + 4 * k + 3, 0⟩ [fm]⊢⁺
    ⟨2 * f + 6 * k + 7, 0, 0, 3 * f + 12 * k + 10, 0⟩ := by
  rw [show f + 2 * k + 3 = (f + 2 * k + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (d_to_e_r5 (f + 4 * k + 3))
  have h1 : ⟨f + 2 * k + 2, 1, 0, 0, f + 4 * k + 3⟩ [fm]⊢*
      ⟨0, f + 2 * k + 3, 0, 2 * f + 4 * k + 4, 2 * k + 1⟩ := by
    have := r2r1_chain (f + 2 * k + 1) 0 0 (2 * k + 1)
    simp only [Nat.zero_add] at this; convert this using 2; all_goals ring_nf
  apply stepStar_trans h1
  have h2 : ⟨0, f + 2 * k + 3, 0, 2 * f + 4 * k + 4, 2 * k + 1⟩ [fm]⊢*
      ⟨0, f + 2, 2 * k + 1, 2 * f + 8 * k + 6, (0 : ℕ)⟩ := by
    have := r2_drain (2 * k) (f + 2) 0 (2 * f + 4 * k + 4)
    simp only [Nat.zero_add] at this
    ring_nf at this ⊢; exact this
  apply stepStar_trans h2
  show ⟨0, (f + 1) + 1, 2 * k + 1, 2 * f + 8 * k + 6, 0⟩ [fm]⊢* _
  apply stepStar_trans (r3r1r1_odd k (f + 1) (2 * f + 8 * k + 6))
  have h3 : ⟨1, f + 3 * k + 3, 0, 2 * f + 9 * k + 7, 0⟩ [fm]⊢*
      ⟨2 * f + 6 * k + 7, 0, 0, 3 * f + 12 * k + 10, (0 : ℕ)⟩ := by
    have := r3_chain (f + 3 * k + 2) 0 (2 * f + 9 * k + 7)
    ring_nf at this ⊢; exact this
  rw [show f + 1 + 3 * k + 2 = f + 3 * k + 3 from by ring,
      show 2 * f + 8 * k + 6 + k + 1 = 2 * f + 9 * k + 7 from by ring]
  apply stepStar_trans h3
  ring_nf; finish

-- Main transition c0 = 2*(k+1) (even)
theorem main_trans_even :
    ⟨f + 2 * k + 4, 0, 0, f + 4 * k + 5, 0⟩ [fm]⊢⁺
    ⟨2 * f + 6 * k + 10, 0, 0, 3 * f + 12 * k + 16, 0⟩ := by
  rw [show f + 2 * k + 4 = (f + 2 * k + 3) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (d_to_e_r5 (f + 4 * k + 5))
  have h1 : ⟨f + 2 * k + 3, 1, 0, 0, f + 4 * k + 5⟩ [fm]⊢*
      ⟨0, f + 2 * k + 4, 0, 2 * f + 4 * k + 6, 2 * k + 2⟩ := by
    have := r2r1_chain (f + 2 * k + 2) 0 0 (2 * k + 2)
    simp only [Nat.zero_add] at this; convert this using 2; all_goals ring_nf
  apply stepStar_trans h1
  have h2 : ⟨0, f + 2 * k + 4, 0, 2 * f + 4 * k + 6, 2 * k + 2⟩ [fm]⊢*
      ⟨0, f + 2, 2 * (k + 1), 2 * f + 8 * k + 10, (0 : ℕ)⟩ := by
    have := r2_drain (2 * k + 1) (f + 2) 0 (2 * f + 4 * k + 6)
    simp only [Nat.zero_add] at this; ring_nf at this ⊢; exact this
  apply stepStar_trans h2
  show ⟨0, (f + 1) + 1, 2 * (k + 1), 2 * f + 8 * k + 10, 0⟩ [fm]⊢* _
  apply stepStar_trans (r3r1r1_even k (f + 1) (2 * f + 8 * k + 10))
  have h3 : ⟨0, f + 3 * k + 5, 0, 2 * f + 9 * k + 11, 0⟩ [fm]⊢*
      ⟨2 * f + 6 * k + 10, 0, 0, 3 * f + 12 * k + 16, (0 : ℕ)⟩ := by
    have := r3_chain0 (f + 3 * k + 4) (2 * f + 9 * k + 11)
    ring_nf at this ⊢; exact this
  rw [show f + 1 + 3 * (k + 1) + 1 = f + 3 * k + 5 from by ring,
      show 2 * f + 8 * k + 10 + k + 1 = 2 * f + 9 * k + 11 from by ring]
  apply stepStar_trans h3
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨f, c0⟩ ↦ ⟨f + c0 + 2, 0, 0, f + 2 * c0 + 1, 0⟩) ⟨0, 0⟩
  intro ⟨f, c0⟩
  rcases c0 with _ | c0
  · -- c0 = 0
    refine ⟨⟨f + 1, f + 1⟩, ?_⟩
    change ⟨f + 0 + 2, 0, 0, f + 2 * 0 + 1, 0⟩ [fm]⊢⁺
      ⟨(f + 1) + (f + 1) + 2, 0, 0, (f + 1) + 2 * (f + 1) + 1, 0⟩
    rw [show f + 0 + 2 = f + 2 from by ring,
        show f + 2 * 0 + 1 = f + 1 from by ring,
        show (f + 1) + (f + 1) + 2 = 2 * f + 4 from by ring,
        show (f + 1) + 2 * (f + 1) + 1 = 3 * f + 4 from by ring]
    exact main_trans_c0
  · rcases Nat.even_or_odd c0 with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- c0 = 2k, c0+1 = 2k+1 (odd)
      subst hk
      refine ⟨⟨f + 1, f + 6 * k + 4⟩, ?_⟩
      change ⟨f + (k + k + 1) + 2, 0, 0, f + 2 * (k + k + 1) + 1, 0⟩ [fm]⊢⁺
        ⟨(f + 1) + (f + 6 * k + 4) + 2, 0, 0, (f + 1) + 2 * (f + 6 * k + 4) + 1, 0⟩
      rw [show f + (k + k + 1) + 2 = f + 2 * k + 3 from by ring,
          show f + 2 * (k + k + 1) + 1 = f + 4 * k + 3 from by ring,
          show (f + 1) + (f + 6 * k + 4) + 2 = 2 * f + 6 * k + 7 from by ring,
          show (f + 1) + 2 * (f + 6 * k + 4) + 1 = 3 * f + 12 * k + 10 from by ring]
      exact main_trans_odd
    · -- c0 = 2k+1, c0+1 = 2(k+1) (even)
      subst hk
      refine ⟨⟨f + 1, f + 6 * k + 7⟩, ?_⟩
      change ⟨f + (2 * k + 1 + 1) + 2, 0, 0, f + 2 * (2 * k + 1 + 1) + 1, 0⟩ [fm]⊢⁺
        ⟨(f + 1) + (f + 6 * k + 7) + 2, 0, 0, (f + 1) + 2 * (f + 6 * k + 7) + 1, 0⟩
      rw [show f + (2 * k + 1 + 1) + 2 = f + 2 * k + 4 from by ring,
          show f + 2 * (2 * k + 1 + 1) + 1 = f + 4 * k + 5 from by ring,
          show (f + 1) + (f + 6 * k + 7) + 2 = 2 * f + 6 * k + 10 from by ring,
          show (f + 1) + 2 * (f + 6 * k + 7) + 1 = 3 * f + 12 * k + 16 from by ring]
      exact main_trans_even
