import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #674: [35/6, 28/55, 847/2, 3/7, 5/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  1 -1
-1  0  0  1  2
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_674

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem d_to_b : ∀ k, ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (b := b + 1) (d := d))
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ c d e, ⟨(0 : ℕ), b + 2 * k, c + 1, d, e + k⟩ [fm]⊢*
    ⟨0, b, c + 1 + k, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 1) (d + 3) e)
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a d, ⟨a, (0 : ℕ), c + k + 1, d, k + 1⟩ [fm]⊢*
    ⟨a + 2 * k + 2, 0, c, d + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; finish
  · rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) (d + 1))
    ring_nf; finish

theorem r3r2r2_chain : ∀ k, ∀ a d, ⟨a + 1, (0 : ℕ), c + 2 * k, d, 0⟩ [fm]⊢*
    ⟨a + 1 + 3 * k, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (d + 3))
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ d e, ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1) (e + 2))
    ring_nf; finish

theorem tail : ⟨a + 1, (0 : ℕ), 1, d, 0⟩ [fm]⊢* ⟨a + 1, 0, 0, d + 3, 3⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem phase_c_even (M : ℕ) (a d : ℕ) : ⟨a + 1, (0 : ℕ), 2 * M, d, 0⟩ [fm]⊢*
    ⟨0, 0, 0, d + a + 1 + 6 * M, 2 * a + 2 + 6 * M⟩ := by
  rw [show (2 : ℕ) * M = 0 + 2 * M from by ring]
  apply stepStar_trans (r3r2r2_chain M (c := 0) a d)
  apply stepStar_trans (r3_drain (a + 1 + 3 * M) (d + 3 * M) 0)
  ring_nf; finish

theorem phase_c_odd (M : ℕ) (a d : ℕ) : ⟨a + 1, (0 : ℕ), 2 * M + 1, d, 0⟩ [fm]⊢*
    ⟨0, 0, 0, d + a + 4 + 6 * M, 2 * a + 5 + 6 * M⟩ := by
  rw [show (2 : ℕ) * M + 1 = 1 + 2 * M from by ring]
  apply stepStar_trans (r3r2r2_chain M (c := 1) a d)
  rw [show a + 1 + 3 * M = a + 3 * M + 1 from by ring]
  apply stepStar_trans (tail (a := a + 3 * M) (d := d + 3 * M))
  rw [show a + 3 * M + 1 = a + 1 + 3 * M from by ring]
  apply stepStar_trans (r3_drain (a + 1 + 3 * M) (d + 3 * M + 3) 3)
  ring_nf; finish

theorem phase_b_a0 (c : ℕ) : ⟨(0 : ℕ), 2 * c + 1, 1, 0, c + 1⟩ [fm]⊢*
    ⟨1, 0, c + 1, 3 * c + 2, 0⟩ := by
  rw [show (2 : ℕ) * c + 1 = 1 + 2 * c from by ring,
      show c + 1 = 1 + c from by ring]
  apply stepStar_trans (r2r1r1_chain c (b := 1) 0 0 1)
  rw [show (0 : ℕ) + 1 + c = c + 1 from by ring,
      show (0 : ℕ) + 3 * c = 3 * c from by ring]
  step fm; step fm; ring_nf; finish

theorem phase_b_even (m c : ℕ) : ⟨(0 : ℕ), 2 * m + 2 * c + 3, 1, 0, 2 * m + c + 3⟩ [fm]⊢*
    ⟨2 * m + 3, 0, c + 1, 4 * m + 3 * c + 6, 0⟩ := by
  rw [show (2 : ℕ) * m + 2 * c + 3 = 1 + 2 * (m + c + 1) from by ring,
      show (2 : ℕ) * m + c + 3 = (m + 2) + (m + c + 1) from by ring]
  apply stepStar_trans (r2r1r1_chain (m + c + 1) (b := 1) 0 0 (m + 2))
  rw [show (0 : ℕ) + 1 + (m + c + 1) = (m + c + 1) + 1 from by ring,
      show (0 : ℕ) + 3 * (m + c + 1) = 3 * m + 3 * c + 3 from by ring,
      show (m + 2 : ℕ) = (m + 1) + 1 from by ring]
  step fm; step fm
  rw [show m + c + 1 + 1 = (c + 1) + m + 1 from by ring,
      show 3 * m + 3 * c + 3 + 1 + 1 = 3 * m + 3 * c + 5 from by ring]
  apply stepStar_trans (r2_drain m (c := c + 1) 1 (3 * m + 3 * c + 5))
  ring_nf; finish

theorem phase_b_odd (m c : ℕ) : ⟨(0 : ℕ), 2 * m + 2 * c + 2, 1, 0, 2 * m + c + 2⟩ [fm]⊢*
    ⟨2 * m + 2, 0, c + 1, 4 * m + 3 * c + 4, 0⟩ := by
  rw [show (2 : ℕ) * m + 2 * c + 2 = 0 + 2 * (m + c + 1) from by ring,
      show (2 : ℕ) * m + c + 2 = (m + 1) + (m + c + 1) from by ring]
  apply stepStar_trans (r2r1r1_chain (m + c + 1) (b := 0) 0 0 (m + 1))
  rw [show (0 : ℕ) + 1 + (m + c + 1) = (c + 1) + m + 1 from by ring,
      show (0 : ℕ) + 3 * (m + c + 1) = 3 * m + 3 * c + 3 from by ring]
  apply stepStar_trans (r2_drain m (c := c + 1) 0 (3 * m + 3 * c + 3))
  ring_nf; finish

theorem main_trans (a c : ℕ) : ⟨(0 : ℕ), 0, 0, a + 2 * c + 1, a + c + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 3 * a + 6 * c + 6, 2 * a + 3 * c + 5⟩ := by
  rw [show a + 2 * c + 1 = 0 + (a + 2 * c + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (a + 2 * c + 1) (b := 0) (d := 0) (e := a + c + 2))
  rw [show (0 : ℕ) + (a + 2 * c + 1) = a + 2 * c + 1 from by ring,
      show a + c + 2 = (a + c + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (show (0, a + 2 * c + 1, 0, 0, (a + c + 1) + 1) [fm]⊢
      (0, a + 2 * c + 1, 1, 0, a + c + 1) from by rfl)
  rcases Nat.even_or_odd a with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rcases m with _ | m
    · -- a = 0
      simp only [Nat.zero_add]
      apply stepStar_trans (phase_b_a0 c)
      rcases Nat.even_or_odd c with ⟨j, hj⟩ | ⟨j, hj⟩
      · subst hj
        rw [show j + j + 1 = 2 * j + 1 from by ring]
        apply stepStar_trans (phase_c_odd j 0 (3 * (j + j) + 2))
        ring_nf; finish
      · subst hj
        rw [show (2 : ℕ) * j + 1 + 1 = 2 * (j + 1) from by ring]
        apply stepStar_trans (phase_c_even (j + 1) 0 (3 * (2 * j + 1) + 2))
        ring_nf; finish
    · -- a = 2*(m+1) = 2m+2
      rw [show (m + 1) + (m + 1) + 2 * c + 1 = 2 * m + 2 * c + 3 from by ring,
          show (m + 1) + (m + 1) + c + 1 = 2 * m + c + 3 from by ring]
      apply stepStar_trans (phase_b_even m c)
      rcases Nat.even_or_odd c with ⟨j, hj⟩ | ⟨j, hj⟩
      · subst hj
        rw [show j + j + 1 = 2 * j + 1 from by ring,
            show (2 : ℕ) * m + 3 = (2 * m + 2) + 1 from by ring]
        apply stepStar_trans (phase_c_odd j (2 * m + 2) (4 * m + 3 * (j + j) + 6))
        ring_nf; finish
      · subst hj
        rw [show (2 : ℕ) * j + 1 + 1 = 2 * (j + 1) from by ring,
            show (2 : ℕ) * m + 3 = (2 * m + 2) + 1 from by ring]
        apply stepStar_trans (phase_c_even (j + 1) (2 * m + 2)
          (4 * m + 3 * (2 * j + 1) + 6))
        ring_nf; finish
  · subst hm
    -- a = 2m+1
    rw [show (2 : ℕ) * m + 1 + 2 * c + 1 = 2 * m + 2 * c + 2 from by ring,
        show (2 : ℕ) * m + 1 + c + 1 = 2 * m + c + 2 from by ring]
    apply stepStar_trans (phase_b_odd m c)
    rcases Nat.even_or_odd c with ⟨j, hj⟩ | ⟨j, hj⟩
    · subst hj
      rw [show j + j + 1 = 2 * j + 1 from by ring,
          show (2 : ℕ) * m + 2 = (2 * m + 1) + 1 from by ring]
      apply stepStar_trans (phase_c_odd j (2 * m + 1) (4 * m + 3 * (j + j) + 4))
      ring_nf; finish
    · subst hj
      rw [show (2 : ℕ) * j + 1 + 1 = 2 * (j + 1) from by ring,
          show (2 : ℕ) * m + 2 = (2 * m + 1) + 1 from by ring]
      apply stepStar_trans (phase_c_even (j + 1) (2 * m + 1)
        (4 * m + 3 * (2 * j + 1) + 4))
      ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 0, p.1 + 2 * p.2 + 1, p.1 + p.2 + 2⟩) ⟨0, 0⟩
  intro ⟨a, c⟩
  refine ⟨⟨a + 1, a + 3 * c + 2⟩, ?_⟩
  show ⟨(0 : ℕ), 0, 0, a + 2 * c + 1, a + c + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, (a + 1) + 2 * (a + 3 * c + 2) + 1, (a + 1) + (a + 3 * c + 2) + 2⟩
  rw [show (a + 1) + 2 * (a + 3 * c + 2) + 1 = 3 * a + 6 * c + 6 from by ring,
      show (a + 1) + (a + 3 * c + 2) + 2 = 2 * a + 3 * c + 5 from by ring]
  exact main_trans a c

end Sz22_2003_unofficial_674
