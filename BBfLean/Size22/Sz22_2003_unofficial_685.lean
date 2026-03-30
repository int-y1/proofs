import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #685: [35/6, 4/55, 11/2, 3/7, 140/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 2  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_685

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c+1, d+1, e⟩
  | _ => none

theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (b := b + 1)); ring_nf; finish

theorem a_drain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (e := e + 1)); ring_nf; finish

theorem r2_drain : ∀ k, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih generalizing a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a := a + 2)); ring_nf; finish

theorem r2r1r1_even : ∀ n, ∀ c d e,
    ⟨0, 2 * (n + 1), c + 1, d, e + n + 1⟩ [fm]⊢* ⟨0, 0, c + n + 2, d + 2 * (n + 1), e⟩ := by
  intro n; induction' n with n ih <;> intro c d e
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show 2 * (n + 1 + 1) = 2 * (n + 1) + 2 from by ring,
        show e + (n + 1) + 1 = (e + 1) + n + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + (n + 1) + 2 = (c + 1) + n + 2 from by ring,
        show d + (2 * (n + 1) + 2) = (d + 2) + 2 * (n + 1) from by ring]
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring,
        show d + 1 + 1 = d + 2 from by ring,
        show e + 1 + n = e + n + 1 from by ring]
    exact ih (c + 1) (d + 2) e

theorem r2r1r1_odd : ∀ n, ∀ c d e,
    ⟨0, 2 * n + 1, c + 1, d, e + n + 1⟩ [fm]⊢* ⟨1, 0, c + n + 1, d + 2 * n + 1, e⟩ := by
  intro n; induction' n with n ih <;> intro c d e
  · step fm; step fm; finish
  · rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by ring,
        show e + (n + 1) + 1 = (e + 1) + n + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring,
        show d + 1 + 1 = d + 2 from by ring,
        show e + 1 + n = e + n + 1 from by ring,
        show c + (n + 1) + 1 = (c + 1) + n + 1 from by ring,
        show d + 2 * (n + 1) + 1 = (d + 2) + 2 * n + 1 from by ring]
    exact ih (c + 1) (d + 2) e

theorem middle_even (m : ℕ) :
    ⟨0, 2 * m, 3, 3, 4 * m + 4⟩ [fm]⊢* ⟨0, 0, 0, 2 * m + 3, 4 * m + 7⟩ := by
  rcases m with _ | m
  · rw [show (3 : ℕ) = 0 + 3 from by ring,
        show (4 : ℕ) = 1 + 3 from by ring]
    apply stepStar_trans (r2_drain 3 (a := 0) (c := 0) (d := 3) (e := 1))
    rw [show 0 + 2 * 3 = 0 + 6 from by ring]
    apply stepStar_trans (a_drain 6 (a := 0) (d := 3) (e := 1))
    ring_nf; finish
  · rw [show 2 * (m + 1) = 2 * (m + 1) from rfl,
        show (3 : ℕ) = 2 + 1 from by ring,
        show 4 * (m + 1) + 4 = (3 * m + 7) + m + 1 from by ring]
    apply stepStar_trans (r2r1r1_even m (c := 2) (d := 3) (e := 3 * m + 7))
    rw [show 2 + m + 2 = 0 + (m + 4) from by ring,
        show 3 * m + 7 = (2 * m + 3) + (m + 4) from by ring]
    apply stepStar_trans (r2_drain (m + 4) (a := 0) (c := 0) (d := 3 + 2 * (m + 1)) (e := 2 * m + 3))
    rw [show 3 + 2 * (m + 1) = 2 * m + 5 from by ring,
        show 0 + 2 * (m + 4) = 0 + (2 * m + 8) from by ring]
    apply stepStar_trans (a_drain (2 * m + 8) (a := 0) (d := 2 * m + 5) (e := 2 * m + 3))
    ring_nf; finish

theorem middle_odd (m : ℕ) :
    ⟨0, 2 * m + 1, 3, 3, 4 * m + 6⟩ [fm]⊢* ⟨0, 0, 0, 2 * m + 4, 4 * m + 9⟩ := by
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 4 * m + 6 = (3 * m + 5) + m + 1 from by ring]
  apply stepStar_trans (r2r1r1_odd m (c := 2) (d := 3) (e := 3 * m + 5))
  rw [show 2 + m + 1 = 0 + (m + 3) from by ring,
      show 3 * m + 5 = (2 * m + 2) + (m + 3) from by ring]
  apply stepStar_trans (r2_drain (m + 3) (a := 1) (c := 0) (d := 3 + (2 * m + 1)) (e := 2 * m + 2))
  rw [show 3 + (2 * m + 1) = 2 * m + 4 from by ring,
      show 1 + 2 * (m + 3) = 0 + (2 * m + 7) from by ring]
  apply stepStar_trans (a_drain (2 * m + 7) (a := 0) (d := 2 * m + 4) (e := 2 * m + 2))
  ring_nf; finish

theorem main_trans (d : ℕ) :
    ⟨0, 0, 0, d, 2 * d + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 1, 2 * d + 3⟩ := by
  rcases d with _ | _ | d
  · execute fm 6
  · execute fm 10
  · -- d+2
    rw [show 2 * (d + 2) + 1 = 2 * d + 5 from by ring,
        show d + 2 + 1 = d + 3 from by ring,
        show 2 * (d + 2) + 3 = 2 * d + 7 from by ring]
    -- R4 chain + R5 gives the first step for ⊢⁺
    apply stepStar_stepPlus_stepPlus
    · -- ⊢*: R4 chain
      rw [show (d + 2 : ℕ) = 0 + (d + 2) from by ring]
      exact d_to_b (d + 2) (b := 0) (d := 0) (e := 2 * d + 5)
    -- ⊢⁺: (0, 0+(d+2), 0, 0, 2d+5) -> ...
    -- R5 is the first explicit step
    rw [show 2 * d + 5 = (2 * d + 4) + 1 from by ring]
    simp only [Nat.zero_add]
    -- R5: e+1 pattern fires
    apply step_stepStar_stepPlus (show (0, d + 2, 0, 0, (2 * d + 4) + 1) [fm]⊢ (2, d + 2, 1, 1, 2 * d + 4) from rfl)
    -- R1: a+1, b+1 pattern
    rw [show (2 : ℕ) = 1 + 1 from by ring, show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (step_stepStar (show (1 + 1, (d + 1) + 1, 1, 1, 2 * d + 4) [fm]⊢ (1, d + 1, 2, 2, 2 * d + 4) from rfl))
    -- R1 again
    rw [show (1 : ℕ) = 0 + 1 from by ring, show d + 1 = d + 1 from rfl]
    apply stepStar_trans (step_stepStar (show (0 + 1, d + 1, 2, 2, 2 * d + 4) [fm]⊢ (0, d, 3, 3, 2 * d + 4) from rfl))
    -- (0, d, 3, 3, 2d+4)
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      rw [show 2 * (k + k) + 4 = 4 * k + 4 from by ring,
          show k + k + 3 = 2 * k + 3 from by ring,
          show 2 * (k + k) + 7 = 4 * k + 7 from by ring,
          show k + k = 2 * k from by ring]
      exact middle_even k
    · subst hk
      rw [show 2 * (2 * k + 1) + 4 = 4 * k + 6 from by ring,
          show 2 * k + 1 + 3 = 2 * k + 4 from by ring,
          show 2 * (2 * k + 1) + 7 = 4 * k + 9 from by ring]
      exact middle_odd k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d, 2 * d + 1⟩) 0
  intro d; exists d + 1; exact main_trans d

end Sz22_2003_unofficial_685
