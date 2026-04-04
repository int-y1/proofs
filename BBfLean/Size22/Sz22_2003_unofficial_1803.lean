import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1803: [9/10, 55/147, 14/3, 7/11, 15/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -2  1
 1 -1  0  1  0
 0  0  0  1 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1803

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+2, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1) (e := e))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a b d e,
    ⟨a + k, b + 1, 0, d + 2 * k, e⟩ [fm]⊢* ⟨a, b + 1 + k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a b d e; exists 0
  · intro a b d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih a (b + 1) d (e + 1))
    ring_nf; finish

theorem opening (n : ℕ) : ⟨n + 2, 0, 0, 3 * n + 3, 0⟩ [fm]⊢* ⟨0, n + 3, 0, n + 3, n⟩ := by
  step fm
  step fm
  show ⟨n, 3, 0, 3 * n + 3, 0⟩ [fm]⊢* _
  rw [show (n : ℕ) = 0 + n from by omega,
      show (3 : ℕ) = 2 + 1 from rfl,
      show 3 * (0 + n) + 3 = (n + 3) + 2 * n from by ring]
  apply stepStar_trans (r2r1_chain n 0 2 (n + 3) 0)
  ring_nf; finish

theorem r2_chain : ∀ k, ∀ b c d e,
    ⟨0, b + k, c, d + 2 * k, e⟩ [fm]⊢* ⟨0, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro b c d e; exists 0
  · intro b c d e
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    ring_nf; finish

theorem d1_fix : ⟨0, b + 1, c + 1, 1, e⟩ [fm]⊢* ⟨0, b + 1, c + 1, 0, e + 1⟩ := by
  step fm; step fm; step fm; finish

theorem c_drain_step : ⟨0, b + 1, c + 2, 0, e⟩ [fm]⊢* ⟨0, b + 2, c + 1, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem c_drain_final : ⟨0, b + 1, 1, 0, e⟩ [fm]⊢* ⟨0, b + 2, 0, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem c_drain : ∀ c, ∀ b e,
    ⟨0, b + 1, c + 1, 0, e⟩ [fm]⊢* ⟨0, b + c + 2, 0, 0, e + c + 1⟩ := by
  intro c; induction' c with c ih
  · intro b e; exact c_drain_final
  · intro b e
    apply stepStar_trans (c_drain_step (b := b) (c := c) (e := e))
    apply stepStar_trans (ih (b + 1) (e + 1))
    ring_nf; finish

theorem rampup_step : ⟨a, b + 3, 0, 0, e⟩ [fm]⊢* ⟨a + 1, b + 2, 0, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem rampup_chain : ∀ k, ∀ a e,
    ⟨a, k + 3, 0, 0, e⟩ [fm]⊢* ⟨a + k, 3, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a e; exists 0
  · intro a e
    rw [show (k + 1) + 3 = (k + 1) + 3 from rfl]
    apply stepStar_trans (rampup_step (a := a) (b := k + 1) (e := e))
    show ⟨a + 1, (k + 1) + 2, 0, 0, e + 1⟩ [fm]⊢* _
    rw [show (k + 1) + 2 = k + 3 from by ring]
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

theorem final_ramp : ⟨a, 3, 0, 0, e⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 2, e + 1⟩ := by
  step fm; step fm; step fm; step fm
  step fm; step fm; finish

theorem main_trans_even (m : ℕ) :
    ⟨2 * m + 2, 0, 0, 6 * m + 3, 0⟩ [fm]⊢⁺ ⟨2 * m + 3, 0, 0, 6 * m + 6, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2 * m + 3, 0, 0, 2, 6 * m + 4⟩)
  · show ⟨2 * m + 2, 0, 0, 6 * m + 3, 0⟩ [fm]⊢* ⟨2 * m + 3, 0, 0, 2, 6 * m + 4⟩
    rw [show 6 * m + 3 = 3 * (2 * m) + 3 from by ring,
        show 2 * m + 2 = (2 * m) + 2 from by ring]
    apply stepStar_trans (opening (2 * m))
    show ⟨0, 2 * m + 3, 0, 2 * m + 3, 2 * m⟩ [fm]⊢* _
    have h1 := r2_chain (m + 1) (m + 2) 0 1 (2 * m)
    rw [show m + 2 + (m + 1) = 2 * m + 3 from by ring,
        show 1 + 2 * (m + 1) = 2 * m + 3 from by ring] at h1
    apply stepStar_trans h1
    show ⟨0, m + 2, 0 + (m + 1), 1, 2 * m + (m + 1)⟩ [fm]⊢* _
    rw [show (0 : ℕ) + (m + 1) = m + 1 from by ring,
        show 2 * m + (m + 1) = 3 * m + 1 from by ring]
    apply stepStar_trans (d1_fix (b := m + 1) (c := m) (e := 3 * m + 1))
    show ⟨0, m + 1 + 1, m + 1, 0, 3 * m + 1 + 1⟩ [fm]⊢* _
    rw [show m + 1 + 1 = m + 2 from by ring,
        show 3 * m + 1 + 1 = 3 * m + 2 from by ring]
    apply stepStar_trans (c_drain m (m + 1) (3 * m + 2))
    show ⟨0, m + 1 + m + 2, 0, 0, 3 * m + 2 + m + 1⟩ [fm]⊢* _
    rw [show m + 1 + m + 2 = 2 * m + 3 from by ring,
        show 3 * m + 2 + m + 1 = 4 * m + 3 from by ring]
    apply stepStar_trans (rampup_chain (2 * m) 0 (4 * m + 3))
    show ⟨0 + 2 * m, 3, 0, 0, 4 * m + 3 + 2 * m⟩ [fm]⊢* _
    rw [show 0 + 2 * m = 2 * m from by ring,
        show 4 * m + 3 + 2 * m = 6 * m + 3 from by ring]
    apply stepStar_trans (stepPlus_stepStar (final_ramp (a := 2 * m) (e := 6 * m + 3)))
    show ⟨2 * m + 3, 0, 0, 2, 6 * m + 3 + 1⟩ [fm]⊢* ⟨2 * m + 3, 0, 0, 2, 6 * m + 4⟩
    ring_nf; finish
  · show ⟨2 * m + 3, 0, 0, 2, 6 * m + 4⟩ [fm]⊢⁺ ⟨2 * m + 3, 0, 0, 6 * m + 6, 0⟩
    rw [show 6 * m + 4 = 0 + (6 * m + 4) from by ring,
        show 6 * m + 6 = 2 + (6 * m + 4) from by ring]
    apply step_stepStar_stepPlus
    · show fm ⟨2 * m + 3, 0, 0, 2, 0 + (6 * m + 4)⟩ = some ⟨2 * m + 3, 0, 0, 3, 6 * m + 3⟩
      simp [fm]
    · show ⟨2 * m + 3, 0, 0, 3, 6 * m + 3⟩ [fm]⊢* ⟨2 * m + 3, 0, 0, 2 + (6 * m + 4), 0⟩
      rw [show (3 : ℕ) = 2 + 1 from by ring,
          show 6 * m + 3 = 0 + (6 * m + 3) from by ring,
          show 2 + (6 * m + 4) = (2 + 1) + (6 * m + 3) from by ring]
      exact r4_chain (6 * m + 3) (a := 2 * m + 3) (d := 2 + 1) (e := 0)

theorem main_trans_odd (m : ℕ) :
    ⟨2 * m + 3, 0, 0, 6 * m + 6, 0⟩ [fm]⊢⁺ ⟨2 * m + 4, 0, 0, 6 * m + 9, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2 * m + 4, 0, 0, 2, 6 * m + 7⟩)
  · show ⟨2 * m + 3, 0, 0, 6 * m + 6, 0⟩ [fm]⊢* ⟨2 * m + 4, 0, 0, 2, 6 * m + 7⟩
    rw [show 6 * m + 6 = 3 * (2 * m + 1) + 3 from by ring,
        show 2 * m + 3 = (2 * m + 1) + 2 from by ring]
    apply stepStar_trans (opening (2 * m + 1))
    show ⟨0, 2 * m + 4, 0, 2 * m + 4, 2 * m + 1⟩ [fm]⊢* _
    have h1 := r2_chain (m + 2) (m + 2) 0 0 (2 * m + 1)
    rw [show m + 2 + (m + 2) = 2 * m + 4 from by ring,
        show 0 + 2 * (m + 2) = 2 * m + 4 from by ring] at h1
    apply stepStar_trans h1
    show ⟨0, m + 2, 0 + (m + 2), 0, 2 * m + 1 + (m + 2)⟩ [fm]⊢* _
    rw [show (0 : ℕ) + (m + 2) = m + 2 from by ring,
        show 2 * m + 1 + (m + 2) = 3 * m + 3 from by ring]
    apply stepStar_trans (c_drain (m + 1) (m + 1) (3 * m + 3))
    show ⟨0, m + 1 + (m + 1) + 2, 0, 0, 3 * m + 3 + (m + 1) + 1⟩ [fm]⊢* _
    rw [show m + 1 + (m + 1) + 2 = 2 * m + 4 from by ring,
        show 3 * m + 3 + (m + 1) + 1 = 4 * m + 5 from by ring]
    apply stepStar_trans (rampup_chain (2 * m + 1) 0 (4 * m + 5))
    show ⟨0 + (2 * m + 1), 3, 0, 0, 4 * m + 5 + (2 * m + 1)⟩ [fm]⊢* _
    rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring,
        show 4 * m + 5 + (2 * m + 1) = 6 * m + 6 from by ring]
    apply stepStar_trans (stepPlus_stepStar (final_ramp (a := 2 * m + 1) (e := 6 * m + 6)))
    show ⟨2 * m + 4, 0, 0, 2, 6 * m + 6 + 1⟩ [fm]⊢* ⟨2 * m + 4, 0, 0, 2, 6 * m + 7⟩
    ring_nf; finish
  · show ⟨2 * m + 4, 0, 0, 2, 6 * m + 7⟩ [fm]⊢⁺ ⟨2 * m + 4, 0, 0, 6 * m + 9, 0⟩
    rw [show 6 * m + 7 = 0 + (6 * m + 7) from by ring,
        show 6 * m + 9 = 2 + (6 * m + 7) from by ring]
    apply step_stepStar_stepPlus
    · show fm ⟨2 * m + 4, 0, 0, 2, 0 + (6 * m + 7)⟩ = some ⟨2 * m + 4, 0, 0, 3, 6 * m + 6⟩
      simp [fm]
    · show ⟨2 * m + 4, 0, 0, 3, 6 * m + 6⟩ [fm]⊢* ⟨2 * m + 4, 0, 0, 2 + (6 * m + 7), 0⟩
      rw [show (3 : ℕ) = 2 + 1 from by ring,
          show 6 * m + 6 = 0 + (6 * m + 6) from by ring,
          show 2 + (6 * m + 7) = (2 + 1) + (6 * m + 6) from by ring]
      exact r4_chain (6 * m + 6) (a := 2 * m + 4) (d := 2 + 1) (e := 0)

theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 3 * n + 3, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 3 * n + 6, 0⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    rw [show 3 * (2 * m) + 3 = 6 * m + 3 from by ring,
        show 3 * (2 * m) + 6 = 6 * m + 6 from by ring]
    exact main_trans_even m
  · subst hm
    rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 3 * (2 * m + 1) + 3 = 6 * m + 6 from by ring,
        show 2 * m + 1 + 3 = 2 * m + 4 from by ring,
        show 3 * (2 * m + 1) + 6 = 6 * m + 9 from by ring]
    exact main_trans_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 3, 0⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 3 * n + 3, 0⟩) 0
  intro n; exists n + 1
  rw [show 3 * (n + 1) + 3 = 3 * n + 6 from by ring]
  exact main_trans n
