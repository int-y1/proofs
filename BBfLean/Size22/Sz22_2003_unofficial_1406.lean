import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1406: [7/15, 1089/14, 4/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  2
 2 -1  0  0  0
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1406

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem e_to_c : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (c := c + 1)); ring_nf; finish

theorem b_to_a : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a := a + 2)); ring_nf; finish

theorem round_chain : ∀ k A C D E,
    ⟨A + k, 2, C + 2 * k, D, E⟩ [fm]⊢* ⟨A, 2, C, D + k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih A C (D + 1) (E + 2)); ring_nf; finish

theorem r2_drain : ∀ k, ⟨a + k, B, 0, d + k, E⟩ [fm]⊢* ⟨a, B + 2 * k, 0, d, E + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a B d E
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (B := B + 2) (E := E + 2)); ring_nf; finish

theorem interleave_even (m : ℕ) : ⟨2 * m, 2, 2 * m, 0, 3⟩ [fm]⊢*
    ⟨0, 2 * m + 2, 0, 0, 4 * m + 3⟩ := by
  have h1 := round_chain m m 0 0 3
  have h2 := r2_drain m (a := 0) (B := 2) (d := 0) (E := 3 + 2 * m)
  rw [show (2 * m, 2, 2 * m, 0, 3) = (m + m, 2, 0 + 2 * m, 0, (3 : ℕ))
    from by simp [Prod.mk.injEq]; ring_nf; try simp]
  apply stepStar_trans h1
  rw [show (m, 2, 0, 0 + m, 3 + 2 * m) = (0 + m, 2, 0, 0 + m, 3 + 2 * m)
    from by simp]
  apply stepStar_trans h2
  rw [show (0, 2 + 2 * m, 0, 0, 3 + 2 * m + 2 * m) = (0, 2 * m + 2, 0, 0, 4 * m + 3)
    from by simp [Prod.mk.injEq]; ring_nf; try simp]; finish

theorem interleave_odd (m : ℕ) : ⟨2 * m + 1, 2, 2 * m + 1, 0, 3⟩ [fm]⊢*
    ⟨0, 2 * m + 3, 0, 0, 4 * m + 5⟩ := by
  have h1 := round_chain m (m + 1) 1 0 3
  rw [show (2 * m + 1, 2, 2 * m + 1, 0, 3) = (m + 1 + m, 2, 1 + 2 * m, 0, (3 : ℕ))
    from by simp [Prod.mk.injEq]; ring_nf; try simp]
  apply stepStar_trans h1
  rw [show (m + 1, 2, 1, 0 + m, 3 + 2 * m) = (m + 1, 2, 1, m, 2 * m + 3)
    from by simp [Prod.mk.injEq]; ring_nf; try simp]
  step fm; step fm
  have h2 := r2_drain m (a := 0) (B := 3) (d := 0) (E := 2 * m + 5)
  rw [show (m, 3, 0, m, 2 * m + 5) = (0 + m, 3, 0, 0 + m, 2 * m + 5)
    from by simp]
  apply stepStar_trans h2
  rw [show (0, 3 + 2 * m, 0, 0, 2 * m + 5 + 2 * m) = (0, 2 * m + 3, 0, 0, 4 * m + 5)
    from by simp [Prod.mk.injEq]; ring_nf; try simp]; finish

theorem middle_phase (c : ℕ) : ⟨c + 1, 0, c, 0, 0⟩ [fm]⊢* ⟨0, c + 1, 0, 0, 2 * c + 1⟩ := by
  rcases c with _ | c
  · step fm; finish
  · rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
    step fm; step fm; step fm
    rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      apply stepStar_trans (interleave_even m); ring_nf; finish
    · subst hm
      apply stepStar_trans (interleave_odd m); ring_nf; finish

theorem main_trans (e : ℕ) : ⟨e + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨2 * e + 2, 0, 0, 0, 2 * e + 1⟩ := by
  have h_etc := e_to_c e (a := e + 1) (c := 0) (e := 0)
  rw [show (e + 1, 0, 0, 0, e) = (e + 1, 0, 0, 0, 0 + e) from by simp]
  apply stepStar_stepPlus_stepPlus h_etc
  rw [show (e + 1, 0, 0 + e, 0, 0) = (e + 1, 0, e, 0, 0) from by simp]
  apply step_stepStar_stepPlus
  · show fm ⟨e + 1, 0, e, 0, 0⟩ = some ⟨e, 1, e, 0, 1⟩; simp [fm]
  rcases e with _ | e
  · step fm; finish
  · step fm; step fm
    rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      apply stepStar_trans (interleave_even m)
      rw [show (0, 2 * m + 2, 0, 0, 4 * m + 3) = (0, 0 + (2 * m + 2), 0, 0, 4 * m + 3)
        from by simp]
      apply stepStar_trans (b_to_a (2 * m + 2) (a := 0) (b := 0) (e := 4 * m + 3))
      rw [show (0 + 2 * (2 * m + 2), 0, 0, 0, 4 * m + 3) =
          (2 * (2 * m + 1) + 2, 0, 0, 0, 2 * (2 * m + 1) + 1) from by simp [Prod.mk.injEq]; ring_nf; try simp]
      finish
    · subst hm
      apply stepStar_trans (interleave_odd m)
      rw [show (0, 2 * m + 3, 0, 0, 4 * m + 5) = (0, 0 + (2 * m + 3), 0, 0, 4 * m + 5)
        from by simp]
      apply stepStar_trans (b_to_a (2 * m + 3) (a := 0) (b := 0) (e := 4 * m + 5))
      rw [show (0 + 2 * (2 * m + 3), 0, 0, 0, 4 * m + 5) =
          (2 * (2 * m + 1 + 1) + 2, 0, 0, 0, 2 * (2 * m + 1 + 1) + 1)
        from by simp [Prod.mk.injEq]; ring_nf; try simp]
      finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨e + 1, 0, 0, 0, e⟩) 1
  intro e; exists 2 * e + 1
  exact main_trans e
