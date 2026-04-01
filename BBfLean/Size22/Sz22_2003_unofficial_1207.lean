import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1207: [5/6, 539/2, 4/35, 3/7, 245/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  0
 0  1  0 -1  0
 0  0  1  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1207

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+2, e⟩
  | _ => none

theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [Nat.add_succ d k]
    step fm
    apply stepStar_trans (ih (b := b + 1) (d := d))
    ring_nf; finish

theorem middle_round : ⟨0, b + 4, c, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 3, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem middle_loop : ∀ k, ⟨0, b + 4 * k, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · exists 0
  · rw [show b + 4 * (k + 1) = (b + 4) + 4 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b := b + 4) (e := e + 1))
    apply stepStar_trans middle_round
    rw [show c + 3 * k + 3 = c + 3 * (k + 1) from by ring]
    finish

theorem exit_b1 : ⟨0, 1, c, 0, e + 1⟩ [fm]⊢* ⟨0, 0, c + 1, 3, e + 1⟩ := by
  step fm; step fm; step fm; step fm
  ring_nf; finish

theorem exit_b2 : ⟨0, 2, c, 0, e + 1⟩ [fm]⊢* ⟨0, 0, c + 1, 4, e + 2⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem exit_b3 : ⟨0, 3, c, 0, e + 1⟩ [fm]⊢* ⟨0, 0, c + 2, 2, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem drain : ∀ C, ⟨0, 0, C + 1, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * (C + 1) + 1, e + 2 * (C + 1)⟩ := by
  intro C; induction' C with C ih generalizing d e
  · step fm; step fm; step fm; ring_nf; finish
  · step fm; step fm; step fm
    rw [show d + 3 + 1 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 3) (e := e + 2))
    ring_nf; finish

-- Phase 1 + 2 + 3 for D = 4k+2
theorem full_r0 : ⟨0, 0, 0, 4 * k + 2, e + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 9 * k + 7, e + 6 * k + 4⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 0, 4 * k + 1, e + k + 1⟩)
  · rw [show 4 * k + 2 = (4 * k + 1) + 1 from by omega]; simp [fm]
  apply stepStar_trans
  · show ⟨0, 1, 0, 4 * k + 1, e + k + 1⟩ [fm]⊢* ⟨0, 4 * k + 2, 0, 0, e + k + 1⟩
    rw [show 4 * k + 1 = 0 + (4 * k + 1) from by ring]
    apply stepStar_trans (d_to_b (4 * k + 1) (b := 1) (d := 0) (e := e + k + 1))
    rw [show 1 + (4 * k + 1) = 4 * k + 2 from by ring]; finish
  show ⟨0, 4 * k + 2, 0, 0, e + k + 1⟩ [fm]⊢* ⟨0, 0, 0, 9 * k + 7, e + 6 * k + 4⟩
  rw [show 4 * k + 2 = 2 + 4 * k from by ring,
      show e + k + 1 = (e + 1) + k from by ring]
  apply stepStar_trans (middle_loop k (b := 2) (c := 0) (e := e + 1))
  show ⟨0, 2, 0 + 3 * k, 0, e + 1⟩ [fm]⊢* ⟨0, 0, 0, 9 * k + 7, e + 6 * k + 4⟩
  rw [show 0 + 3 * k = 3 * k from by ring]
  apply stepStar_trans (exit_b2 (c := 3 * k) (e := e))
  show ⟨0, 0, 3 * k + 1, 4, e + 2⟩ [fm]⊢* ⟨0, 0, 0, 9 * k + 7, e + 6 * k + 4⟩
  rw [show 3 * k + 1 = (3 * k) + 1 from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (drain (3 * k) (d := 3) (e := e + 2))
  ring_nf; finish

-- Phase 1 + 2 + 3 for D = 4k+3
theorem full_r1 : ⟨0, 0, 0, 4 * k + 3, e + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 9 * k + 8, e + 6 * k + 5⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 0, 4 * k + 2, e + k + 1⟩)
  · rw [show 4 * k + 3 = (4 * k + 2) + 1 from by omega]; simp [fm]
  apply stepStar_trans
  · show ⟨0, 1, 0, 4 * k + 2, e + k + 1⟩ [fm]⊢* ⟨0, 4 * k + 3, 0, 0, e + k + 1⟩
    rw [show 4 * k + 2 = 0 + (4 * k + 2) from by ring]
    apply stepStar_trans (d_to_b (4 * k + 2) (b := 1) (d := 0) (e := e + k + 1))
    rw [show 1 + (4 * k + 2) = 4 * k + 3 from by ring]; finish
  show ⟨0, 4 * k + 3, 0, 0, e + k + 1⟩ [fm]⊢* ⟨0, 0, 0, 9 * k + 8, e + 6 * k + 5⟩
  rw [show 4 * k + 3 = 3 + 4 * k from by ring,
      show e + k + 1 = (e + 1) + k from by ring]
  apply stepStar_trans (middle_loop k (b := 3) (c := 0) (e := e + 1))
  show ⟨0, 3, 0 + 3 * k, 0, e + 1⟩ [fm]⊢* ⟨0, 0, 0, 9 * k + 8, e + 6 * k + 5⟩
  rw [show 0 + 3 * k = 3 * k from by ring]
  apply stepStar_trans (exit_b3 (c := 3 * k) (e := e))
  show ⟨0, 0, 3 * k + 2, 2, e + 1⟩ [fm]⊢* ⟨0, 0, 0, 9 * k + 8, e + 6 * k + 5⟩
  rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain (3 * k + 1) (d := 1) (e := e + 1))
  ring_nf; finish

-- Phase 1 + 2 + 3 for D = 4(k+1) = 4k+4
theorem full_r2 : ⟨0, 0, 0, 4 * k + 4, e + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 9 * k + 14, e + 6 * k + 8⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 0, 4 * k + 3, e + k + 2⟩)
  · rw [show 4 * k + 4 = (4 * k + 3) + 1 from by omega]; simp [fm]
  apply stepStar_trans
  · show ⟨0, 1, 0, 4 * k + 3, e + k + 2⟩ [fm]⊢* ⟨0, 4 * k + 4, 0, 0, e + k + 2⟩
    rw [show 4 * k + 3 = 0 + (4 * k + 3) from by ring]
    apply stepStar_trans (d_to_b (4 * k + 3) (b := 1) (d := 0) (e := e + k + 2))
    rw [show 1 + (4 * k + 3) = 4 * k + 4 from by ring]; finish
  show ⟨0, 4 * k + 4, 0, 0, e + k + 2⟩ [fm]⊢* ⟨0, 0, 0, 9 * k + 14, e + 6 * k + 8⟩
  rw [show 4 * k + 4 = 0 + 4 * (k + 1) from by ring,
      show e + k + 2 = (e + 1) + (k + 1) from by ring]
  apply stepStar_trans (middle_loop (k + 1) (b := 0) (c := 0) (e := e + 1))
  show ⟨0, 0, 0 + 3 * (k + 1), 0, e + 1⟩ [fm]⊢* ⟨0, 0, 0, 9 * k + 14, e + 6 * k + 8⟩
  rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring]
  -- exit_b0: R5 then drain
  step fm
  show ⟨0, 0, 3 * k + 3 + 1, 2, e⟩ [fm]⊢* ⟨0, 0, 0, 9 * k + 14, e + 6 * k + 8⟩
  rw [show 3 * k + 3 + 1 = (3 * k + 3) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain (3 * k + 3) (d := 1) (e := e))
  ring_nf; finish

-- Phase 1 + 2 + 3 for D = 4k+1
theorem full_r3 : ⟨0, 0, 0, 4 * k + 1, e + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 9 * k + 6, e + 6 * k + 3⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 0, 4 * k, e + k + 1⟩)
  · rw [show 4 * k + 1 = (4 * k) + 1 from by omega]; simp [fm]
  apply stepStar_trans
  · show ⟨0, 1, 0, 4 * k, e + k + 1⟩ [fm]⊢* ⟨0, 4 * k + 1, 0, 0, e + k + 1⟩
    rw [show 4 * k = 0 + 4 * k from by ring]
    apply stepStar_trans (d_to_b (4 * k) (b := 1) (d := 0) (e := e + k + 1))
    ring_nf; finish
  show ⟨0, 4 * k + 1, 0, 0, e + k + 1⟩ [fm]⊢* ⟨0, 0, 0, 9 * k + 6, e + 6 * k + 3⟩
  rw [show 4 * k + 1 = 1 + 4 * k from by ring,
      show e + k + 1 = (e + 1) + k from by ring]
  apply stepStar_trans (middle_loop k (b := 1) (c := 0) (e := e + 1))
  show ⟨0, 1, 0 + 3 * k, 0, e + 1⟩ [fm]⊢* ⟨0, 0, 0, 9 * k + 6, e + 6 * k + 3⟩
  rw [show 0 + 3 * k = 3 * k from by ring]
  apply stepStar_trans (exit_b1 (c := 3 * k) (e := e))
  show ⟨0, 0, 3 * k + 1, 3, e + 1⟩ [fm]⊢* ⟨0, 0, 0, 9 * k + 6, e + 6 * k + 3⟩
  rw [show 3 * k + 1 = (3 * k) + 1 from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (drain (3 * k) (d := 2) (e := e + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ D ≥ 2 ∧ 4 * E ≥ D + 2)
  · intro c ⟨D, E, hq, hD, hE⟩; subst hq
    obtain ⟨k, rfl | rfl | rfl | rfl⟩ : ∃ k, D = 4 * k ∨ D = 4 * k + 1 ∨ D = 4 * k + 2 ∨ D = 4 * k + 3 :=
      ⟨D / 4, by omega⟩
    · -- D = 4k, k >= 1
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨e, rfl⟩ : ∃ e, E = e + (k + 2) := ⟨E - (k + 2), by omega⟩
      exact ⟨⟨0, 0, 0, 9 * k + 14, e + 6 * k + 8⟩,
        ⟨9 * k + 14, e + 6 * k + 8, rfl, by omega, by omega⟩,
        full_r2⟩
    · -- D = 4k+1
      obtain ⟨e, rfl⟩ : ∃ e, E = e + (k + 1) := ⟨E - (k + 1), by omega⟩
      exact ⟨⟨0, 0, 0, 9 * k + 6, e + 6 * k + 3⟩,
        ⟨9 * k + 6, e + 6 * k + 3, rfl, by omega, by omega⟩,
        full_r3⟩
    · -- D = 4k+2
      obtain ⟨e, rfl⟩ : ∃ e, E = e + (k + 1) := ⟨E - (k + 1), by omega⟩
      exact ⟨⟨0, 0, 0, 9 * k + 7, e + 6 * k + 4⟩,
        ⟨9 * k + 7, e + 6 * k + 4, rfl, by omega, by omega⟩,
        full_r0⟩
    · -- D = 4k+3
      obtain ⟨e, rfl⟩ : ∃ e, E = e + (k + 1) := ⟨E - (k + 1), by omega⟩
      exact ⟨⟨0, 0, 0, 9 * k + 8, e + 6 * k + 5⟩,
        ⟨9 * k + 8, e + 6 * k + 5, rfl, by omega, by omega⟩,
        full_r1⟩
  · exact ⟨2, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1207
