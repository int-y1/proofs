import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1146: [5/6, 44/35, 539/2, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  1
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1146

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem e_to_b : ∀ k, ⟨0, b, 0, d, 0 + k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih generalizing b
  · simp; exists 0
  · rw [show 0 + (k + 1) = (0 + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 2) (e := e + 1))
    ring_nf; finish

theorem r2_chain : ∀ k, ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

theorem interleave_step : ⟨0, b + 2, c + 1, d + 1, j⟩ [fm]⊢* ⟨0, b, c + 2, d, j + 1⟩ := by
  step fm; step fm; step fm; finish

theorem interleave : ∀ k, ⟨0, 2 * k + b, c + 1, d + k, j⟩ [fm]⊢* ⟨0, b, c + k + 1, d, j + k⟩ := by
  intro k; induction' k with k ih generalizing b c d j
  · simp; exists 0
  · rw [show 2 * (k + 1) + b = (2 * k + b) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans interleave_step
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c := c + 1) (j := j + 1))
    ring_nf; finish

theorem r3r2_alt : ∀ c, ⟨a + 1, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 3 * c + 2 * a + 2, e + 3 * c + a + 1⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih generalizing a e
  rcases c with _ | _ | c
  · apply stepStar_trans (r3_chain (a + 1))
    ring_nf; finish
  · step fm; step fm
    show ⟨a + 2, 0, 0, 0 + 1, e + 2⟩ [fm]⊢* _
    step fm
    apply stepStar_trans (r3_chain (a + 1))
    ring_nf; finish
  · step fm; step fm; step fm
    show ⟨(a + 3) + 1, 0, c, 0, e + 3⟩ [fm]⊢* _
    apply stepStar_trans (ih c (by omega) (a := a + 3) (e := e + 3))
    ring_nf; finish

theorem r2r3_drain : ∀ c, a + d ≥ 1 → ⟨a, 0, c, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * c + 2 * a, e + 3 * c + a⟩ := by
  intro c; induction' c with c ih generalizing a d e
  · intro _
    apply stepStar_trans (r3_chain a)
    ring_nf; finish
  · intro had
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      apply stepStar_trans (r3r2_alt (c + 1) (a := a') (e := e))
      ring_nf; finish
    · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      step fm
      apply stepStar_trans (ih (a := a + 2) (d := d') (e := e + 1) (by omega))
      ring_nf; finish

theorem trans_even : ⟨0, 0, 0, d + (m + 2), 2 * m⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 3 * m + 4, 4 * m + 3⟩ := by
  -- Phase 1: R4 drain
  rw [show (2 * m : ℕ) = 0 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m) (b := 0) (d := d + (m + 2)))
  -- Now at (0, 2*m, 0, d+(m+2), 0). Need R5 step.
  rw [show 0 + 2 * m = 2 * m from by ring]
  -- R5: (0, 2m, 0, d+(m+2), 0) → (0, 2m, 1, d+(m+1), 0)
  rw [show d + (m + 2) = (d + (m + 1)) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show ⟨0, 2 * m, 0, (d + (m + 1)) + 1, 0⟩ [fm]⊢ ⟨0, 2 * m, 1, d + (m + 1), 0⟩
    simp [fm]
  -- Now at (0, 2m, 1, d+(m+1), 0). Interleave m rounds.
  rw [show d + (m + 1) = (d + 1) + m from by ring,
      show (2 * m : ℕ) = 2 * m + 0 from by ring]
  apply stepStar_trans (interleave m (b := 0) (c := 0) (d := d + 1) (j := 0))
  -- Now at (0, 0, m+1, d+1, m)
  rw [show 0 + m + 1 = m + 1 from by ring, show 0 + m = m from by ring]
  apply stepStar_trans (r2r3_drain (m + 1) (a := 0) (d := d + 1) (e := m) (by omega))
  ring_nf; finish

theorem trans_odd : ⟨0, 0, 0, d + (m + 2), 2 * m + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 3 * m + 5, 4 * m + 5⟩ := by
  -- Phase 1: R4 drain
  rw [show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m + 1) (b := 0) (d := d + (m + 2)))
  -- R5 step
  rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring,
      show d + (m + 2) = (d + (m + 1)) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show ⟨0, 2 * m + 1, 0, (d + (m + 1)) + 1, 0⟩ [fm]⊢ ⟨0, 2 * m + 1, 1, d + (m + 1), 0⟩
    simp [fm]
  -- Interleave m rounds
  rw [show d + (m + 1) = (d + 1) + m from by ring,
      show (2 * m + 1 : ℕ) = 2 * m + 1 from by ring]
  apply stepStar_trans (interleave m (b := 1) (c := 0) (d := d + 1) (j := 0))
  -- Now at (0, 1, m+1, d+1, m). R2 then R1 (2 steps).
  rw [show 0 + m + 1 = m + 1 from by ring, show 0 + m = m from by ring]
  step fm; step fm
  -- Now at (1, 0, m+1, d, m+1)
  apply stepStar_trans (r2r3_drain (m + 1) (a := 1) (d := d) (e := m + 1) (by omega))
  ring_nf; finish

theorem main_trans (hd : 2 * D ≥ E + 3) :
    ⟨0, 0, 0, D, E⟩ [fm]⊢⁺ ⟨0, 0, 0, D + E + 2, 2 * E + 3⟩ := by
  rcases Nat.even_or_odd E with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    obtain ⟨d, rfl⟩ : ∃ d, D = d + (m + 2) := ⟨D - (m + 2), by omega⟩
    have h := trans_even (d := d) (m := m)
    convert h using 2
    all_goals ring_nf
  · subst hm
    obtain ⟨d, rfl⟩ : ∃ d, D = d + (m + 2) := ⟨D - (m + 2), by omega⟩
    have h := trans_odd (d := d) (m := m)
    convert h using 2
    all_goals ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ 2 * D ≥ E + 3)
  · intro q ⟨D, E, hq, hd⟩; subst hq
    refine ⟨⟨0, 0, 0, D + E + 2, 2 * E + 3⟩, ⟨D + E + 2, 2 * E + 3, rfl, ?_⟩, main_trans hd⟩
    omega
  · exact ⟨2, 1, rfl, by omega⟩

end Sz22_2003_unofficial_1146
