import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1838: [9/10, 8/21, 77/2, 5/7, 14/11]

Vector representation:
```
-1  2 -1  0  0
 3 -1  0 -1  0
-1  0  0  1  1
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1838

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem d_to_c : ∀ k, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (d := d + 1) (e := e + 1))
    ring_nf; finish

theorem r3r2_drain : ∀ b, ⟨a + 1, b + 1, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * b + 3, 0, 0, 0, e + b + 1⟩ := by
  intro b; induction' b with b ih generalizing a e
  · step fm; step fm; finish
  · step fm; step fm
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

theorem opening : ⟨0, 0, c + 1, 0, e + 1⟩ [fm]⊢* ⟨3, 1, c, 0, e⟩ := by
  step fm; step fm; step fm; finish

theorem chunk : ∀ k, ⟨3, b, c + 4 * k, 0, e + k⟩ [fm]⊢* ⟨3, b + 7 * k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · exists 0
  · rw [show c + 4 * (k + 1) = (c + 4) + 4 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b := b) (c := c + 4) (e := e + 1))
    rw [show c + 4 = c + 1 + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm; step fm
    ring_nf; finish

theorem r3r2_drain_plus : ∀ b, ⟨a + 1, b + 1, 0, 0, e⟩ [fm]⊢⁺ ⟨a + 2 * b + 3, 0, 0, 0, e + b + 1⟩ := by
  intro b; induction' b with b ih generalizing a e
  · step fm; step fm; finish
  · step fm; step fm
    apply stepStar_trans (r3r2_drain b (a := a + 2) (e := e + 1))
    ring_nf; finish

theorem base0 : ⟨3, b + 1, 0, 0, e⟩ [fm]⊢⁺ ⟨2 * b + 5, 0, 0, 0, e + b + 1⟩ := by
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (r3r2_drain_plus b (a := 2) (e := e))
  ring_nf; finish

theorem base1 : ⟨3, b + 1, 1, 0, e⟩ [fm]⊢⁺ ⟨2 * b + 8, 0, 0, 0, e + b + 3⟩ := by
  step fm
  rw [show b + 1 + 2 = (b + 2) + 1 from by ring]
  apply stepStar_trans (r3r2_drain (b + 2) (a := 1) (e := e))
  ring_nf; finish

theorem base2 : ⟨3, b + 1, 2, 0, e⟩ [fm]⊢⁺ ⟨2 * b + 11, 0, 0, 0, e + b + 5⟩ := by
  step fm; step fm; step fm; step fm
  rw [show b + 4 = (b + 3) + 1 from by ring]
  apply stepStar_trans (r3r2_drain (b + 3) (a := 2) (e := e + 1))
  ring_nf; finish

theorem base3 : ⟨3, b + 1, 3, 0, e + 1⟩ [fm]⊢⁺ ⟨2 * b + 16, 0, 0, 0, e + b + 6⟩ := by
  step fm; step fm; step fm; step fm; step fm
  rw [show b + 6 = (b + 5) + 1 from by ring]
  apply stepStar_trans (r3r2_drain (b + 5) (a := 3) (e := e))
  ring_nf; finish

theorem spiral : ∀ c, ∀ b e, e ≥ c →
    ∃ A E, ⟨3, b + 1, c, 0, e⟩ [fm]⊢⁺ ⟨A + 1, 0, 0, 0, E⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih
  intro b e he
  rcases c with _ | _ | _ | _ | c
  · exact ⟨2 * b + 4, e + b + 1, base0⟩
  · exact ⟨2 * b + 7, e + b + 3, base1⟩
  · exact ⟨2 * b + 10, e + b + 5, base2⟩
  · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    exact ⟨2 * b + 15, e' + b + 6, base3⟩
  · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have ⟨A, E, h⟩ := ih c (by omega) (b + 7) e' (by omega)
    refine ⟨A, E, ?_⟩
    rw [show c + 4 = c + 4 * 1 from by ring,
        show e' + 1 = e' + 1 from rfl]
    apply stepStar_stepPlus_stepPlus
    · apply stepStar_trans (chunk 1 (b := b + 1) (c := c) (e := e'))
      rw [show b + 1 + 7 * 1 = (b + 7) + 1 from by ring]
      finish
    · exact h

theorem main_trans (a e : ℕ) :
    ∃ a' e', ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a' + 1, 0, 0, 0, e'⟩ := by
  have hr3 : ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, a + 1, e + a + 1⟩ := by
    rw [show a + 1 = 0 + (a + 1) from by ring]
    apply stepStar_trans (r3_chain (a + 1) (a := 0) (d := 0) (e := e))
    ring_nf; finish
  have hd2c : ⟨0, 0, 0, a + 1, e + a + 1⟩ [fm]⊢* ⟨0, 0, a + 1, 0, e + a + 1⟩ := by
    rw [show a + 1 = 0 + (a + 1) from by ring]
    apply stepStar_trans (d_to_c (a + 1) (c := 0) (d := 0) (e := e + a + 1))
    ring_nf; finish
  have hopening : ⟨0, 0, a + 1, 0, e + a + 1⟩ [fm]⊢* ⟨3, 1, a, 0, e + a⟩ := by
    rw [show e + a + 1 = (e + a) + 1 from by ring]
    exact opening
  have hspiral := spiral a 0 (e + a) (Nat.le_add_left a e)
  obtain ⟨A, E, hsp⟩ := hspiral
  refine ⟨A, E, ?_⟩
  apply stepStar_stepPlus_stepPlus
  · apply stepStar_trans hr3
    apply stepStar_trans hd2c
    exact hopening
  · exact hsp

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e⟩)
  · intro q ⟨a, e, hq⟩
    subst hq
    obtain ⟨a', e', h⟩ := main_trans a e
    exact ⟨⟨a' + 1, 0, 0, 0, e'⟩, ⟨a', e', rfl⟩, h⟩
  · exact ⟨0, 0, rfl⟩
