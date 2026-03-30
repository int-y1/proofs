import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #653: [35/6, 143/2, 8/55, 3/7, 6/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 3  0 -1  0 -1  0
 0  1  0 -1  0  0
 1  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_653

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d, e, f⟩
  | _ => none

-- R4 repeated: move d to b.
theorem r4_drain : ∀ k, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- Tail phase: R2x3 then R3, repeated k times.
theorem tail_phase : ∀ k c d e f, ⟨3, 0, c + k, d, e, f⟩ [fm]⊢* ⟨(3 : ℕ), 0, c, d, e + 2 * k, f + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih c d (e + 2) (f + 3))
    ring_nf; finish

-- R1x3 + R3 chain: each round drains b by 3 and e by 1.
theorem r1r3_chain : ∀ k b c d e f,
    ⟨3, b + 3 * k, c, d, e + k, f⟩ [fm]⊢* ⟨(3 : ℕ), b, c + 2 * k, d + 3 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 2) (d + 3) e f)
    ring_nf; finish

-- Remainder b=1: 4 steps via R1, R2, R2, R3.
theorem rem_b1 : ⟨3, 1, c, d, e, f⟩ [fm]⊢* ⟨3, 0, c, d + 1, e + 1, f + 2⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

-- Remainder b=2: 4 steps via R1, R1, R2, R3.
theorem rem_b2 : ⟨3, 2, c, d, e, f⟩ [fm]⊢* ⟨3, 0, c + 1, d + 2, e, f + 1⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

-- Middle phase: (3, D, 0, 1, E, F) →* (3, 0, 0, D+1, E+D, F+2*D)
-- Proven by decomposing D mod 3.
theorem middle (D E F : ℕ) (hD : D ≤ 3 * E) :
    ⟨3, D, 0, 1, E, F⟩ [fm]⊢* ⟨3, 0, 0, D + 1, E + D, F + 2 * D⟩ := by
  obtain ⟨q, rfl | rfl | rfl⟩ : ∃ q, D = 3 * q ∨ D = 3 * q + 1 ∨ D = 3 * q + 2 :=
    ⟨D / 3, by omega⟩
  · -- D = 3*q
    obtain ⟨e, rfl⟩ : ∃ e, E = e + q := ⟨E - q, by omega⟩
    rw [show 3 * q = 0 + 3 * q from by ring]
    apply stepStar_trans (r1r3_chain q 0 0 1 e F)
    rw [show 0 + 2 * q = 0 + (2 * q) from by ring]
    apply stepStar_trans (tail_phase (2 * q) 0 (1 + 3 * q) e F)
    ring_nf; finish
  · -- D = 3*q+1
    obtain ⟨e, rfl⟩ : ∃ e, E = e + q := ⟨E - q, by omega⟩
    rw [show 3 * q + 1 = 1 + 3 * q from by ring]
    apply stepStar_trans (r1r3_chain q 1 0 1 e F)
    rw [show 0 + 2 * q = 2 * q from by ring]
    apply stepStar_trans (rem_b1 (c := 2 * q) (d := 1 + 3 * q) (e := e) (f := F))
    rw [show 2 * q = 0 + (2 * q) from by ring]
    apply stepStar_trans (tail_phase (2 * q) 0 (1 + 3 * q + 1) (e + 1) (F + 2))
    ring_nf; finish
  · -- D = 3*q+2
    obtain ⟨e, rfl⟩ : ∃ e, E = e + q := ⟨E - q, by omega⟩
    rw [show 3 * q + 2 = 2 + 3 * q from by ring]
    apply stepStar_trans (r1r3_chain q 2 0 1 e F)
    rw [show 0 + 2 * q = 2 * q from by ring]
    apply stepStar_trans (rem_b2 (c := 2 * q) (d := 1 + 3 * q) (e := e) (f := F))
    rw [show 2 * q + 1 + 0 = 0 + (2 * q + 1) from by ring]
    apply stepStar_trans (tail_phase (2 * q + 1) 0 (1 + 3 * q + 2) e (F + 1))
    ring_nf; finish

-- Full cycle: (3, 0, 0, d+1, e, f) →⁺ (3, 0, 0, d+2, e+d+3, f+2*d+4)
theorem main_cycle (hd : d + 1 ≤ 3 * (e + 2)) :
    ⟨3, 0, 0, d + 1, e, f⟩ [fm]⊢⁺ ⟨3, 0, 0, d + 2, e + d + 3, f + 2 * d + 4⟩ := by
  -- Phase 1: R2 x 3
  step fm; step fm; step fm
  -- Phase 2: R4 drain d+1 to b
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_trans (r4_drain (d + 1) (b := 0) (d := 0))
  rw [show 0 + (d + 1) = d + 1 from by ring]
  -- Phase 3-5: R5, R1, R3
  step fm; step fm; step fm
  -- Phase 6: Middle phase
  apply stepStar_trans (middle (d + 1) (e + 2) (f + 2) (by omega))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0, 0⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e f, q = ⟨3, 0, 0, d + 1, e, f⟩ ∧ d + 1 ≤ 3 * (e + 2))
  · intro c ⟨d, e, f, hq, hd⟩; subst hq
    exact ⟨⟨3, 0, 0, d + 2, e + d + 3, f + 2 * d + 4⟩,
      ⟨d + 1, e + d + 3, f + 2 * d + 4, rfl, by omega⟩,
      main_cycle hd⟩
  · exact ⟨0, 0, 0, rfl, by omega⟩
