import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #823: [35/6, 8/55, 143/2, 3/7, 14/13]

Vector representation:
```
-1 -1  1  1  0  0
 3  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_823

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

-- R4 chain: move d to b
theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R3 chain: drain a, incrementing e and f
theorem r3_drain : ∀ k, ⟨k, 0, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih generalizing d e f
  · exists 0
  · step fm
    apply stepStar_trans (ih (e := e + 1) (f := f + 1))
    ring_nf; finish

-- R2 chain: consume c using e
theorem r2_chain : ∀ c, ⟨a, 0, c, D, E + c, F⟩ [fm]⊢* ⟨a + 3 * c, 0, 0, D, E, F⟩ := by
  intro c; induction' c with c ih generalizing a D E F
  · exists 0
  · rw [show E + (c + 1) = (E + c) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 3))
    ring_nf; finish

-- Combined R1/R2 chain
theorem r1r2_chain : ∀ b, ∀ a c D E F,
    ⟨a + 1, b, c, D, E + b + c, F⟩ [fm]⊢* ⟨a + 1 + 2 * b + 3 * c, 0, 0, D + b, E, F⟩ := by
  intro b; induction' b with b ih <;> intro a c D E F
  · exact r2_chain c
  · rw [show E + (b + 1) + c = E + b + (c + 1) from by ring]
    step fm
    rcases a with _ | a'
    · rw [show E + b + (c + 1) = (E + b + c) + 1 from by ring]
      step fm
      apply stepStar_trans (ih 2 c (D + 1) E F)
      ring_nf; finish
    · apply stepStar_trans (ih a' (c + 1) (D + 1) E F)
      ring_nf; finish

-- Main transition
theorem main_trans : ∀ d e f, ⟨0, 0, 0, d + 1, e + d + 1, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, d + 2, e + 2 * d + 3, f + 2 * d + 3⟩ := by
  intro d e f
  -- Phase 1: R4 x (d+1)
  apply stepStar_stepPlus_stepPlus
  · rw [show (d + 1 : ℕ) = 0 + (d + 1) from by ring]
    exact d_to_b (d + 1) (b := 0) (d := 0) (e := e + d + 1) (f := f + 1)
  -- Now at (0, d+1, 0, 0, e+d+1, f+1)
  -- Phase 2-4: R5, R1, R2 (3 steps)
  step fm -- R5
  step fm -- R1
  rw [show e + d + 1 = (e + d) + 1 from by ring]
  step fm -- R2
  -- Normalize Nat.add 0 d
  show ⟨3, 0 + d, 0, 2, e + d, f⟩ [fm]⊢* _
  rw [Nat.zero_add]
  rw [show (e + d : ℕ) = e + d + 0 from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r1r2_chain d 2 0 2 e f)
  -- Now at (3+2*d, 0, 0, 2+d, e, f)
  -- Phase 6: R3 drain
  rw [show 2 + 1 + 2 * d + 3 * 0 = 2 * d + 3 from by ring,
      show 2 + d = d + 2 from by ring]
  apply stepStar_trans (r3_drain (2 * d + 3) (d := d + 2) (e := e) (f := f))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2, 1⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e f, q = ⟨0, 0, 0, d + 1, e + d + 1, f + 1⟩)
  · intro c ⟨d, e, f, hq⟩; subst hq
    exact ⟨⟨0, 0, 0, d + 2, e + 2 * d + 3, f + 2 * d + 3⟩,
      ⟨d + 1, e + d + 1, f + 2 * d + 2, by ring_nf⟩,
      main_trans d e f⟩
  · exact ⟨0, 1, 0, by ring_nf⟩
