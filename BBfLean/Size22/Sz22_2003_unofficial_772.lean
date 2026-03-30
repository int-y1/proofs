import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #772: [35/6, 52/55, 77/2, 3/13, 65/7]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  1
-1  0  0  1  1  0
 0  1  0  0  0 -1
 0  0  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_772

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | _ => none

-- R3 drain: with b=0, c=0, only R3 fires.
theorem r3_drain : ∀ n d e f, ⟨n, 0, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d + n, e + n, f⟩ := by
  intro n; induction' n with n ih <;> intro d e f
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1) (e + 1) f)
    ring_nf; finish

-- R4 drain: with a=0, c=0, only R4 fires (when f>=1).
theorem r4_drain : ∀ f b d e, ⟨0, b, 0, d, e, f⟩ [fm]⊢* ⟨0, b + f, 0, d, e, 0⟩ := by
  intro f; induction' f with f ih <;> intro b d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R1/R1/R2 chain: each round does R1, R1, R2.
theorem r1r1r2_chain : ∀ e c d f,
    ⟨2, 2 * e, c, d, e, f⟩ [fm]⊢* ⟨2, 0, c + e, d + 2 * e, 0, f + e⟩ := by
  intro e; induction' e with e ih <;> intro c d f
  · exists 0
  · rw [show 2 * (e + 1) = (2 * e + 1) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih (c + 1) (d + 2) (f + 1))
    ring_nf; finish

-- R3/R2 chain: each pair does R3 then R2.
theorem r3_r2_chain : ∀ c a d f,
    ⟨a + 1, 0, c, d, 0, f⟩ [fm]⊢* ⟨a + 1 + c, 0, 0, d + c, 0, f + c⟩ := by
  intro c; induction' c with c ih <;> intro a d f
  · exists 0
  · step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (d + 1) (f + 1))
    ring_nf; finish

-- Main transition: (a+1, 0, 0, d, 0, 2*a) ⊢⁺ (a+2, 0, 0, d+4*a, 0, 2*a+2)
theorem main_trans (a d : ℕ) :
    ⟨a + 1, 0, 0, d, 0, 2 * a⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, d + 4 * a, 0, 2 * a + 2⟩ := by
  -- Phase A: R3 drain (a+1 steps)
  apply stepStar_stepPlus_stepPlus (r3_drain (a + 1) d 0 (2 * a))
  rw [show 0 + (a + 1) = a + 1 from by ring]
  -- Phase B: R4 drain (2*a steps)
  apply stepStar_stepPlus_stepPlus (r4_drain (2 * a) 0 (d + a + 1) (a + 1))
  rw [show 0 + 2 * a = 2 * a from by ring]
  -- Phase C start: R5
  step fm
  -- Phase C: R2
  step fm
  -- Phase C loop: R1/R1/R2 chain (a rounds)
  apply stepStar_trans (r1r1r2_chain a 0 (d + a) 2)
  rw [show 0 + a = a from by ring, show d + a + 2 * a = d + 3 * a from by ring,
      show 2 + a = a + 2 from by ring]
  -- Phase D: R3/R2 chain (a pairs)
  show ⟨1 + 1, 0, a, d + 3 * a, 0, a + 2⟩ [fm]⊢* ⟨a + 2, 0, 0, d + 4 * a, 0, 2 * a + 2⟩
  apply stepStar_trans (r3_r2_chain a 1 (d + 3 * a) (a + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0, 2⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + 1, 0, 0, d, 0, 2 * a⟩) ⟨1, 0⟩
  intro ⟨a, d⟩; exact ⟨⟨a + 1, d + 4 * a⟩, main_trans a d⟩
