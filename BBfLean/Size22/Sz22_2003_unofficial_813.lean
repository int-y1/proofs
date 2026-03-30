import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #813: [35/6, 7865/2, 4/77, 3/5, 7/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  1  0  2  1
 2  0  0 -1 -1  0
 0  1 -1  0  0  0
 0  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_813

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+2, f+1⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d+1, e, f⟩
  | _ => none

-- R4 repeated: move c to b.
theorem c_to_b : ∀ k, ∀ b e f,
    ⟨(0 : ℕ), b, k, 0, e, f⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

-- R1,R1,R3 chain: k rounds.
-- Each round: R1 twice (a:2->1->0, b-=2, c+=2, d+=2), then R3 (a:0->2, d-=1, e-=1).
-- Net per round: b -= 2, c += 2, d += 1, e -= 1.
theorem r1r1r3_chain : ∀ k, ∀ c d e f,
    ⟨(2 : ℕ), 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨(2 : ℕ), 0, c + 2 * k, d + k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm -- R1: (1, 2*k+1, c+1, d+1, e+k+1, f)
    step fm -- R1: (0, 2*k, c+2, d+2, e+k+1, f)
    rw [show d + 2 = (d + 1) + 1 from by ring,
        show e + k + 1 = (e + k) + 1 from by ring]
    step fm -- R3: (2, 2*k, c+2, d+1, e+k, f)
    apply stepStar_trans (ih (c + 2) (d + 1) e f)
    ring_nf; finish

-- R3,R2,R2 chain: k rounds.
-- Each round: R3 (a:0->2, d-=1, e-=1), R2 twice (a:2->1->0, c+=2, e+=4, f+=2).
-- Net per round: c += 2, d -= 1, e += 3, f += 2.
theorem r3r2r2_chain : ∀ k, ∀ c e f,
    ⟨(0 : ℕ), 0, c, k, e + 1, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + 2 * k, 0, e + 3 * k + 1, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  · step fm -- R3: (2, 0, c, k, e, f)
    step fm -- R2: (1, 0, c+1, k, e+2, f+1)
    step fm -- R2: (0, 0, c+2, k, e+4, f+2)
    rw [show e + 4 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (c + 2) (e + 3) (f + 2))
    ring_nf; finish

-- Main transition: canonical state (0, 2*b, 0, 0, b+2+e, f+1) steps to
-- (0, 2*(2*b+1), 0, 0, (2*b+1)+2+(b+2+e), (2*b+f+1)+1).
theorem main_transition : ∀ b e f,
    ⟨(0 : ℕ), 2 * b, 0, 0, b + 2 + e, f + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 2 * (2 * b + 1), 0, 0, (2 * b + 1) + 2 + (b + 2 + e), (2 * b + f + 1) + 1⟩ := by
  intro b e f
  -- Phase 1: R5, R3
  step fm -- R5: (0, 2*b, 0, 1, b+2+e, f)
  rw [show b + 2 + e = (b + 1 + e) + 1 from by ring]
  step fm -- R3: (2, 2*b, 0, 0, b+1+e, f)
  -- Phase 2: R1,R1,R3 chain with k=b
  rw [show b + 1 + e = e + 1 + b from by ring]
  apply stepStar_trans (r1r1r3_chain b 0 0 (e + 1) f)
  -- Now at (2, 0, 2*b, b, e+1, f)
  rw [show (0 : ℕ) + 2 * b = 2 * b from by ring,
      show (0 : ℕ) + b = b from by ring]
  -- Phase 3: R2, R2
  step fm -- R2: (1, 0, 2*b+1, b, e+3, f+1)
  step fm -- R2: (0, 0, 2*b+2, b, e+5, f+2)
  -- Phase 4: R3,R2,R2 chain with k=b
  rw [show e + 5 = (e + 4) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain b (2 * b + 2) (e + 4) (f + 2))
  -- Now at (0, 0, 4*b+2, 0, e+4+3*b+1, f+2+2*b)
  -- Phase 5: R4 chain
  rw [show 2 * b + 2 + 2 * b = 4 * b + 2 from by ring]
  apply stepStar_trans (c_to_b (4 * b + 2) 0 (e + 4 + 3 * b + 1) (f + 2 + 2 * b))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 4, 0, 0, 6, 3⟩)
  · execute fm 13
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨b, e, f⟩ ↦ ⟨0, 2 * b, 0, 0, b + 2 + e, f + 1⟩) ⟨2, 2, 2⟩
  intro ⟨b, e, f⟩
  exact ⟨⟨2 * b + 1, b + 2 + e, 2 * b + f + 1⟩, main_transition b e f⟩
