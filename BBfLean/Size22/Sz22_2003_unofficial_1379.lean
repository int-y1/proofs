import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1379: [63/10, 5/33, 2/3, 11/7, 525/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  0 -1
 1 -1  0  0  0
 0  0  0 -1  1
-1  1  2  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1379

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+2, d+1, e⟩
  | _ => none

-- R4: transfer d to e (b=0, c=0)
theorem d_to_e : ∀ k, ∀ d e, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro d e; exists 0
  · intro d e; rw [Nat.add_succ]
    step fm
    apply stepStar_trans (ih d (e + 1)); ring_nf; finish

-- R2+R1 interleaved chain
theorem r2r1_chain : ∀ k, ∀ a b d e, ⟨a + k, b + 1, 0, d, e + k + 1⟩ [fm]⊢* ⟨a, b + k + 1, 0, d + k, e + 1⟩ := by
  intro k; induction' k with k ih
  · intro a b d e; exists 0
  · intro a b d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (b + 1) (d + 1) e); ring_nf; finish

-- R2 drain
theorem r2_drain : ∀ k, ∀ b c, ⟨0, b + k, c, d, k⟩ [fm]⊢* ⟨0, b, c + k, d, 0⟩ := by
  intro k; induction' k with k ih
  · intro b c; exists 0
  · intro b c
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1)); ring_nf; finish

-- R3+R1 interleaved chain
theorem r3r1_chain : ∀ k, ∀ b c d, ⟨0, b + 1, c + k, d, 0⟩ [fm]⊢* ⟨0, b + k + 1, c, d + k, 0⟩ := by
  intro k; induction' k with k ih
  · intro b c d; exists 0
  · intro b c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) c (d + 1)); ring_nf; finish

-- R3 drain
theorem r3_drain : ∀ k, ∀ a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih
  · intro a d; exists 0
  · intro a d; step fm
    apply stepStar_trans (ih (a + 1) d); ring_nf; finish

-- Combined phase: R5+R1+R1+r2r1_chain
-- From (2n+2+1, 0, 0, 0, 3n+3) via R5,R1,R1 to (2n, 5, 0, 3, 3n+3)
-- then r2r1_chain(2n) to (0, 2n+5, 0, 2n+3, n+3)
theorem opening_and_r2r1 (n : ℕ) :
    ⟨2 * n + 3, 0, 0, 0, 3 * n + 3⟩ [fm]⊢⁺ ⟨0, 2 * n + 5, 0, 2 * n + 3, n + 3⟩ := by
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
  step fm
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show 2 * n + 1 = (2 * n) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- Now at (2n, 5, 0, 3, 3n+3)
  -- r2r1_chain needs: (a+k, b+1, 0, d, e+k+1) = (2n, 5, 0, 3, 3n+3)
  -- k=2n, a=0: a+k = 0+2n = 2n ✓
  -- b+1=5: b=4 ✓
  -- e+k+1 = e+2n+1 = 3n+3: e = n+2 ✓
  rw [show (2 * n : ℕ) = 0 + 2 * n from by ring,
      show (5 : ℕ) = 4 + 1 from by ring,
      show 3 * n + 3 = (n + 2) + 2 * n + 1 from by ring]
  apply stepStar_trans (r2r1_chain (2 * n) 0 4 3 (n + 2))
  ring_nf; finish

-- Main transition: (2n+3, 0, 0, 3n+3, 0) ⊢⁺ (2n+5, 0, 0, 3n+6, 0)
theorem main_trans (n : ℕ) :
    ⟨2 * n + 3, 0, 0, 3 * n + 3, 0⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, 0, 3 * n + 6, 0⟩ := by
  -- Phase 1: d_to_e: → (2n+3, 0, 0, 0, 3n+3)
  rw [show 3 * n + 3 = 0 + (3 * n + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (3 * n + 3) 0 0 (a := 2 * n + 3))
  rw [show 0 + (3 * n + 3) = 3 * n + 3 from by ring]
  -- Phases 2-5: opening + r2r1_chain → (0, 2n+5, 0, 2n+3, n+3)
  apply stepPlus_stepStar_stepPlus (opening_and_r2r1 n)
  -- Phase 6: r2_drain with k=n+3
  -- (0, 2n+5, 0, 2n+3, n+3) = (0, (n+2)+(n+3), 0, 2n+3, n+3)
  rw [show 2 * n + 5 = (n + 2) + (n + 3) from by ring]
  apply stepStar_trans (r2_drain (n + 3) (n + 2) 0 (d := 2 * n + 3))
  -- State: (0, n+2, 0+(n+3), 2n+3, 0) = (0, n+2, n+3, 2n+3, 0)
  rw [show 0 + (n + 3) = n + 3 from by ring]
  -- Phase 7: r3r1_chain with k=n+3
  -- (0, n+2, n+3, 2n+3, 0) = (0, (n+1)+1, 0+(n+3), 2n+3, 0)
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show n + 3 = 0 + (n + 3) from by ring]
  apply stepStar_trans (r3r1_chain (n + 3) (n + 1) 0 (2 * n + 3))
  rw [show n + 1 + (n + 3) + 1 = 2 * n + 5 from by ring,
      show 2 * n + 3 + (n + 3) = 3 * n + 6 from by ring]
  -- Phase 8: r3_drain: (0, 2n+5, 0, 3n+6, 0) → (2n+5, 0, 0, 3n+6, 0)
  -- Take one R3 step to get ⊢⁺, then the rest via r3_drain
  rw [show 2 * n + 5 = (2 * n + 4) + 1 from by ring]
  step fm
  apply stepStar_trans (r3_drain (2 * n + 4) 1 (3 * n + 6)); ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 3, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, 0, 3 * n + 3, 0⟩) 0
  intro n; exact ⟨n + 1, by
    rw [show 2 * (n + 1) + 3 = 2 * n + 5 from by ring,
        show 3 * (n + 1) + 3 = 3 * n + 6 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_1379
