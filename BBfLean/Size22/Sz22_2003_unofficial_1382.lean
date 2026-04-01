import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1382: [63/10, 5/33, 4/3, 11/7, 147/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  0 -1
 2 -1  0  0  0
 0  0  0 -1  1
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1382

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- R4: transfer d to e (with b=0, c=0).
theorem d_to_e : ∀ k, ∀ d e, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih d (e + 1)); ring_nf; finish

-- R3: drain b into a (with c=0, e=0).
theorem r3_chain : ∀ k, ∀ A d, ⟨A, k, 0, d, 0⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro A d
  · exists 0
  · step fm
    apply stepStar_trans (ih (A + 2) d); ring_nf; finish

-- R2+R1 interleaved chain: k pairs.
theorem r2r1_chain : ∀ k, ∀ A E,
    ⟨A + k, 1, 0, 2, E + k⟩ [fm]⊢* ⟨A, k + 1, 0, k + 2, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  · rw [show A + (k + 1) = (A + 1) + k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    apply stepStar_trans (ih (A + 1) (E + 1))
    step fm; step fm; ring_nf; finish

-- Main transition: C(n) ⊢⁺ C(n+1) where C(n) = (n²+4n+5, 0, 0, 2n+4, 0).
theorem main_trans (n : ℕ) :
    ⟨n * n + 4 * n + 5, 0, 0, 2 * n + 4, 0⟩ [fm]⊢⁺
    ⟨n * n + 6 * n + 10, 0, 0, 2 * n + 6, 0⟩ := by
  -- Phase 1: R4 (first step gives ⊢⁺)
  rw [show 2 * n + 4 = (2 * n + 3) + 1 from by ring]
  step fm
  -- Now at ⊢* with (a, 0, 0, 2n+3, 1). Continue d_to_e for remaining 2n+3.
  rw [show 2 * n + 3 = 0 + (2 * n + 3) from by ring]
  apply stepStar_trans (d_to_e (2 * n + 3) 0 1 (a := n * n + 4 * n + 5))
  -- Now at (a, 0, 0, 0, 2n+4).
  rw [show (1 + (2 * n + 3) : ℕ) = 2 * n + 4 from by ring]
  -- Phase 2: R5 step
  rw [show n * n + 4 * n + 5 = (n * n + 4 * n + 4) + 1 from by ring]
  step fm
  -- Now at (n²+4n+4, 1, 0, 2, 2n+4).
  -- Phase 3: r2r1_chain with k = 2n+4
  rw [show n * n + 4 * n + 4 = (n * n + 2 * n) + (2 * n + 4) from by ring]
  conv in (occs := 2) (2 * n + 4) => rw [show 2 * n + 4 = 0 + (2 * n + 4) from by ring]
  apply stepStar_trans (r2r1_chain (2 * n + 4) (n * n + 2 * n) 0)
  -- Now at (n²+2n, 2n+5, 0, 2n+6, 0).
  rw [show (2 * n + 4 + 1 : ℕ) = 2 * n + 5 from by ring,
      show (2 * n + 4 + 2 : ℕ) = 2 * n + 6 from by ring,
      show (0 : ℕ) = 0 from rfl]
  -- Phase 4: r3_chain with k = 2n+5
  apply stepStar_trans (r3_chain (2 * n + 5) (n * n + 2 * n) (2 * n + 6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 4, 0⟩)
  · execute fm 12
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n * n + 4 * n + 5, 0, 0, 2 * n + 4, 0⟩) 0
  intro n; refine ⟨n + 1, ?_⟩
  show ⟨n * n + 4 * n + 5, 0, 0, 2 * n + 4, 0⟩ [fm]⊢⁺
    ⟨(n + 1) * (n + 1) + 4 * (n + 1) + 5, 0, 0, 2 * (n + 1) + 4, 0⟩
  rw [show (n + 1) * (n + 1) + 4 * (n + 1) + 5 = n * n + 6 * n + 10 from by ring,
      show 2 * (n + 1) + 4 = 2 * n + 6 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1382
