import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1400: [7/15, 1/3, 132/7, 25/2, 1/55, 3/5]

Vector representation:
```
 0 -1 -1  1  0
 0 -1  0  0  0
 2  1  0 -1  1
-1  0  2  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1400

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3+R1 interleaved chain: k rounds
theorem r3r1_chain : ∀ k c j, ⟨2*j, 0, c+k, 1, j⟩ [fm]⊢* ⟨2*(j+k), 0, c, 1, j+k⟩ := by
  intro k; induction' k with k ih
  · intro c j; exists 0
  · intro c j
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih c (j + 1)); ring_nf; finish

-- R4 chain: drain a, converting to c
theorem r4_chain : ∀ k a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c e; exists 0
  · intro a c e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2) e); ring_nf; finish

-- R5 chain: drain e, consuming c and e
theorem r5_chain : ∀ k c e, ⟨0, 0, c+k, 0, e+k⟩ [fm]⊢* ⟨0, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c e; exists 0
  · intro c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c e); ring_nf; finish

-- Combined: opening + R3R1 chain + closing + R4 chain + R5 chain
theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * n + 3, 0, 0⟩ := by
  rw [show n + 2 = (n + 1) + 1 from by ring]
  -- R6
  step fm
  -- R1
  step fm
  -- Now at (0, 0, n, 1, 0). Apply R3+R1 chain.
  rw [show (0 : ℕ) = 2 * 0 from by ring,
      show n = 0 + n from by ring]
  apply stepStar_trans (r3r1_chain n 0 0)
  -- Now at (2*n, 0, 0, 1, n). R3 then R2.
  rw [show 0 + n = n from by ring]
  step fm; step fm
  -- Now at (2*n+2, 0, 0, 0, n+1). Apply R4 chain.
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (r4_chain (2 * n + 2) 0 0 (n + 1))
  -- Now at (0, 0, 4*n+4, 0, n+1). Apply R5 chain.
  show ⟨0, 0, 0 + 2 * (2 * n + 2), 0, n + 1⟩ [fm]⊢* ⟨0, 0, 3 * n + 3, 0, 0⟩
  have h := r5_chain (n + 1) (3 * n + 3) 0
  simp only [Nat.zero_add] at h
  rw [show 0 + 2 * (2 * n + 2) = (3 * n + 3) + (n + 1) from by ring]
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 0, 0⟩) 0
  intro n; exact ⟨3 * n + 1, main_trans n⟩

end Sz22_2003_unofficial_1400
