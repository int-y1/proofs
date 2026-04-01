import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1300: [63/10, 121/2, 2/33, 5/7, 42/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 1 -1  0  0 -1
 0  0  1 -1  0
 1  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1300

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer d to c
theorem d_to_c : ∀ k, ∀ c d, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- R1/R3 interleaving: (1, b, c+k, d, e+k) →* (1, b+k, c, d+k, e)
theorem r1r3_chain : ∀ k, ∀ b c d e, ⟨1, b, c + k, d, e + k⟩ [fm]⊢* ⟨1, b + k, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by omega,
        show e + (k + 1) = (e + k) + 1 from by omega]
    step fm  -- R1: (0, b+2, c+k, d+1, e+k+1)
    step fm  -- R3: (1, b+1, c+k, d+1, e+k)
    apply stepStar_trans (ih (b + 1) c (d + 1) e)
    ring_nf; finish

-- R2/R3 drain: (1, b+k, 0, d, e) →* (1, b, 0, d, e+k) when c=0
theorem r2r3_drain : ∀ k, ∀ b d e, ⟨1, b + k, 0, d, e⟩ [fm]⊢* ⟨1, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by omega]
    step fm  -- R2: (0, b+k+1, 0, d, e+2)
    step fm  -- R3: (1, b+k, 0, d, e+1)
    apply stepStar_trans (ih b d (e + 1))
    ring_nf; finish

-- Main transition: (1, 0, 0, n+1, 2*(n+1)) →⁺ (1, 0, 0, n+2, 2*(n+2))
theorem main_trans (n : ℕ) :
    ⟨1, 0, 0, n + 1, 2 * (n + 1)⟩ [fm]⊢⁺ ⟨1, 0, 0, n + 2, 2 * (n + 2)⟩ := by
  -- Step 1: R2
  rw [show 2 * (n + 1) = 2 * n + 2 from by ring]
  step fm  -- (0, 0, 0, n+1, 2*n+4)
  -- Step 2: R4 × (n+1)
  show ⟨0, 0, 0, n + 1, 2 * n + 4⟩ [fm]⊢* ⟨1, 0, 0, n + 2, 2 * (n + 2)⟩
  rw [show (n + 1 : ℕ) = 0 + (n + 1) from by omega]
  apply stepStar_trans (d_to_c (n + 1) 0 0 (e := 2 * n + 4))
  -- Now at (0, 0, n+1, 0, 2*n+4)
  show ⟨0, 0, 0 + (n + 1), 0, 2 * n + 4⟩ [fm]⊢* ⟨1, 0, 0, n + 2, 2 * (n + 2)⟩
  -- Step 3: R5
  rw [show 2 * n + 4 = (2 * n + 3) + 1 from by omega,
      show 0 + (n + 1) = n + 1 from by omega]
  step fm  -- R5: (1, 1, n+1, 1, 2*n+3)
  -- Step 4: R1/R3 × (n+1)
  show ⟨1, 1, n + 1, 1, 2 * n + 3⟩ [fm]⊢* ⟨1, 0, 0, n + 2, 2 * (n + 2)⟩
  rw [show (n + 1 : ℕ) = 0 + (n + 1) from by omega,
      show (2 * n + 3 : ℕ) = (n + 2) + (n + 1) from by omega]
  apply stepStar_trans (r1r3_chain (n + 1) 1 0 1 (n + 2))
  -- Now at (1, n+2, 0, n+2, n+2)
  show ⟨1, 1 + (n + 1), 0, 1 + (n + 1), n + 2⟩ [fm]⊢* ⟨1, 0, 0, n + 2, 2 * (n + 2)⟩
  -- Step 5: R2/R3 × (n+2)
  rw [show 1 + (n + 1) = 0 + (n + 2) from by omega]
  apply stepStar_trans (r2r3_drain (n + 2) 0 (0 + (n + 2)) (n + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 2⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, n + 1, 2 * (n + 1)⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
