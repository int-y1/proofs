import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #105: [1/30, 49/2, 6/77, 25/7, 242/5]

Vector representation:
```
-1 -1 -1  0  0
-1  0  0  2  0
 1  1  0 -1 -1
 0  0  2 -1  0
 1  0 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_105

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- R4 loop: convert d to c (when a=0, e=0)
theorem d_to_c : ∀ k, ∀ b c d, ⟨0, b, c, d+k, 0⟩ [fm]⊢* ⟨0, b, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro b c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R5/R1 interleaved: consume b and c, produce e
theorem r5r1_chain : ∀ k, ∀ b c e, ⟨0, b+k, c+2*k, 0, e⟩ [fm]⊢* ⟨0, b, c, 0, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro b c e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k + 1) + 1 from by ring]
  step fm
  rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3/R2 interleaved: consume e, build b and d
theorem r3r2_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d+1, e+k⟩ [fm]⊢* ⟨0, b+k, 0, d+k+1, e⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: (0, 2n, 0, 2n+2, 0) →⁺ (0, 4n+2, 0, 4n+4, 0)
theorem main_trans (n : ℕ) : ⟨0, 2*n, 0, 2*n+2, 0⟩ [fm]⊢⁺ ⟨0, 4*n+2, 0, 4*n+4, 0⟩ := by
  -- Phase 1 first step (R4)
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  -- Now: (0, 2n, 2, 2n+1, 0) →* (0, 4n+2, 0, 4n+4, 0)
  -- Phase 1 remainder
  apply stepStar_trans (c₂ := ⟨0, 2*n, 4*n+4, 0, 0⟩)
  · have h := d_to_c (2*n+1) (2*n) 2 0
    simp only [Nat.zero_add,
               (show 2 + 2 * (2 * n + 1) = 4 * n + 4 from by ring)] at h
    exact h
  -- Phase 2: R5/R1 chain
  apply stepStar_trans (c₂ := ⟨0, 0, 4, 0, 4*n⟩)
  · have h := r5r1_chain (2*n) 0 4 0
    simp only [Nat.zero_add,
               (show 4 + 2 * (2 * n) = 4 * n + 4 from by ring),
               (show 0 + 2 * (2 * n) = 4 * n from by ring)] at h
    exact h
  -- Phase 3: fixed sequence
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 2, 4*n+2⟩)
  · execute fm 8
  -- Phase 4: R3/R2 chain
  have h := r3r2_chain (4*n+2) 0 1 0
  simp only [Nat.zero_add,
             (show 1 + 1 = 2 from by ring),
             (show 1 + (4 * n + 2) + 1 = 4 * n + 4 from by ring)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 4, 0⟩) (by execute fm 15)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2*(n+1), 0, 2*(n+1)+2, 0⟩) 0
  intro n
  exists 2*n + 2
  have h := main_trans (n + 1)
  simp only [(show 4 * (n + 1) + 2 = 2 * (2 * n + 2 + 1) from by ring),
             (show 4 * (n + 1) + 4 = 2 * (2 * n + 2 + 1) + 2 from by ring)] at h
  exact h

end Sz22_2003_unofficial_105
