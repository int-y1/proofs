import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #525: [28/15, 33/2, 11/3, 5/847, 14/11]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0  1
 0 -1  0  0  1
 0  0  1 -1 -2
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_525

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R2 repeated k times: drain a to b (c=0 so R1 won't fire)
theorem a_to_b : ∀ k b e, ⟨k, b, 0, d, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro b e
  · exists 0
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3 repeated k times: drain b to e (a=0, c=0)
theorem drain_b : ∀ k e, ⟨0, k, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro e
  · exists 0
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R4 repeated k times: convert d,e to c
theorem d_to_c : ∀ k c, ⟨0, 0, c, d+k, e+2*k⟩ [fm]⊢* ⟨0, 0, c+k, d, e⟩ := by
  intro k; induction' k with k h <;> intro c
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by omega,
      show e + 2 * (k + 1) = (e + 2 * k) + 2 from by omega]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R2+R1 interleaved k times: (a+1, 0, k, d, e) →* (a+k+1, 0, 0, d+k, e+k)
theorem r2r1_chain : ∀ k, ∀ a d e, ⟨a+1, 0, k, d, e⟩ [fm]⊢* ⟨a+k+1, 0, 0, d+k, e+k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  step fm; step fm
  rw [show a + 2 = (a + 1) + 1 from by ring]
  apply stepStar_trans (h (a+1) (d+1) (e+1))
  ring_nf; finish

-- Main transition: (n+1, 0, 0, n+1, e+1) →⁺ (n+2, 0, 0, n+2, e+n+1)
theorem main_trans : ⟨n+1, 0, 0, n+1, e+1⟩ [fm]⊢⁺ ⟨n+2, 0, 0, n+2, e+n+1⟩ := by
  -- Phase 1: R2 x (n+1): →* (0, n+1, 0, n+1, e+n+2)
  apply stepStar_stepPlus_stepPlus (a_to_b (d := n+1) (n+1) 0 (e+1))
  -- Phase 2: R3 x (n+1): →* (0, 0, 0, n+1, e+2*n+3)
  rw [show 0 + (n + 1) = n + 1 from by omega]
  apply stepStar_stepPlus_stepPlus (drain_b (d := n+1) (n+1) (e+1+(n+1)))
  -- Phase 3: R4 x (n+1): →* (0, 0, n+1, 0, e+1)
  rw [show e + 1 + (n + 1) + (n + 1) = e + 1 + 2 * (n + 1) from by ring]
  have h3 := @d_to_c 0 (e+1) (n+1) 0
  simp only [Nat.zero_add] at h3
  apply stepStar_stepPlus_stepPlus h3
  -- Phase 4: R5
  step fm
  -- Phase 5: R2+R1 chain x (n+1)
  apply stepStar_trans (r2r1_chain (n+1) 0 1 e)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨n+1, 0, 0, n+1, e+1⟩) ⟨0, 0⟩
  intro ⟨n, e⟩
  exact ⟨⟨n+1, e+n⟩, main_trans⟩

end Sz22_2003_unofficial_525
