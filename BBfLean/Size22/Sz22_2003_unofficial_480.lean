import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #480: [28/15, 3/22, 1225/2, 11/7, 3/11]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  2  0
 0  0  0 -1  1
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_480

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: drain d to e
theorem d_to_e : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R3 chain: drain a, adding 2 to c and d each step
theorem r3_chain : ∀ k, ∀ c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d + 2 * k, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show k + 1 = k + 1 from rfl]; step fm
  apply stepStar_trans (h (c + 2) (d + 2)); ring_nf; finish

-- Interleaved R1/R2 chain: k+1 R1 steps and k R2 steps
theorem r1r2_chain : ∀ k, ∀ a d e,
    ⟨a, 1, k + 1, d, e + k⟩ [fm]⊢* ⟨a + k + 2, 0, 0, d + k + 1, e⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · step fm; ring_nf; finish
  rw [show k + 1 + 1 = (k + 1) + 1 from by ring,
      show e + (k + 1) = e + k + 1 from by ring]
  step fm
  rw [show a + 2 = (a + 1) + 1 from by ring,
      show e + k + 1 = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h (a + 1) (d + 1) e); ring_nf; finish

-- R2 drain when c=0
theorem r2_drain : ∀ k, ∀ a b d,
    ⟨a + k, b, 0, d, k⟩ [fm]⊢* ⟨a, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show k + 1 = k + 1 from rfl]
  step fm
  apply stepStar_trans (h a (b + 1) d); ring_nf; finish

-- (R3, R1, R1) chain: K rounds, each consuming 2 from b
theorem r3r1r1_chain : ∀ k, ∀ a d,
    ⟨a + 1, 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, d + 4 * k, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
  step fm
  rw [show 2 * k + 1 = 2 * k + 1 from rfl]
  step fm
  rw [show d + 2 + 1 = d + 2 + 1 from rfl]
  step fm
  rw [show a + 3 + 1 = (a + 3) + 1 from by ring]
  apply stepStar_trans (h (a + 3) (d + 4)); ring_nf; finish

-- Main transition:
-- (0, 0, 2m+2K+2, 2m+4K+2, 0) →⁺ (0, 0, 4m+6K+6, 6m+12K+8, 0)
theorem main_trans (m K : ℕ) :
    ⟨0, 0, 2 * m + 2 * K + 2, 2 * m + 4 * K + 2, 0⟩ [fm]⊢⁺
    ⟨0, 0, 4 * m + 6 * K + 6, 6 * m + 12 * K + 8, 0⟩ := by
  -- Phase 1: R4*(2m+4K+2): drain d to e
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2 * m + 2 * K + 2, 0, 2 * m + 4 * K + 2⟩)
  · have h := d_to_e (2 * m + 4 * K + 2) (2 * m + 2 * K + 2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 2 * m + 2 * K + 2, 0, 2 * m + 4 * K + 1⟩)
  · show fm ⟨0, 0, 2 * m + 2 * K + 2, 0, (2 * m + 4 * K + 1) + 1⟩ =
         some ⟨0, 1, 2 * m + 2 * K + 2, 0, 2 * m + 4 * K + 1⟩
    simp [fm]
  -- Phase 3: R1/R2 chain (2m+2K+2 rounds, k = 2m+2K+1)
  apply stepStar_trans (c₂ := ⟨2 * m + 2 * K + 3, 0, 0, 2 * m + 2 * K + 2, 2 * K⟩)
  · have h := r1r2_chain (2 * m + 2 * K + 1) 0 0 (2 * K)
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Phase 4: R2 drain (2K steps)
  apply stepStar_trans (c₂ := ⟨2 * m + 3, 2 * K, 0, 2 * m + 2 * K + 2, 0⟩)
  · have h := r2_drain (2 * K) (2 * m + 3) 0 (2 * m + 2 * K + 2)
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Phase 5: (R3, R1, R1) chain (K rounds)
  apply stepStar_trans (c₂ := ⟨2 * m + 3 * K + 3, 0, 0, 2 * m + 6 * K + 2, 0⟩)
  · have h := r3r1r1_chain K (2 * m + 2) (2 * m + 2 * K + 2)
    convert h using 2; ring_nf
  -- Phase 6: R3 chain
  have h := r3_chain (2 * m + 3 * K + 3) 0 (2 * m + 6 * K + 2)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, K⟩ ↦ ⟨0, 0, 2 * m + 2 * K + 2, 2 * m + 4 * K + 2, 0⟩) ⟨0, 0⟩
  intro ⟨m, K⟩; exact ⟨⟨m + 1, m + 1 + 3 * K⟩, by
    show ⟨0, 0, 2 * m + 2 * K + 2, 2 * m + 4 * K + 2, 0⟩ [fm]⊢⁺
         ⟨0, 0, 2 * (m + 1) + 2 * (m + 1 + 3 * K) + 2,
          2 * (m + 1) + 4 * (m + 1 + 3 * K) + 2, 0⟩
    convert main_trans m K using 2; ring_nf⟩

end Sz22_2003_unofficial_480
