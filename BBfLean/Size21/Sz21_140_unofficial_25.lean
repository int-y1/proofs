import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #25: [28/15, 3/22, 65/2, 11/7, 33/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  0
 0  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_25

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

-- Phase 1: R3 repeated: a → c, f (when b=0, e=0)
theorem a_to_cf : ∀ k, ∀ a c f, ⟨a+k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
  intro k; induction' k with k h <;> intro a c f
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 2: R4 repeated: d → e (when a=0, b=0)
theorem d_to_e : ∀ k, ∀ d e, ⟨0, 0, c, d+k, e, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k, f⟩ := by
  intro k; induction' k with k h <;> intro d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Phase 5: R2 repeated: a,e → b (when c=0)
theorem ae_to_b : ∀ k, ∀ a b, ⟨a+k, b, 0, d, k, f⟩ [fm]⊢* ⟨a, b+k, 0, d, 0, f⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Phase 4: chain of (R2, R1) rounds
-- One round: (a+1, 0, c+1, d, e+1, f) →R2→ (a, 1, c+1, d, e, f) →R1→ (a+2, 0, c, d+1, e, f)
-- Net per round: a: +1, c: -1, d: +1, e: -1
-- Chain: (a+1, 0, c+k, d, e+k, f) →* (a+k+1, 0, c, d+k, e, f)
theorem r2r1_chain : ∀ k, ∀ a c d e, ⟨a+1, 0, c+k, d, e+k, f⟩ [fm]⊢* ⟨a+k+1, 0, c, d+k, e, f⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  -- R2: (a+1, 0, (c+k)+1, d, (e+k)+1, f) → (a, 1, (c+k)+1, d, e+k, f)
  step fm
  -- R1: (a, 1, (c+k)+1, d, e+k, f) → (a+2, 0, c+k, d+1, e+k, f)
  step fm
  -- Now: (a+2, 0, c+k, d+1, e+k, f)
  -- IH with a' = a+1: (a+1+1, 0, c+k, d+1, e+k, f) →* (a+1+k+1, 0, c, d+1+k, e, f)
  have h2 := h (a+1) c (d+1) e
  rw [show a + 2 = a + 1 + 1 from by ring] at *
  refine stepStar_trans h2 ?_
  ring_nf; finish

-- Phase 6: chain of (R3, R1) rounds
-- One round: (a+1, b+1, 0, d, 0, f) →R3→ (a, b+1, 1, d, 0, f+1) →R1→ (a+2, b, 0, d+1, 0, f+1)
-- Net per round: a: +1, b: -1, d: +1, f: +1
-- Chain: (a+1, b+k, 0, d, 0, f) →* (a+k+1, b, 0, d+k, 0, f+k)
theorem r3r1_chain : ∀ k, ∀ a b d f, ⟨a+1, b+k, 0, d, 0, f⟩ [fm]⊢* ⟨a+k+1, b, 0, d+k, 0, f+k⟩ := by
  intro k; induction' k with k h <;> intro a b d f
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  step fm
  have h2 := h (a+1) b (d+1) (f+1)
  rw [show a + 2 = a + 1 + 1 from by ring] at *
  refine stepStar_trans h2 ?_
  ring_nf; finish

-- Main transition: C(n) = (n+1, 0, 0, 2*n, 0, n*n) →⁺ C(n+1) = (n+2, 0, 0, 2*n+2, 0, (n+1)*(n+1))
theorem main_trans (n : ℕ) : ⟨n+1, 0, 0, 2*n, 0, n*n⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 2*n+2, 0, (n+1)*(n+1)⟩ := by
  -- Phase 1: R3 × (n+1): →* (0, 0, n+1, 2n, 0, n²+n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, 2*n, 0, n*n+n+1⟩)
  · have h := a_to_cf (d := 2*n) (n+1) 0 0 (n*n)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 × 2n: →* (0, 0, n+1, 0, 2n, n²+n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, 0, 2*n, n*n+n+1⟩)
  · have h := d_to_e (c := n+1) (f := n*n+n+1) (2*n) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 step: →⁺ (0, 1, n+1, 0, 2n+1, n²+n)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, n+1, 0, 2*n+1, n*n+n⟩)
  · show fm ⟨0, 0, n+1, 0, 2*n, (n*n+n) + 1⟩ = some ⟨0, 1, n+1, 0, 2*n+1, n*n+n⟩
    simp [fm]
  -- Phase 4a: First R1 step: (0, 1, n+1, 0, 2n+1, n²+n) → (2, 0, n, 1, 2n+1, n²+n)
  apply stepStar_trans (c₂ := ⟨2, 0, n, 1, 2*n+1, n*n+n⟩)
  · have : fm ⟨0, 0+1, n+1, 0, 2*n+1, n*n+n⟩ = some ⟨0+2, 0, n, 0+1, 2*n+1, n*n+n⟩ := by
      simp [fm]
    exact step_stepStar this
  -- Phase 4b: n rounds of (R2, R1)
  -- r2r1_chain k=n, a=1, c=0, d=1, e=(n+1):
  -- (1+1, 0, 0+n, 1, (n+1)+n, f) →* (1+n+1, 0, 0, 1+n, n+1, f)
  apply stepStar_trans (c₂ := ⟨n+2, 0, 0, n+1, n+1, n*n+n⟩)
  · have h := r2r1_chain (f := n*n+n) n 1 0 1 (n+1)
    simp only [Nat.zero_add] at h
    rw [show 1 + 1 = 2 from by ring,
        show (n + 1) + n = 2 * n + 1 from by ring,
        show 1 + n + 1 = n + 2 from by ring,
        show 1 + n = n + 1 from by ring] at h
    exact h
  -- Phase 5: R2 × (n+1): (n+2, 0, 0, n+1, n+1, f) →* (1, n+1, 0, n+1, 0, f)
  apply stepStar_trans (c₂ := ⟨1, n+1, 0, n+1, 0, n*n+n⟩)
  · have h := ae_to_b (d := n+1) (f := n*n+n) (n+1) 1 0
    simp only [Nat.zero_add] at h
    rw [show 1 + (n + 1) = n + 2 from by ring] at h
    exact h
  -- Phase 6: R3,R1 × (n+1) rounds: (1, n+1, 0, n+1, 0, n²+n) →* (n+2, 0, 0, 2n+2, 0, (n+1)²)
  -- r3r1_chain k=n+1, a=0, b=0, d=n+1, f=n*n+n:
  -- (0+1, 0+(n+1), 0, n+1, 0, n*n+n) →* (0+(n+1)+1, 0, 0, (n+1)+(n+1), 0, (n*n+n)+(n+1))
  have h := r3r1_chain (n+1) 0 0 (n+1) (n*n+n)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, 0, 2*n, 0, n*n⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩
