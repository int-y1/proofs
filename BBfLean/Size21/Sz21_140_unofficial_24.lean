import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #24: [28/15, 3/22, 65/2, 11/7, 21/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_24

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- Phase 1: R3 repeated: a → c, f (when b=0, e=0)
theorem a_to_cf : ∀ k, ∀ a c d f, ⟨a+k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
  intro k; induction' k with k ih <;> intro a c d f
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- Phase 2: R4 repeated: d → e
theorem d_to_e : ∀ k, ∀ c d e f, ⟨0, 0, c, d+k, e, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- Phase 4: R2+R1 rounds
theorem r2r1_chain : ∀ k, ∀ a c d e, ⟨a+1, 0, c+k, d, e+k, f⟩ [fm]⊢* ⟨a+1+k, 0, c, d+k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  have h := ih (a + 1) c (d + 1) e
  rw [show a + 2 = a + 1 + 1 from by ring]
  apply stepStar_trans h
  ring_nf; finish

-- Phase 5: R2 repeated: drain e into b
theorem drain_e : ∀ k, ∀ a b d f, ⟨a+k, b, 0, d, k, f⟩ [fm]⊢* ⟨a, b+k, 0, d, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a b d f
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- Phase 6: R3+R1 alternating rounds
theorem r3r1_chain : ∀ k, ∀ a b d f, ⟨a+2, b+k, 0, d, 0, f⟩ [fm]⊢* ⟨a+2+k, b, 0, d+k, 0, f+k⟩ := by
  intro k; induction' k with k ih <;> intro a b d f
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm; step fm
  rw [show a + 3 = (a + 1) + 2 from by ring]
  apply stepStar_trans (ih (a + 1) b (d + 1) (f + 1))
  ring_nf; finish

-- Canonical state: (n+2, 0, 0, 2*n+2, 0, n*n+n) → (n+3, 0, 0, 2*n+4, 0, n*n+3*n+2)
theorem full_cycle (n : ℕ) : ⟨n+2, 0, 0, 2*n+2, 0, n*n+n⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 2*n+4, 0, n*n+3*n+2⟩ := by
  -- Phase 1: R3 × (n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+2, 2*n+2, 0, n*n+2*n+2⟩)
  · have h := a_to_cf (n+2) 0 0 (2*n+2) (n*n+n)
    simp only [Nat.zero_add] at h
    -- h : (n+2, 0, 0, 2n+2, 0, n*n+n) →* (0, 0, n+2, 2n+2, 0, n*n+n+(n+2))
    -- Need to show f matches: n*n+n+(n+2) = n*n+2*n+2
    rw [show n * n + n + (n + 2) = n * n + 2 * n + 2 from by ring] at h
    exact h
  -- Phase 2: R4 × (2n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+2, 0, 2*n+2, n*n+2*n+2⟩)
  · have h := d_to_e (2*n+2) (n+2) 0 0 (n*n+2*n+2)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 × 1 (gives stepPlus)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, n+2, 1, 2*n+2, n*n+2*n+1⟩)
  · rw [show n * n + 2 * n + 2 = (n * n + 2 * n + 1) + 1 from by ring]
    simp [fm]
  -- Phase 4a: R1 × 1
  apply stepStar_trans (c₂ := ⟨2, 0, n+1, 2, 2*n+2, n*n+2*n+1⟩)
  · rw [show n + 2 = (n + 1) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm; finish
  -- Phase 4b: R2+R1 × (n+1) rounds
  apply stepStar_trans (c₂ := ⟨n+3, 0, 0, n+3, n+1, n*n+2*n+1⟩)
  · have h := r2r1_chain (n+1) 1 0 2 (n+1) (f := n*n+2*n+1)
    -- h : (1+1, 0, 0+(n+1), 2, (n+1)+(n+1), ...) →* (1+1+(n+1), 0, 0, 2+(n+1), n+1, ...)
    rw [show (1 : ℕ) + 1 = 2 from by ring,
        show (0 : ℕ) + (n + 1) = n + 1 from by ring,
        show (n + 1 : ℕ) + (n + 1) = 2 * n + 2 from by ring,
        show (2 : ℕ) + (n + 1) = n + 3 from by ring] at h
    exact h
  -- Phase 5: R2 × (n+1): drain e
  apply stepStar_trans (c₂ := ⟨2, n+1, 0, n+3, 0, n*n+2*n+1⟩)
  · have h := drain_e (n+1) 2 0 (n+3) (n*n+2*n+1)
    simp only [Nat.zero_add] at h
    rw [show (2 : ℕ) + (n + 1) = n + 3 from by ring] at h
    exact h
  -- Phase 6: R3+R1 × (n+1) rounds
  have h := r3r1_chain (n+1) 0 0 (n+3) (n*n+2*n+1)
  simp only [Nat.zero_add] at h
  -- h : (0+2, 0+(n+1), 0, n+3, 0, n*n+2*n+1) →* (0+2+(n+1), 0, 0, (n+3)+(n+1), 0, (n*n+2*n+1)+(n+1))
  rw [show (2 : ℕ) + (n + 1) = n + 3 from by ring,
      show (n + 3 : ℕ) + (n + 1) = 2 * n + 4 from by ring,
      show (n * n + 2 * n + 1 : ℕ) + (n + 1) = n * n + 3 * n + 2 from by ring] at h
  exact h

-- Main transition wrapper
theorem main_trans (n : ℕ) : ⟨n+2, 0, 0, 2*(n+1), 0, n*(n+1)⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 2*(n+2), 0, (n+1)*(n+2)⟩ := by
  have h := full_cycle n
  rw [show 2 * (n + 1) = 2 * n + 2 from by ring,
      show n * (n + 1) = n * n + n from by ring,
      show 2 * (n + 2) = 2 * n + 4 from by ring,
      show (n + 1) * (n + 2) = n * n + 3 * n + 2 from by ring]
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+2, 0, 0, 2*(n+1), 0, n*(n+1)⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩

end Sz21_140_unofficial_24
