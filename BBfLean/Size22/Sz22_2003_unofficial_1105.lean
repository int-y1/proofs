import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1105: [5/6, 4/35, 539/2, 3/11, 242/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  2  1
 0  1  0  0 -1
 1  0  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1105

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- R3 repeated: drain a to d and e.
-- (a+k, 0, 0, d, e) →* (a, 0, 0, d+2*k, e+k)
theorem r3_drain : ∀ k, ∀ d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

-- R4 repeated: drain e to b.
-- (0, b, 0, d, e+k) →* (0, b+k, 0, d, e)
theorem e_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- R2 repeated (with b=0): drain c and d, increase a.
-- (a, 0, k, d+k, e) →* (a+2*k, 0, 0, d, e)
theorem r2_chain : ∀ k, ∀ a d, ⟨a, 0, k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d)
    ring_nf; finish

-- Interleaving phase (generalized with c):
-- (1, b+1, c, d+b+1+c, 2) ⊢* (b+2+2*c, 0, 0, d, 2)
-- By strong induction on b with base cases b=0 and b=1.
theorem interleave_gen : ∀ b, ∀ c d, ⟨1, b + 1, c, d + b + 1 + c, 2⟩ [fm]⊢* ⟨b + 2 + 2 * c, 0, 0, d, 2⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro c d
  rcases b with _ | _ | b
  · -- b = 0: (1, 1, c, d+1+c, 2) → R1 → (0, 0, c+1, d+1+c, 2) → R2 chain (c+1 steps)
    rw [show d + 0 + 1 + c = d + (c + 1) from by ring]
    step fm
    show ⟨0, 0, c + 1, d + (c + 1), 2⟩ [fm]⊢* ⟨0 + 2 + 2 * c, 0, 0, d, 2⟩
    apply stepStar_trans (r2_chain (c + 1) 0 d (e := 2))
    ring_nf; finish
  · -- b = 1: (1, 2, c, d+2+c, 2) → R1 → (0, 1, c+1, d+2+c, 2)
    --   → R2 → (2, 1, c, d+1+c, 2) → R1 → (1, 0, c+1, d+1+c, 2)
    --   → R2 chain (c+1 steps) → (2c+3, 0, 0, d, 2)
    rw [show d + 1 + 1 + c = (d + c + 1) + 1 from by ring]
    step fm
    rw [show d + c + 1 + 1 = (d + c) + 1 + 1 from by ring]
    step fm
    step fm
    show ⟨1, 0, c + 1, d + (c + 1), 2⟩ [fm]⊢* ⟨1 + 2 + 2 * c, 0, 0, d, 2⟩
    apply stepStar_trans (r2_chain (c + 1) 1 d (e := 2))
    ring_nf; finish
  · -- b+2: (1, b+3, c, d+b+3+c, 2) → R1 → (0, b+2, c+1, d+b+3+c, 2)
    --   → R2 → (2, b+2, c, d+b+2+c, 2) → R1 → (1, b+1, c+1, d+b+2+c, 2)
    --   Apply IH with b, c+1: (1, b+1, c+1, d+b+1+(c+1), 2) ⊢* (b+2+2*(c+1), 0, 0, d, 2)
    rw [show d + (b + 2) + 1 + c = (d + b + 2 + c) + 1 from by ring]
    step fm -- R1: (0, b+2, c+1, (d+b+2+c)+1, 2)
    step fm -- R2: (2, b+2, c, d+b+2+c, 2)
    step fm -- R1: (1, b+1, c+1, d+b+2+c, 2)
    rw [show d + b + 2 + c = d + b + 1 + (c + 1) from by ring]
    apply stepStar_trans (ih b (by omega) (c + 1) d)
    ring_nf; finish

-- Specialization: (1, b+1, 0, d+b+1, 2) ⊢* (b+2, 0, 0, d, 2)
theorem interleave : ∀ b d, ⟨1, b + 1, 0, d + b + 1, 2⟩ [fm]⊢* ⟨b + 2, 0, 0, d, 2⟩ := by
  intro b d
  have h := interleave_gen b 0 d
  rw [show d + b + 1 + 0 = d + b + 1 from by ring,
      show b + 2 + 2 * 0 = b + 2 from by ring] at h
  exact h

-- R3 drain (full version from 0): (k, 0, 0, d, e) →* (0, 0, 0, d+2*k, e+k)
theorem r3_drain_full : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

-- Main cycle: (a+8, 0, 0, d, 2) ⊢⁺ (a+11, 0, 0, d+a+5, 2)
theorem main_trans : ⟨a + 8, 0, 0, d, 2⟩ [fm]⊢⁺ ⟨a + 11, 0, 0, d + a + 5, 2⟩ := by
  -- Phase 1: first R3 step (to get ⊢⁺), then R3 drain full
  rw [show a + 8 = (a + 7) + 1 from by ring]
  step fm
  -- Now at (a+7, 0, 0, d+2, 3) ⊢* target
  apply stepStar_trans (r3_drain_full (a + 7) (d + 2) 3)
  -- Now at (0, 0, 0, d+2+2*(a+7), 3+(a+7))
  -- Phase 2: R4 drain
  rw [show (3 : ℕ) + (a + 7) = 0 + (a + 10) from by ring,
      show d + 2 + 2 * (a + 7) = d + 2 * a + 16 from by ring]
  apply stepStar_trans (e_to_b (a + 10) 0 (d + 2 * a + 16) (e := 0))
  -- Now at (0, 0+(a+10), 0, d+2a+16, 0)
  -- Phase 3: R5 kick
  rw [show (0 : ℕ) + (a + 10) = a + 10 from by ring,
      show d + 2 * a + 16 = (d + 2 * a + 15) + 1 from by ring]
  step fm
  -- Now at (1, a+10, 0, d+2a+15, 2)
  -- Phase 4: interleave (b = a+9)
  rw [show (a : ℕ) + 10 = (a + 9) + 1 from by ring,
      show d + 2 * a + 15 = (d + a + 5) + (a + 9) + 1 from by ring]
  apply stepStar_trans (interleave (a + 9) (d + a + 5))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨8, 0, 0, 1, 2⟩)
  · execute fm 47
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + 8, 0, 0, d, 2⟩) ⟨0, 1⟩
  intro ⟨a, d⟩
  exact ⟨⟨a + 3, d + a + 5⟩, main_trans⟩

end Sz22_2003_unofficial_1105
