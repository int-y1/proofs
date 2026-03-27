import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #35: [1/15, 3/14, 44/3, 5/2, 7/55, 3/5]

Vector representation:
```
 0 -1 -1  0  0
-1  1  0 -1  0
 2 -1  0  0  1
-1  0  1  0  0
 0  0 -1  1 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_35

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 chain: a → c
theorem r3_chain : ∀ k, ∀ a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 chain: c,e → d
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2 chain: b → a,e (when c=0, d=0)
theorem r2_chain : ∀ k, ∀ a b e, ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+2*k, b, 0, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a b e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Drain: (2, b, 0, D, e) ⊢* (2*b + D + 2, 0, 0, 0, b + D + e)
-- by strong induction on D
theorem drain : ∀ D, ∀ b e, ⟨2, b, 0, D, e⟩ [fm]⊢* ⟨2*b + D + 2, 0, 0, 0, b + D + e⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro b e
  rcases D with _ | _ | D
  · -- D=0: R2 chain to drain b
    have := r2_chain b 2 0 e
    simp only [Nat.zero_add,
               (by ring : 2 + 2 * b = 2 * b + 0 + 2),
               (by ring : e + b = b + 0 + e)] at this
    exact this
  · -- D=1: R1 then R2 chain
    rw [show (2:ℕ) = 0 + 1 + 1 from by ring, show (1:ℕ) = 0 + 1 from by ring]
    step fm
    have := r2_chain (b + 1) 1 0 e
    simp only [Nat.zero_add,
               (by ring : 1 + 2 * (b + 1) = 2 * b + 1 + 2),
               (by ring : e + (b + 1) = b + 1 + e)] at this
    exact this
  · -- D+2: R1, R1, R2 → (2, b+1, 0, D, e+1), then IH
    -- (2, b, 0, D+2, e): R1: a=2>=1, d=D+2>=1 → (1, b+1, 0, D+1, e)
    -- (1, b+1, 0, D+1, e): R1: a=1>=1, d=D+1>=1 → (0, b+2, 0, D, e)
    -- (0, b+2, 0, D, e): R2: b+2>=1 → (2, b+1, 0, D, e+1)
    rw [show (2:ℕ) = 0 + 1 + 1 from by ring,
        show D + 2 = (D + 1) + 1 from by ring,
        show D + 1 = D + 1 from rfl]
    step fm
    rw [show D + 1 = D + 1 from rfl]
    step fm
    rw [show b + 1 + 1 = (b + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih D (by omega) _ _)
    ring_nf; finish

-- Main transition: (n+2, 0, 0, 0, n+1) ⊢⁺ (n+3, 0, 0, 0, n+2)
theorem main_trans (n : ℕ) : ⟨n+2, 0, 0, 0, n+1⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 0, n+2⟩ := by
  -- Phase 1: R3 chain (n+2 steps): (n+2, 0, 0, 0, n+1) → (0, 0, n+2, 0, n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+2, 0, n+1⟩)
  · have := r3_chain (n+2) 0 0 (n+1)
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R4 chain (n+1 steps): (0, 0, n+2, 0, n+1) → (0, 0, 1, n+1, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 1, n+1, 0⟩)
  · have := r4_chain (n+1) 1 0 0
    simp only [Nat.zero_add, (by ring : 1 + (n + 1) = n + 2)] at this; exact this
  -- Phase 3: R5 (1 step): (0, 0, 1, n+1, 0) → (0, 1, 0, n+1, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0 + 1, n + 1, 0⟩ = some ⟨0, 0 + 1, 0, n + 1, 0⟩; simp [fm]
  -- Phase 4: R2 (1 step): (0, 1, 0, n+1, 0) → (2, 0, 0, n+1, 1)
  apply stepStar_trans (c₂ := ⟨2, 0, 0, n+1, 1⟩)
  · rw [show (1:ℕ) = 0 + 1 from by ring]; step fm; ring_nf; finish
  -- Phase 5: Drain: (2, 0, 0, n+1, 1) → (n+3, 0, 0, 0, n+2)
  have := drain (n+1) 0 1
  simp only [Nat.zero_add, (by ring : 2 * 0 + (n + 1) + 2 = n + 3)] at this
  exact this

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+2, 0, 0, 0, n+1⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩

end Sz22_2003_unofficial_35
