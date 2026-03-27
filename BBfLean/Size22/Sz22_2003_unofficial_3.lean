import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #3: [1/105, 15/22, 4/3, 49/2, 363/7]

Vector representation:
```
 0 -1 -1 -1  0
-1  1  1  0 -1
 2 -1  0  0  0
-1  0  0  2  0
 0  1  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_3

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R3 chain: convert b to a (when d=0, e=0)
theorem r3_chain : ∀ k, ∀ a c, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · simp; exists 0
  step fm
  apply stepStar_trans (h (a + 2) c)
  rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring]; finish

-- R4 chain: convert a to d (when b=0, e=0)
theorem r4_chain : ∀ k, ∀ a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · simp; exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h a c (d + 2))
  rw [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]; finish

-- R5/R1 drain: convert c and d to e (paired rounds)
theorem r5r1_drain : ∀ k, ∀ c d e, ⟨0, 0, c + k, d + 2 * k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + 2 * k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · simp; exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + 2 * (k + 1) = (d + 2 * k) + 1 + 1 from by ring]
  step fm  -- R5
  step fm  -- R1
  apply stepStar_trans (h c d (e + 2))
  rw [show e + 2 + 2 * k = e + 2 * (k + 1) from by ring]; finish

-- R2/R3 interleaving: (0, b+1, c, 0, e) ⊢* (2*(b+1)+e, 0, c+e, 0, 0)
theorem r2r3_chain : ∀ e, ∀ b c, ⟨0, b + 1, c, 0, e⟩ [fm]⊢* ⟨2 * (b + 1) + e, 0, c + e, 0, 0⟩ := by
  intro e
  induction' e using Nat.strongRecOn with e ih
  intro b c
  match e with
  | 0 =>
    simp only [Nat.add_zero]
    have h := r3_chain (b + 1) 0 c
    simp only [Nat.zero_add] at h; exact h
  | 1 =>
    step fm  -- R3: (2, b, c, 0, 1)
    step fm  -- R2: (1, b+1, c+1, 0, 0)
    apply stepStar_trans (r3_chain (b + 1) 1 (c + 1))
    rw [show 1 + 2 * (b + 1) = 2 * (b + 1) + 1 from by ring]; finish
  | e + 2 =>
    step fm  -- R3: (2, b, c, 0, e+2)
    step fm  -- R2: (1, b+1, c+1, 0, e+1)
    step fm  -- R2: (0, b+2, c+2, 0, e)
    apply stepStar_trans (ih e (by omega) (b + 1) (c + 2))
    rw [show 2 * ((b + 1) + 1) + e = 2 * (b + 1) + (e + 2) from by ring,
        show c + 2 + e = c + (e + 2) from by ring]; finish

-- Main transition: (1, 0, 0, 0, e) ⊢⁺ (1, 0, 0, 0, 2*e+1)
theorem main_trans (e : ℕ) : ⟨1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2 * e + 1⟩ := by
  rcases e with _ | e
  · -- e = 0: 5 steps via R4 then closing
    execute fm 5
  · -- e ≥ 1: phase 1 → phase 2 → phase 3 → phase 4
    apply step_stepStar_stepPlus
    · show fm ⟨1, 0, 0, 0, e + 1⟩ = some ⟨0, 1, 1, 0, e⟩; rfl
    -- After R2: (0, 1, 1, 0, e)
    -- r2r3_chain gives: (0, 0+1, 1, 0, e) ⊢* (2*(0+1)+e, 0, 1+e, 0, 0)
    apply stepStar_trans (r2r3_chain e 0 1)
    rw [show 2 * (0 + 1) + e = e + 2 from by ring,
        show 1 + e = e + 1 from by ring]
    apply stepStar_trans (c₂ := ⟨0, 0, e + 1, 2 * (e + 2), 0⟩)
    · have h := r4_chain (e + 2) 0 (e + 1) 0
      simp only [Nat.zero_add] at h; exact h
    apply stepStar_trans (c₂ := ⟨0, 0, 0, 2, 2 * (e + 1)⟩)
    · have h := r5r1_drain (e + 1) 0 2 0
      simp only [Nat.zero_add] at h
      rw [show 2 + 2 * (e + 1) = 2 * (e + 2) from by ring] at h
      exact h
    execute fm 4

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨1, 0, 0, 0, n⟩) 0
  intro n; exists 2 * n + 1; exact main_trans n

end Sz22_2003_unofficial_3
