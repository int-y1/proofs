import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1778: [9/10, 343/2, 22/21, 5/11, 3/7]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  3  0
 1 -1  0 -1  1
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1778

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: (0, 0, c, d, k) →* (0, 0, c+k, d, 0)
theorem e_to_c : ∀ k c d, ⟨(0 : ℕ), 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- R3+R1 spiral: (0, b+1, n, n+(d+1), e) →* (0, b+n+1, 0, d+1, e+n)
theorem r3r1_spiral : ∀ n, ∀ b d e, ⟨(0 : ℕ), b + 1, n, n + (d + 1), e⟩ [fm]⊢* ⟨0, b + n + 1, 0, d + 1, e + n⟩ := by
  intro n; induction' n with n ih <;> intro b d e
  · ring_nf; finish
  · -- R3: (0, b+1, n+1, (n+1)+(d+1), e) → (1, b, n+1, n+(d+1), e+1)
    -- Note: (n+1)+(d+1) = n+d+2 = (n+d+1)+1, and R3 matches d+1 pattern
    apply stepStar_trans (step_stepStar (show ⟨(0 : ℕ), b + 1, n + 1, (n + 1) + (d + 1), e⟩ [fm]⊢
              ⟨1, b, n + 1, (n + 1) + d, e + 1⟩ from by simp [fm]))
    -- R1: (1, b, n+1, n+1+d, e+1) → (0, b+2, n, n+1+d, e+1)
    -- Note: n+1+d = n+(d+1) for the recursive call
    apply stepStar_trans (step_stepStar (show ⟨(1 : ℕ), b, n + 1, (n + 1) + d, e + 1⟩ [fm]⊢
              ⟨0, b + 2, n, (n + 1) + d, e + 1⟩ from by simp [fm]))
    rw [show (n + 1) + d = n + (d + 1) from by ring]
    apply stepStar_trans (ih (b + 1) d (e + 1))
    ring_nf; finish

-- R3+R2 drain: (0, b+1, 0, d+1, e) →⁺ (0, 0, 0, d+2*b+3, e+b+1)
theorem r3r2_drain : ∀ b, ∀ d e, ⟨(0 : ℕ), b + 1, 0, d + 1, e⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2 * b + 3, e + b + 1⟩ := by
  intro b; induction' b with b ih <;> intro d e
  · step fm; step fm; ring_nf; finish
  · -- R3: (0, b+2, 0, d+1, e) → (1, b+1, 0, d, e+1)
    -- R2: (1, b+1, 0, d, e+1) → (0, b+1, 0, d+3, e+1)
    apply step_stepPlus_stepPlus (show ⟨(0 : ℕ), b + 2, 0, d + 1, e⟩ [fm]⊢
              ⟨1, b + 1, 0, d, e + 1⟩ from by simp [fm])
    apply step_stepPlus_stepPlus (show ⟨(1 : ℕ), b + 1, 0, d, e + 1⟩ [fm]⊢
              ⟨0, b + 1, 0, d + 3, e + 1⟩ from by simp [fm])
    rw [show d + 3 = (d + 2) + 1 from by ring]
    apply stepPlus_stepStar_stepPlus (ih (d + 2) (e + 1))
    ring_nf; finish

-- R5 + spiral + drain: (0, 0, k, k+3, 0) →⁺ (0, 0, 0, 2*k+4, 2*k+1)
theorem spiral_and_drain : ∀ k, ⟨(0 : ℕ), 0, k, k + 3, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 4, 2 * k + 1⟩ := by
  intro k
  -- R5: (0, 0, k, k+3, 0) → (0, 1, k, k+2, 0)
  apply step_stepPlus_stepPlus (show ⟨(0 : ℕ), 0, k, k + 3, 0⟩ [fm]⊢
    ⟨0, 1, k, k + 2, 0⟩ from by rw [show k + 3 = (k + 2) + 1 from by ring]; simp [fm])
  -- Spiral: (0, 1, k, k+2, 0) →* (0, k+1, 0, 2, k)
  rw [show k + 2 = k + (1 + 1) from by ring]
  have h_spiral := r3r1_spiral k 0 1 0
  rw [show (0 : ℕ) + 1 = 1 from by ring] at h_spiral
  apply stepStar_stepPlus_stepPlus h_spiral
  -- Drain: (0, k+1, 0, 2, k) →⁺ (0, 0, 0, 2k+4, 2k+1)
  rw [show (0 : ℕ) + k + 1 = k + 1 from by ring,
      show (0 : ℕ) + k = k from by ring,
      show 1 + 1 = (2 : ℕ) from by ring]
  have h_drain := r3r2_drain k 1 k
  rw [show 1 + 2 * k + 3 = 2 * k + 4 from by ring,
      show k + k + 1 = 2 * k + 1 from by ring] at h_drain
  exact h_drain

-- Main transition: (0, 0, 0, k+3, k) →⁺ (0, 0, 0, 2*k+4, 2*k+1)
theorem main_trans : ∀ k, ⟨(0 : ℕ), 0, 0, k + 3, k⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 4, 2 * k + 1⟩ := by
  intro k
  have h1 := e_to_c k 0 (k + 3)
  rw [Nat.zero_add] at h1
  exact stepStar_stepPlus_stepPlus h1 (spiral_and_drain k)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, 0, k + 3, k⟩) 0
  intro k; exists 2 * k + 1
  exact main_trans k

end Sz22_2003_unofficial_1778
