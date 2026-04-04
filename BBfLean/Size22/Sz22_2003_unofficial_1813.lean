import BBfLean.FM

/-!
# sz22_2003_unofficial #1813: [9/10, 55/21, 2/3, 7/11, 693/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  2  0  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1813

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e+1⟩
  | _ => none

-- R4 chain: move e to d.
theorem e_to_d : ∀ e, ∀ d, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + e, 0⟩ := by
  intro e; induction' e with e ih <;> intro d
  · exists 0
  · rw [show d + (e + 1) = (d + 1) + e from by omega]
    step fm
    exact ih (d + 1)

-- R3 chain: move b to a (when c=0, d=0).
theorem b_to_a : ∀ b, ∀ a, ⟨a, b, 0, 0, e⟩ [fm]⊢* ⟨a + b, 0, 0, 0, e⟩ := by
  intro b; induction' b with b ih <;> intro a
  · exists 0
  · have h1 : ⟨a, b + 1, 0, 0, e⟩ [fm]⊢ ⟨a + 1, b, 0, 0, e⟩ := by unfold fm; simp
    apply stepStar_trans (step_stepStar h1)
    have h := ih (a + 1)
    rw [show a + 1 + b = a + (b + 1) from by omega] at h
    exact h

-- R2/R1 drain: alternating R2 then R1, draining a.
theorem r2r1_drain : ∀ k, ∀ a b d e, ⟨a + k, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨a, b + k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by omega,
        show d + (k + 1) = (d + k) + 1 from by omega]
    step fm  -- R2
    step fm  -- R1
    have h := ih a (b + 1) d (e + 1)
    rw [show b + 1 + k + 1 = b + (k + 1) + 1 from by omega,
        show e + 1 + k = e + (k + 1) from by omega] at h
    exact h

-- Pure R2 drain: (0, b+k, c, d+k, e) →* (0, b, c+k, d, e+k)
theorem r2_drain : ∀ k, ∀ b c d e, ⟨0, b + k, c, d + k, e⟩ [fm]⊢* ⟨0, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by omega,
        show d + (k + 1) = (d + k) + 1 from by omega]
    step fm  -- R2
    have h := ih b (c + 1) d (e + 1)
    rw [show c + 1 + k = c + (k + 1) from by omega,
        show e + 1 + k = e + (k + 1) from by omega] at h
    exact h

-- R1/R3 drain of c: (1, b, c+1, 0, e) →* (0, b+c+2, 0, 0, e)
theorem r1r3_drain : ∀ k, ∀ b, ⟨1, b, k + 1, 0, e⟩ [fm]⊢* ⟨0, b + k + 2, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · step fm; finish
  · step fm  -- R1: (0, b+2, k+1, 0, e)
    step fm  -- R3: (1, b+1, k+1, 0, e)
    have h := ih (b + 1)
    rw [show b + 1 + k + 2 = b + (k + 1) + 2 from by omega] at h
    exact h

-- Composed phase: from (0, n+3, 0, n+2, n+2) to (n+3, 0, 0, 2*(n+2), 0)
theorem phase_tail : ⟨0, n + 3, 0, n + 2, n + 2⟩ [fm]⊢* ⟨n + 3, 0, 0, 2 * (n + 2), 0⟩ := by
  have h1 := r2_drain (n + 2) 1 0 0 (n + 2)
  rw [show 1 + (n + 2) = n + 3 from by omega,
      show 0 + (n + 2) = n + 2 from by omega] at h1
  apply stepStar_trans h1
  -- State: (0, 1, n+2, 0, n+2+(n+2))
  rw [show n + 2 + (n + 2) = 2 * n + 4 from by omega]
  -- Need to fire R3: (0, 1, n+2, 0, 2*n+4) → (1, 0, n+2, 0, 2*n+4)
  apply stepStar_trans (step_stepStar (show ⟨0, 1, n + 2, 0, 2 * n + 4⟩ [fm]⊢ ⟨1, 0, n + 2, 0, 2 * n + 4⟩ from by simp [fm]))
  -- State: (1, 0, n+2, 0, 2*n+4)
  rw [show n + 2 = (n + 1) + 1 from by omega]
  apply stepStar_trans (r1r3_drain (n + 1) 0 (e := 2 * n + 4))
  -- State: (0, n+3, 0, 0, 2*n+4)
  have h2 := b_to_a (0 + (n + 1) + 2) 0 (e := 2 * n + 4)
  rw [show 0 + (0 + (n + 1) + 2) = n + 3 from by omega] at h2
  apply stepStar_trans h2
  -- State: (n+3, 0, 0, 0, 2*n+4)
  have h3 := e_to_d (2 * n + 4) 0 (a := n + 3)
  rw [show 0 + (2 * n + 4) = 2 * (n + 2) from by omega] at h3
  exact h3

-- Main transition: (n+2, 0, 0, 2*(n+1), 0) →⁺ (n+3, 0, 0, 2*(n+2), 0)
theorem main_trans : ∀ n, ⟨n + 2, 0, 0, 2 * (n + 1), 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 2 * (n + 2), 0⟩ := by
  intro n
  rw [show 2 * (n + 1) = (n + 2) + n from by omega]
  step fm
  -- After R5: (n+1, 2, 0, (n+2)+n+1, 1)
  have h1 := r2r1_drain (n + 1) 0 1 (n + 2) 1
  rw [show 0 + (n + 1) = n + 1 from by omega,
      show (n + 2) + (n + 1) = (n + 2) + n + 1 from by omega,
      show 1 + (n + 1) + 1 = n + 3 from by omega,
      show 1 + (n + 1) = n + 2 from by omega] at h1
  apply stepStar_trans h1
  exact phase_tail

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 2 * (n + 1), 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
