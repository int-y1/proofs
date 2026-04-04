import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1812: [9/10, 55/21, 2/3, 7/11, 63/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1812

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R2+R1 interleaved chain: k rounds.
theorem r2r1_chain : ∀ k, ∀ a B d e,
    ⟨a + k, B + 2, 0, d + k, e⟩ [fm]⊢* ⟨a, B + k + 2, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a B d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    rw [show B + 3 = (B + 1) + 2 from by ring]
    apply stepStar_trans (ih a (B + 1) d (e + 1))
    ring_nf; finish

-- R3 repeated: move b to a.
theorem b_to_a : ∀ k, ∀ a b e,
    ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b e)
    ring_nf; finish

-- R4 repeated: move e to d.
theorem e_to_d : ∀ k, ∀ a d e,
    ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) e)
    ring_nf; finish

-- Wrapper for r2r1_chain with cleaned-up form
theorem r2r1_phase (n : ℕ) : ⟨n, 2, 0, n + 1, 0⟩ [fm]⊢* ⟨0, n + 2, 0, 1, n⟩ := by
  have h := r2r1_chain n 0 0 1 0
  simp only [Nat.zero_add, Nat.add_comm 1 n] at h
  exact h

-- Wrapper for b_to_a with cleaned-up form
theorem b_to_a_phase (n : ℕ) : ⟨0, n + 2, 0, 0, n + 1⟩ [fm]⊢* ⟨n + 2, 0, 0, 0, n + 1⟩ := by
  have h := b_to_a (n + 2) 0 0 (n + 1)
  simp only [Nat.zero_add] at h
  exact h

-- Wrapper for e_to_d with cleaned-up form
theorem e_to_d_phase (n : ℕ) : ⟨n + 2, 0, 0, 0, n + 1⟩ [fm]⊢* ⟨n + 2, 0, 0, n + 1, 0⟩ := by
  have h := e_to_d (n + 1) (n + 2) 0 0
  simp only [Nat.zero_add] at h
  exact h

-- Main transition: (n+1, 0, 0, n, 0) →⁺ (n+2, 0, 0, n+1, 0)
theorem main_trans : ∀ n, ⟨n + 1, 0, 0, n, 0⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, n + 1, 0⟩ := by
  intro n
  -- R5: (n+1, 0, 0, n, 0) → (n, 2, 0, n+1, 0)
  step fm
  -- R2+R1 chain: n rounds
  apply stepStar_trans (r2r1_phase n)
  -- Now at (0, n+2, 0, 1, n). Three more steps: R2, R3, R1.
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  step fm
  step fm
  -- Now at (0, n+2, 0, 0, n+1)
  -- R3 drain then R4 drain
  apply stepStar_trans (b_to_a_phase n)
  exact e_to_d_phase n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 1, 0⟩) 0
  intro n; exists n + 1; exact main_trans (n + 1)
