import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #189: [1/6, 2/35, 275/2, 3/5, 7/33, 2/3]

Vector representation:
```
-1 -1  0  0  0
 1  0 -1 -1  0
-1  0  2  0  1
 0  1 -1  0  0
 0 -1  0  1 -1
 1 -1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_189

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- Rule 4 repeated: c → b.
theorem c_to_b : ∀ k : ℕ, ∀ b c e,
    ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Rule 5 repeated: (b, e) → d.
theorem b_e_to_d : ∀ k : ℕ, ∀ b d e,
    ⟨0, b + k, 0, d, e + k⟩ [fm]⊢* ⟨0, b, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Rule 3 repeated: a → (2c, e).
theorem a_descent : ∀ k : ℕ, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · simp; exists 0
  step fm
  have h := ih (c + 2) (e + 1)
  rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring,
      show e + 1 + k = e + (k + 1) from by ring] at h
  exact h

-- d-reduction by 2.
theorem d_reduce2 : ∀ k d e : ℕ,
    ⟨k + 1, 0, 0, d + 2, e⟩ [fm]⊢* ⟨k + 2, 0, 0, d, e + 1⟩ := by
  intro k d e
  step fm; step fm; step fm
  ring_nf; finish

-- Triangular reduction: (k+1, 0, 0, d, e) →⁺ (0, 0, 2*(k+1)+d, 0, e+(k+1)+d).
theorem tri : ∀ d : ℕ, ∀ k e,
    ⟨k + 1, 0, 0, d, e⟩ [fm]⊢⁺ ⟨0, 0, 2 * (k + 1) + d, 0, e + (k + 1) + d⟩ := by
  intro d; induction' d using Nat.strongRecOn with d IH
  rcases d with _ | _ | d
  · -- d = 0
    intro k e
    step fm
    have h := a_descent k 2 (e + 1)
    rw [show 2 + 2 * k = 2 * (k + 1) + 0 from by ring,
        show e + 1 + k = e + (k + 1) + 0 from by ring] at h
    exact h
  · -- d = 1
    intro k e
    step fm; step fm; step fm
    have h := a_descent k 3 (e + 2)
    rw [show 3 + 2 * k = 2 * (k + 1) + 1 from by ring,
        show e + 2 + k = e + (k + 1) + 1 from by ring] at h
    exact h
  · -- d + 2
    intro k e
    apply stepStar_stepPlus_stepPlus (d_reduce2 k d e)
    have h := IH d (by omega) (k + 1) (e + 1)
    rw [show 2 * (k + 1 + 1) + d = 2 * (k + 1) + (d + 2) from by ring,
        show e + 1 + (k + 1 + 1) + d = e + (k + 1) + (d + 2) from by ring] at h
    exact h

-- Full cycle.
theorem full_cycle : ∀ n : ℕ,
    ⟨0, 0, n + 2, 0, n + 1⟩ [fm]⊢⁺ ⟨0, 0, n + 3, 0, n + 2⟩ := by
  intro n
  -- Phase 1: c → b
  apply stepStar_stepPlus_stepPlus
  · have h := c_to_b (n + 2) 0 0 (n + 1)
    simp at h; exact h
  -- Phase 2: (b, e) → d
  apply stepStar_stepPlus_stepPlus
  · have h := b_e_to_d (n + 1) 1 0 0
    rw [show 1 + (n + 1) = n + 2 from by ring,
        show 0 + (n + 1) = n + 1 from by ring] at h
    exact h
  -- Rule 6: b → a
  apply step_stepStar_stepPlus
  · show fm ⟨0, 1, 0, n + 1, 0⟩ = some ⟨1, 0, 0, n + 1, 0⟩; simp [fm]
  -- Phase 3: triangular reduction
  have h := tri (n + 1) 0 0
  rw [show 2 * (0 + 1) + (n + 1) = n + 3 from by ring,
      show 0 + (0 + 1) + (n + 1) = n + 2 from by ring] at h
  exact stepPlus_stepStar h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 0, n + 1⟩) 0
  intro n
  exact ⟨n + 1, full_cycle n⟩

end Sz22_2003_unofficial_189
