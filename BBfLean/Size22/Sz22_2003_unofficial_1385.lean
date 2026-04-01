import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1385: [63/10, 5/363, 14/3, 11/7, 15/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  0 -2
 1 -1  0  1  0
 0  0  0 -1  1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1385

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem d_to_e : ∀ k d e, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih d (e + 1)); ring_nf; finish

theorem r2_r1_chain : ∀ k a b d e, ⟨a + k, b + 1, 0, d, e + 2 * k⟩ [fm]⊢* ⟨a, b + k + 1, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring,
        show e + 2 * (k + 1) = e + 2 * k + 2 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih a (b + 1) (d + 1) e); ring_nf; finish

theorem r2_chain : ∀ k b c d, ⟨0, b + k, c, d, 2 * k⟩ [fm]⊢* ⟨0, b, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) d); ring_nf; finish

theorem r1_r3_chain : ∀ k b c d, ⟨1, b, c + k + 1, d, 0⟩ [fm]⊢* ⟨1, b + k, c + 1, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show c + (k + 1) + 1 = c + k + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b + 1) c (d + 2)); ring_nf; finish

theorem b_to_a : ∀ k a b d, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a + k, b, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b (d + 1)); ring_nf; finish

-- The full cycle from (n+2, 0, 0, 0, 4n+4) to (n+3, 0, 0, 4n+8, 0)
theorem phases (n : ℕ) : ⟨n + 2, 0, 0, 0, 4 * n + 4⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 4 * n + 8, 0⟩ := by
  -- R5: (n+2, 0, 0, 0, 4n+4) → (n+1, 1, 1, 0, 4n+4)
  -- R1: (n+1, 1, 1, 0, 4n+4) → (n, 3, 0, 1, 4n+4)
  -- R2+R1 chain (n rounds): (n, 3, 0, 1, 4n+4) →* (0, n+3, 0, n+1, 2n+4)
  -- R2 chain (n+2 rounds): (0, n+3, 0, n+1, 2n+4) →* (0, 1, n+2, n+1, 0)
  -- R3: (0, 1, n+2, n+1, 0) → (1, 0, n+2, n+2, 0)
  -- R1+R3 chain (n+1 rounds): (1, 0, n+2, n+2, 0) →* (1, n+1, 1, 3n+4, 0)
  -- R1: (1, n+1, 1, 3n+4, 0) → (0, n+3, 0, 3n+5, 0)
  -- R3 chain (n+3 rounds): (0, n+3, 0, 3n+5, 0) →* (n+3, 0, 0, 4n+8, 0)
  -- Build intermediate results using have
  have p1 : ⟨n, 3, 0, 1, 4 * n + 4⟩ [fm]⊢* ⟨0, n + 3, 0, n + 1, 2 * n + 4⟩ := by
    have h := r2_r1_chain n 0 2 1 (2 * n + 4)
    rw [show 0 + n = n from by ring, show 2 + 1 = 3 from by ring,
        show (2 * n + 4) + 2 * n = 4 * n + 4 from by ring,
        show 2 + n + 1 = n + 3 from by ring, show 1 + n = n + 1 from by ring] at h
    exact h
  have p2 : ⟨0, n + 3, 0, n + 1, 2 * n + 4⟩ [fm]⊢* ⟨0, 1, n + 2, n + 1, 0⟩ := by
    have h := r2_chain (n + 2) 1 0 (n + 1)
    rw [show 1 + (n + 2) = n + 3 from by ring, show 2 * (n + 2) = 2 * n + 4 from by ring,
        show 0 + (n + 2) = n + 2 from by ring] at h
    exact h
  have p3 : fm ⟨0, 1, n + 2, n + 1, 0⟩ = some ⟨1, 0, n + 2, n + 2, 0⟩ := by simp [fm]
  have p4 : ⟨1, 0, n + 2, n + 2, 0⟩ [fm]⊢* ⟨1, n + 1, 1, 3 * n + 4, 0⟩ := by
    have h := r1_r3_chain (n + 1) 0 0 (n + 2)
    rw [show 0 + (n + 1) + 1 = n + 2 from by ring, show 0 + (n + 1) = n + 1 from by ring,
        show 0 + 1 = 1 from by ring, show (n + 2) + 2 * (n + 1) = 3 * n + 4 from by ring] at h
    exact h
  have p5 : fm ⟨1, n + 1, 1, 3 * n + 4, 0⟩ = some ⟨0, n + 3, 0, 3 * n + 5, 0⟩ := by simp [fm]
  have p6 : ⟨0, n + 3, 0, 3 * n + 5, 0⟩ [fm]⊢* ⟨n + 3, 0, 0, 4 * n + 8, 0⟩ := by
    have h := b_to_a (n + 3) 0 0 (3 * n + 5)
    rw [show 0 + (n + 3) = n + 3 from by ring, show (3 * n + 5) + (n + 3) = 4 * n + 8 from by ring] at h
    exact h
  -- R5 then R1
  step fm; step fm
  -- After steps: (n, 3, 0, 1, 4*n+3+1) — need 4*n+3+1 = 4*n+4
  rw [show 4 * n + 3 + 1 = 4 * n + 4 from by ring]
  apply stepStar_trans p1
  apply stepStar_trans p2
  apply stepStar_trans (step_stepStar p3)
  apply stepStar_trans p4
  apply stepStar_trans (step_stepStar p5)
  exact p6

theorem main_trans (n : ℕ) : ⟨n + 2, 0, 0, 4 * (n + 1), 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 4 * (n + 2), 0⟩ := by
  rw [show 4 * (n + 1) = 0 + (4 * n + 4) from by ring,
      show 4 * (n + 2) = 4 * n + 8 from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (4 * n + 4) 0 0)
  rw [show 0 + (4 * n + 4) = 4 * n + 4 from by ring]
  exact phases n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 4, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 4 * (n + 1), 0⟩) 0
  intro n; exists n + 1; exact main_trans n
