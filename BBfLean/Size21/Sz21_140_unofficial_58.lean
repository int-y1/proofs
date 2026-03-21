import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #58: [36/35, 5/22, 49/2, 11/3, 5/7]

Vector representation:
```
 2  2 -1 -1  0
-1  0  1  0 -1
-1  0  0  2  0
 0 -1  0  0  1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_58

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 repeated: a → d
theorem a_to_d : ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d+2*k, 0⟩ := by
  have many_step : ∀ k a d, ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d+2*k, 0⟩ := by
    intro k; induction' k with k ih <;> intro a d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact many_step k a d

-- R4 repeated: b → e
theorem b_to_e : ⟨0, b+k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e+k⟩ := by
  have many_step : ∀ k b e, ⟨0, b+k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e+k⟩ := by
    intro k; induction' k with k ih <;> intro b e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact many_step k b e

-- Interleaved R2/R1 rounds
theorem r2r1_chain : ⟨a+1, b, 0, m, m⟩ [fm]⊢* ⟨a+1+m, b+2*m, 0, 0, 0⟩ := by
  have many_step : ∀ m a b, ⟨a+1, b, 0, m, m⟩ [fm]⊢* ⟨a+1+m, b+2*m, 0, 0, 0⟩ := by
    intro m; induction' m with m ih <;> intro a b
    · exists 0
    have step1 : (⟨a + 1, b, 0, m + 1, m + 1⟩ : Q) [fm]⊢ ⟨a, b, 1, m + 1, m⟩ := by
      show fm ⟨a + 1, b, 0, m + 1, m + 1⟩ = some ⟨a, b, 0 + 1, m + 1, m⟩; simp [fm]
    have step2 : (⟨a, b, 1, m + 1, m⟩ : Q) [fm]⊢ ⟨a + 2, b + 2, 0, m, m⟩ := by
      show fm ⟨a, b, 0 + 1, (m) + 1, m⟩ = some ⟨a + 2, b + 2, 0, m, m⟩; simp [fm]
    apply stepStar_trans (step_stepStar step1)
    apply stepStar_trans (step_stepStar step2)
    have h := ih (a + 1) (b + 2)
    rw [show a + 1 + 1 = a + 2 from by ring,
        show a + 1 + 1 + m = a + 1 + (m + 1) from by ring,
        show b + 2 + 2 * m = b + 2 * (m + 1) from by ring] at h
    exact h
  exact many_step m a b

-- Phase 1: R5,R1 chain then R2/R1 rounds
theorem phase1 : ⟨0, 0, 0, n+2, n⟩ [fm]⊢* ⟨n+2, 2*n+2, 0, 0, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨0, 0, 1, n + 1, n⟩)
  · have : (⟨0, 0, 0, n + 2, n⟩ : Q) [fm]⊢ ⟨0, 0, 1, n + 1, n⟩ := by
      rw [show n + 2 = (n + 1) + 1 from by ring]
      show fm ⟨0, 0, 0, (n + 1) + 1, n⟩ = some ⟨0, 0, 0 + 1, n + 1, n⟩; simp [fm]
    exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨2, 2, 0, n, n⟩)
  · have : (⟨0, 0, 1, n + 1, n⟩ : Q) [fm]⊢ ⟨2, 2, 0, n, n⟩ := by
      show fm ⟨0, 0, 0 + 1, (n) + 1, n⟩ = some ⟨0 + 2, 0 + 2, 0, n, n⟩; simp [fm]
    exact step_stepStar this
  have h := @r2r1_chain 1 2 n
  rw [show (1 : ℕ) + 1 = 2 from by ring,
      show 1 + 1 + n = n + 2 from by ring,
      show 2 + 2 * n = 2 * n + 2 from by ring] at h
  exact h

-- Phase 2: drain a into d
theorem phase2 : ⟨n+2, 2*n+2, 0, 0, 0⟩ [fm]⊢* ⟨0, 2*n+2, 0, 2*n+4, 0⟩ := by
  have h := @a_to_d 0 (n + 2) (2 * n + 2) 0
  simp only [Nat.zero_add] at h
  rw [show 2 * (n + 2) = 2 * n + 4 from by ring] at h
  exact h

-- Phase 3: drain b into e
theorem phase3 : ⟨0, 2*n+2, 0, 2*n+4, 0⟩ [fm]⊢* ⟨0, 0, 0, 2*n+4, 2*n+2⟩ := by
  have h := @b_to_e 0 (2 * n + 2) (2 * n + 4) 0
  simp only [Nat.zero_add] at h
  exact h

-- Main transition
theorem main_trans : ⟨0, 0, 0, n+2, n⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*n+4, 2*n+2⟩ := by
  apply stepStar_stepPlus_stepPlus phase1
  apply step_stepStar_stepPlus (c₂ := ⟨n + 1, 2 * n + 2, 0, 2, 0⟩)
  · show fm ⟨(n + 1) + 1, 2 * n + 2, 0, 0, 0⟩ = some ⟨n + 1, 2 * n + 2, 0, 2, 0⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 2 * n + 2, 0, 2 * n + 4, 0⟩)
  · have h := @a_to_d 0 (n + 1) (2 * n + 2) 2
    simp only [Nat.zero_add] at h
    rw [show 2 + 2 * (n + 1) = 2 * n + 4 from by ring] at h
    exact h
  exact phase3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, 0, n+2, n⟩) 0
  intro n; exact ⟨2*n+2, main_trans⟩
