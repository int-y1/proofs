import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #828: [35/6, 8/55, 77/2, 3/7, 4/11]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  0 -1
-1  0  0  1  1
 0  1  0 -1  0
 2  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_828

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ k x d e, ⟨x + k, 0, 0, d, e⟩ [fm]⊢* ⟨x, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro x d e
  · exists 0
  · rw [show x + (k + 1) = (x + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih x (d + 1) (e + 1)); ring_nf; finish

theorem r4_chain : ∀ k b d, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (b + 1) d); ring_nf; finish

theorem r2_chain : ∀ k x c e, ⟨x, 0, c + k, d, e + k⟩ [fm]⊢* ⟨x + 3 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro x c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (x + 3) c e); ring_nf; finish

theorem r3r2_chain : ∀ k x c d, ⟨x + 1, 0, c + k, d, 0⟩ [fm]⊢* ⟨x + 1 + 2 * k, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro x c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    rw [show x + 3 = (x + 2) + 1 from by ring]
    apply stepStar_trans (ih (x + 2) c (d + 1)); ring_nf; finish

theorem interleave : ∀ k b c d e,
    ⟨3, b + 3 * k, c, d, e + k⟩ [fm]⊢* ⟨3, b, c + 2 * k, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3 * k + 2) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show b + 3 * k + 2 = (b + 3 * k + 1) + 1 from by ring]
    step fm
    rw [show b + 3 * k + 1 = (b + 3 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b (c + 2) (d + 3) e); ring_nf; finish

theorem main_transition (n : ℕ) :
    ⟨3 * n + 3, 0, 0, 3 * n + 2, 0⟩ [fm]⊢⁺ ⟨9 * n + 9, 0, 0, 9 * n + 8, 0⟩ := by
  -- Phase 1: R3 x (3n+3)
  have h1 : ⟨3 * n + 3, 0, 0, 3 * n + 2, 0⟩ [fm]⊢* ⟨0, 0, 0, 6 * n + 5, 3 * n + 3⟩ := by
    have := r3_chain (3 * n + 3) 0 (3 * n + 2) 0
    simp only [Nat.zero_add] at this
    rw [show 3 * n + 2 + (3 * n + 3) = 6 * n + 5 from by ring] at this
    exact this
  -- Phase 2: R4 x (6n+5)
  have h2 : ⟨0, 0, 0, 6 * n + 5, 3 * n + 3⟩ [fm]⊢* ⟨0, 6 * n + 5, 0, 0, 3 * n + 3⟩ := by
    have := r4_chain (6 * n + 5) (e := 3 * n + 3) 0 0
    simp only [Nat.zero_add] at this
    exact this
  -- Phase 3: R5 + 2 R1 + R2
  have h3 : ⟨0, 6 * n + 5, 0, 0, 3 * n + 3⟩ [fm]⊢⁺ ⟨3, 6 * n + 3, 1, 2, 3 * n + 1⟩ := by
    rw [show (3 * n + 3 : ℕ) = (3 * n + 2) + 1 from by ring]; step fm
    rw [show (6 * n + 5 : ℕ) = (6 * n + 4) + 1 from by ring]; step fm
    rw [show 6 * n + 4 = (6 * n + 3) + 1 from by ring,
        show (3 * n + 2 : ℕ) = (3 * n + 1) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 4: Interleave (2n+1) rounds
  have h4 : ⟨3, 6 * n + 3, 1, 2, 3 * n + 1⟩ [fm]⊢* ⟨3, 0, 4 * n + 3, 6 * n + 5, n⟩ := by
    have := interleave (2 * n + 1) 0 1 2 n
    simp only [Nat.zero_add] at this
    rw [show 3 * (2 * n + 1) = 6 * n + 3 from by ring,
        show n + (2 * n + 1) = 3 * n + 1 from by ring,
        show 1 + 2 * (2 * n + 1) = 4 * n + 3 from by ring,
        show 2 + (6 * n + 3) = 6 * n + 5 from by ring] at this
    exact this
  -- Phase 5: R2 x n
  have h5 : ⟨3, 0, 4 * n + 3, 6 * n + 5, n⟩ [fm]⊢* ⟨3 * n + 3, 0, 3 * n + 3, 6 * n + 5, 0⟩ := by
    have := r2_chain n 3 (3 * n + 3) (d := 6 * n + 5) 0
    simp only [Nat.zero_add] at this
    rw [show 3 * n + 3 + n = 4 * n + 3 from by ring,
        show 3 + 3 * n = 3 * n + 3 from by ring] at this
    exact this
  -- Phase 6: R3/R2 x (3n+3)
  have h6 : ⟨3 * n + 3, 0, 3 * n + 3, 6 * n + 5, 0⟩ [fm]⊢* ⟨9 * n + 9, 0, 0, 9 * n + 8, 0⟩ := by
    have := r3r2_chain (3 * n + 3) (3 * n + 2) 0 (6 * n + 5)
    simp only [Nat.zero_add] at this
    rw [show 3 * n + 2 + 1 = 3 * n + 3 from by ring,
        show 3 * n + 2 + 1 + 2 * (3 * n + 3) = 9 * n + 9 from by ring,
        show 6 * n + 5 + (3 * n + 3) = 9 * n + 8 from by ring] at this
    exact this
  -- Compose
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus h3
        (stepStar_trans (stepStar_trans h4 h5) h6)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 2, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3 * n + 3, 0, 0, 3 * n + 2, 0⟩) 0
  intro n; exact ⟨3 * n + 2, by
    show ⟨3 * n + 3, 0, 0, 3 * n + 2, 0⟩ [fm]⊢⁺ ⟨3 * (3 * n + 2) + 3, 0, 0, 3 * (3 * n + 2) + 2, 0⟩
    rw [show 3 * (3 * n + 2) + 3 = 9 * n + 9 from by ring,
        show 3 * (3 * n + 2) + 2 = 9 * n + 8 from by ring]
    exact main_transition n⟩
