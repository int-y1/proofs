import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1827: [9/10, 55/21, 484/3, 7/11, 3/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  2
 0  0  0  1 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1827

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (d + 1)); ring_nf; finish

theorem r2r1_loop : ∀ k, ∀ b d e, ⟨k, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm; step fm
    rw [show (b + 2 : ℕ) = (b + 1) + 1 from by ring]
    have h := ih (b + 1) d (e + 1)
    rw [show b + 1 + k + 1 = b + (k + 1) + 1 from by ring,
        show e + 1 + k = e + (k + 1) from by ring] at h
    exact h

theorem r2_drain : ∀ k, ∀ b c d e, ⟨0, b + k, c, d + k, e⟩ [fm]⊢* ⟨0, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    have h := ih b (c + 1) d (e + 1)
    rw [show c + 1 + k = c + (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring] at h
    exact h

theorem r3_chain : ∀ k, ∀ a b e, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]; step fm
    have h := ih (a + 2) b (e + 2)
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring,
        show e + 2 + 2 * k = e + 2 * (k + 1) from by ring] at h
    exact h

theorem spiral_gen : ∀ M, ∀ b e, ⟨2, b, M + 1, 0, e⟩ [fm]⊢* ⟨3 * M + 2 * b + 5, 0, 0, 0, e + 4 * M + 2 * b + 4⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih
  intro b e
  rcases M with _ | _ | M
  · step fm
    have h := r3_chain (b + 2) 1 0 e
    rw [show (0 : ℕ) + (b + 2) = b + 2 from by ring,
        show 1 + 2 * (b + 2) = 3 * 0 + 2 * b + 5 from by ring,
        show e + 2 * (b + 2) = e + 4 * 0 + 2 * b + 4 from by ring] at h
    exact h
  · step fm; step fm; step fm
    have h := r3_chain (b + 3) 2 0 (e + 2)
    rw [show (0 : ℕ) + (b + 3) = b + 3 from by ring,
        show 2 + 2 * (b + 3) = 3 * 1 + 2 * b + 5 from by ring,
        show e + 2 + 2 * (b + 3) = e + 4 * 1 + 2 * b + 4 from by ring] at h
    exact h
  · step fm; step fm; step fm
    have h := ih M (by omega) (b + 3) (e + 2)
    rw [show 3 * M + 2 * (b + 3) + 5 = 3 * (M + 2) + 2 * b + 5 from by ring,
        show e + 2 + 4 * M + 2 * (b + 3) + 4 = e + 4 * (M + 2) + 2 * b + 4 from by ring] at h
    exact h

theorem main_trans (n : ℕ) : ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨3 * n + 5, 0, 0, 0, 6 * n + 8⟩ := by
  have h1 : ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢* ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ := by
    have h := e_to_d (2 * n + 2) 0 (a := n + 2) (e := 0)
    rw [show (0 : ℕ) + (2 * n + 2) = 2 * n + 2 from by ring] at h; exact h
  have h3 : ⟨n + 1, 1, 0, 2 * n + 2, 0⟩ [fm]⊢* ⟨0, n + 2, 0, n + 1, n + 1⟩ := by
    have h := r2r1_loop (n + 1) 0 (n + 1) 0
    rw [show (0 : ℕ) + 1 = 1 from by ring,
        show (n + 1 : ℕ) + (n + 1) = 2 * n + 2 from by ring,
        show 0 + (n + 1) + 1 = n + 2 from by ring,
        show (0 : ℕ) + (n + 1) = n + 1 from by ring] at h; exact h
  have h4 : ⟨0, n + 2, 0, n + 1, n + 1⟩ [fm]⊢* ⟨0, 1, n + 1, 0, 2 * n + 2⟩ := by
    have h := r2_drain (n + 1) 1 0 0 (n + 1)
    rw [show 1 + (n + 1) = n + 2 from by ring,
        show (0 : ℕ) + (n + 1) = n + 1 from by ring,
        show (n + 1 : ℕ) + (n + 1) = 2 * n + 2 from by ring] at h; exact h
  have h6 : ⟨2, 0, n + 1, 0, 2 * n + 4⟩ [fm]⊢* ⟨3 * n + 5, 0, 0, 0, 6 * n + 8⟩ := by
    have h := spiral_gen n 0 (2 * n + 4)
    rw [show 3 * n + 2 * 0 + 5 = 3 * n + 5 from by ring,
        show 2 * n + 4 + 4 * n + 2 * 0 + 4 = 6 * n + 8 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus h1
  have hr5 : ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢ ⟨n + 1, 1, 0, 2 * n + 2, 0⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]; rfl
  apply step_stepStar_stepPlus hr5
  apply stepStar_trans h3
  apply stepStar_trans h4
  have hr3 : ⟨0, 1, n + 1, 0, 2 * n + 2⟩ [fm]⊢ ⟨2, 0, n + 1, 0, 2 * n + 4⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring]; rfl
  exact stepPlus_stepStar (step_stepStar_stepPlus hr3 h6)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by unfold c₀; execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * n + 2⟩) 0
  intro n
  refine ⟨3 * n + 3, ?_⟩
  show ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨3 * n + 3 + 2, 0, 0, 0, 2 * (3 * n + 3) + 2⟩
  rw [show 3 * n + 3 + 2 = 3 * n + 5 from by ring,
      show 2 * (3 * n + 3) + 2 = 6 * n + 8 from by ring]
  exact main_trans n
