import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1816: [9/10, 55/21, 22/3, 7/121, 15/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  1
 0  0  0  1 -2
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1816

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ d, ⟨a, 0, 0, d, e + 2 * k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm; apply stepStar_trans (ih (d + 1)); ring_nf; finish

theorem r3_chain : ∀ k, ∀ a b e, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 1) b (e + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a b d e, ⟨a + k, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨a, b + k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; rw [show a + k + 1 = (a + k) + 1 from by ring]
    step fm; rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih a (b + 1) d (e + 1)); ring_nf; finish

theorem r2_chain : ∀ k, ∀ b c d e, ⟨0, b + k, c, d + k, e⟩ [fm]⊢* ⟨0, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih b (c + 1) d (e + 1)); ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ b c e, ⟨0, b + 1, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k + 1, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; rw [show (c + k) + 1 = c + k + 1 from by ring]
    step fm; rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 1) c (e + 1)); ring_nf; finish

theorem round1 (n : ℕ) : ⟨2*n+1, 3, 0, 3*n+3, 0⟩ [fm]⊢* ⟨2*n+4, 0, 0, 0, 6*n+9⟩ := by
  have p1 : ⟨2*n+1, 3, 0, 3*n+3, (0:ℕ)⟩ [fm]⊢* ⟨0, 2*n+4, 0, n+2, 2*n+1⟩ := by
    have := r2r1_chain (2*n+1) 0 2 (n+2) 0
    simp only [Nat.zero_add] at this; convert this using 2; all_goals ring_nf
  apply stepStar_trans p1
  have p2 : ⟨0, 2*n+4, 0, n+2, 2*n+1⟩ [fm]⊢* ⟨0, n+2, n+2, 0, 3*n+3⟩ := by
    have := r2_chain (n+2) (n+2) 0 0 (2*n+1)
    simp only [Nat.zero_add] at this; convert this using 2; all_goals ring_nf
  apply stepStar_trans p2
  have p3 : ⟨0, n+2, n+2, 0, 3*n+3⟩ [fm]⊢* ⟨0, 2*n+4, 0, 0, 4*n+5⟩ := by
    have := r3r1_chain (n+2) (n+1) 0 (3*n+3)
    simp only [Nat.zero_add] at this; convert this using 2; all_goals ring_nf
  apply stepStar_trans p3
  have p4 : ⟨0, 2*n+4, 0, 0, 4*n+5⟩ [fm]⊢* ⟨2*n+4, 0, 0, 0, 6*n+9⟩ := by
    have := r3_chain (2*n+4) 0 0 (4*n+5)
    simp only [Nat.zero_add] at this; convert this using 2; all_goals ring_nf
  exact p4

theorem round2 (n : ℕ) : ⟨2*n+2, 3, 0, 3*n+4, 1⟩ [fm]⊢* ⟨2*n+5, 0, 0, 0, 6*n+12⟩ := by
  have p1 : ⟨2*n+2, 3, 0, 3*n+4, (1:ℕ)⟩ [fm]⊢* ⟨0, 2*n+5, 0, n+2, 2*n+3⟩ := by
    have := r2r1_chain (2*n+2) 0 2 (n+2) 1
    simp only [Nat.zero_add] at this; convert this using 2; all_goals ring_nf
  apply stepStar_trans p1
  have p2 : ⟨0, 2*n+5, 0, n+2, 2*n+3⟩ [fm]⊢* ⟨0, n+3, n+2, 0, 3*n+5⟩ := by
    have := r2_chain (n+2) (n+3) 0 0 (2*n+3)
    simp only [Nat.zero_add] at this; convert this using 2; all_goals ring_nf
  apply stepStar_trans p2
  have p3 : ⟨0, n+3, n+2, 0, 3*n+5⟩ [fm]⊢* ⟨0, 2*n+5, 0, 0, 4*n+7⟩ := by
    have := r3r1_chain (n+2) (n+2) 0 (3*n+5)
    simp only [Nat.zero_add] at this; convert this using 2; all_goals ring_nf
  apply stepStar_trans p3
  have p4 : ⟨0, 2*n+5, 0, 0, 4*n+7⟩ [fm]⊢* ⟨2*n+5, 0, 0, 0, 6*n+12⟩ := by
    have := r3_chain (2*n+5) 0 0 (4*n+7)
    simp only [Nat.zero_add] at this; convert this using 2; all_goals ring_nf
  exact p4

theorem main_trans (n : ℕ) : ⟨2*n+3, 0, 0, 3*n+3, 0⟩ [fm]⊢⁺ ⟨2*n+5, 0, 0, 3*n+6, (0 : ℕ)⟩ := by
  rw [show 2 * n + 3 = (2 * n + 1) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (round1 n)
  rw [show 6 * n + 9 = 1 + 2 * (3 * n + 4) from by ring]
  apply stepStar_trans (r4_chain (3*n+4) 0 (a := 2*n+4) (e := 1))
  rw [show 0 + (3 * n + 4) = 3 * n + 4 from by ring,
      show 2 * n + 4 = (2 * n + 2) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (round2 n)
  rw [show 6 * n + 12 = 0 + 2 * (3 * n + 6) from by ring]
  apply stepStar_trans (r4_chain (3*n+6) 0 (a := 2*n+5) (e := 0))
  rw [show 0 + (3 * n + 6) = 3 * n + 6 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 3, 0⟩) (by execute fm 17)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, 0, 3 * n + 3, 0⟩) 0
  intro n; exists n + 1
  exact main_trans n

end Sz22_2003_unofficial_1816
