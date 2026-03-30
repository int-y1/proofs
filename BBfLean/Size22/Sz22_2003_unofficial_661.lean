import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #661: [35/6, 1573/2, 4/65, 3/7, 35/11]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  2  1
 2  0 -1  0  0 -1
 0  1  0 -1  0  0
 0  0  1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_661

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | _ => none

theorem d_to_b : ∀ k, ∀ b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

theorem d_to_b_full (n e f : ℕ) : ⟨0, 1, 0, n, e, f⟩ [fm]⊢* ⟨0, n + 1, 0, 0, e, f⟩ := by
  have h := d_to_b n 1 0 e f
  rw [Nat.zero_add, show 1 + n = n + 1 from by ring] at h
  exact h

theorem interleave : ∀ k, ∀ b c d e g, ⟨2, 2 * k + b, c, d, e, k + g⟩ [fm]⊢*
    ⟨2, b, c + k, d + 2 * k, e, g⟩ := by
  intro k; induction' k with k ih <;> intro b c d e g
  · simp; exists 0
  · rw [show 2 * (k + 1) + b = (2 * k + b) + 1 + 1 from by ring,
        show (k + 1) + g = k + (g + 1) from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 = d + 2 from by ring]
    apply stepStar_trans (ih b (c + 1) (d + 2) e g)
    ring_nf; finish

theorem interleave_odd (m e : ℕ) :
    ⟨2, 2 * m + 1, 0, 1, e, 2 * m + 1⟩ [fm]⊢*
    ⟨2, 1, m, 2 * m + 1, e, m + 1⟩ := by
  have h := interleave m 1 0 1 e (m + 1)
  rw [show m + (m + 1) = 2 * m + 1 from by ring,
      show 0 + m = m from Nat.zero_add _,
      show 1 + 2 * m = 2 * m + 1 from by ring] at h
  exact h

theorem interleave_even (m e : ℕ) :
    ⟨2, 2 * m + 2, 0, 1, e, 2 * m + 2⟩ [fm]⊢*
    ⟨2, 0, m + 1, 2 * m + 3, e, m + 1⟩ := by
  have h := interleave (m + 1) 0 0 1 e (m + 1)
  rw [show 2 * (m + 1) + 0 = 2 * m + 2 from by ring,
      show (m + 1) + (m + 1) = 2 * m + 2 from by ring,
      show 0 + (m + 1) = m + 1 from Nat.zero_add _,
      show 1 + 2 * (m + 1) = 2 * m + 3 from by ring] at h
  exact h

theorem tail : ∀ k, ∀ c d e f, ⟨0, 0, c + k, d, e, f + 1⟩ [fm]⊢*
    ⟨0, 0, c, d, e + 4 * k, f + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + 2 + 2 = e + 4 from by ring,
        show f + 1 + 1 = (f + 1) + 1 from by ring]
    apply stepStar_trans (ih c d (e + 4) (f + 1))
    ring_nf; finish

theorem tail_full (k d e f : ℕ) :
    ⟨0, 0, k, d, e, f + 1⟩ [fm]⊢* ⟨0, 0, 0, d, e + 4 * k, f + k + 1⟩ := by
  have h := tail k 0 d e f
  rw [Nat.zero_add] at h
  exact h

theorem main_odd (m : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, (2 * m + 2) * (2 * m + 2) + 1, 2 * m + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 2, (2 * m + 3) * (2 * m + 3) + 1, 2 * m + 3⟩ := by
  step fm
  apply stepStar_trans (d_to_b_full (2 * m) _ _)
  rw [show 2 * m + 1 = 2 * m + 1 from rfl,
      show (2 * m + 2) * (2 * m + 2) + 1 = ((2 * m + 2) * (2 * m + 2)) + 1 from rfl,
      show (2 * m + 2 : ℕ) = (2 * m + 1) + 1 from by ring]
  step fm -- R5
  step fm -- R3
  apply stepStar_trans (interleave_odd m _)
  step fm -- R1
  step fm -- R2
  rw [show (m + 1 + 1 : ℕ) = (m + 1) + 1 from rfl]
  apply stepStar_trans (tail_full (m + 1) (2 * m + 2)
    ((2 * m + 2) * (2 * m + 2) + 2) (m + 1))
  ring_nf; finish

theorem main_even (m : ℕ) :
    ⟨0, 0, 0, 2 * m + 2, (2 * m + 3) * (2 * m + 3) + 1, 2 * m + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 3, (2 * m + 4) * (2 * m + 4) + 1, 2 * m + 4⟩ := by
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (d_to_b_full (2 * m + 1) _ _)
  rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
      show (2 * m + 3) * (2 * m + 3) + 1 = ((2 * m + 3) * (2 * m + 3)) + 1 from rfl,
      show (2 * m + 3 : ℕ) = (2 * m + 2) + 1 from by ring]
  step fm -- R5
  step fm -- R3
  apply stepStar_trans (interleave_even m _)
  step fm -- R2
  step fm -- R2
  rw [show (m + 1 + 1 + 1 : ℕ) = (m + 2) + 1 from by ring]
  apply stepStar_trans (tail_full (m + 1) (2 * m + 3)
    ((2 * m + 3) * (2 * m + 3) + 4) (m + 2))
  ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, n + 1, (n + 2) * (n + 2) + 1, n + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, n + 2, (n + 3) * (n + 3) + 1, n + 3⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m + 1 = 2 * m + 1 from by ring,
        show m + m + 2 = 2 * m + 2 from by ring,
        show m + m + 3 = 2 * m + 3 from by ring]
    exact main_odd m
  · subst hm
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 2 * m + 1 + 3 = 2 * m + 4 from by ring]
    exact main_even m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 5, 2⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 1, (n + 2) * (n + 2) + 1, n + 2⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
