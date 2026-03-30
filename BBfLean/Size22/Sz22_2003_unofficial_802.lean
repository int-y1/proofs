import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #802: [35/6, 605/2, 4/77, 3/5, 7/33]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 0 -1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_802

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

theorem c_to_b : ∀ k b c e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c e)
    ring_nf; finish

theorem r3r2r2_chain : ∀ k c d e, ⟨0, 0, c, d + k, e + 1⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e + 3 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 2) d (e + 3))
    ring_nf; finish

theorem interleaved_even : ∀ n c d f,
    ⟨0, 2 * n, c, d + 1, n + f + 1⟩ [fm]⊢* ⟨0, 0, c + 2 * n, d + n + 1, f + 1⟩ := by
  intro n; induction' n with n ih <;> intro c d f
  · simp; exists 0
  · rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring,
        show (n + 1) + f + 1 = (n + f + 1) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 2) (d + 1) f)
    ring_nf; finish

theorem interleaved_odd : ∀ n c d f,
    ⟨0, 2 * n + 1, c, d + 1, n + f + 1⟩ [fm]⊢* ⟨0, 0, c + 2 * n + 2, d + n + 1, f + 2⟩ := by
  intro n; induction' n with n ih <;> intro c d f
  · simp
    step fm
    step fm
    step fm
    finish
  · rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 from by ring,
        show (n + 1) + f + 1 = (n + f + 1) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 2) (d + 1) f)
    ring_nf; finish

theorem middle_b0 (k : ℕ) : ⟨2, 0, 0, 0, k⟩ [fm]⊢* ⟨0, 2, 0, 0, k + 4⟩ := by
  step fm; step fm
  exact c_to_b 2 0 0 (k + 4)

theorem middle_b1 (k : ℕ) : ⟨2, 1, 0, 0, k + 1⟩ [fm]⊢* ⟨0, 4, 0, 0, k + 6⟩ := by
  step fm
  step fm
  show ⟨0, 0, 2, 0 + 1, (k + 2) + 1⟩ [fm]⊢* ⟨0, 4, 0, 0, k + 6⟩
  apply stepStar_trans (r3r2r2_chain 1 2 0 (k + 2))
  show ⟨0, 0, 2 + 2 * 1, 0, k + 2 + 3 * 1 + 1⟩ [fm]⊢* ⟨0, 4, 0, 0, k + 6⟩
  rw [show 2 + 2 * 1 = 4 from by ring, show k + 2 + 3 * 1 + 1 = k + 6 from by ring]
  exact c_to_b 4 0 0 (k + 6)

theorem middle_even (n f : ℕ) :
    ⟨2, 2 * n + 2, 0, 0, n + f + 2⟩ [fm]⊢* ⟨0, 4 * n + 6, 0, 0, 3 * n + f + 8⟩ := by
  step fm
  step fm
  rw [show n + f + 2 = n + (f + 1) + 1 from by ring]
  apply stepStar_trans (interleaved_even n 2 1 (f + 1))
  rw [show 1 + n + 1 = 0 + (n + 2) from by ring]
  apply stepStar_trans (r3r2r2_chain (n + 2) (2 + 2 * n) 0 (f + 1))
  show ⟨0, 0, 2 + 2 * n + 2 * (n + 2), 0, f + 1 + 3 * (n + 2) + 1⟩ [fm]⊢* _
  rw [show 2 + 2 * n + 2 * (n + 2) = 4 * n + 6 from by ring,
      show f + 1 + 3 * (n + 2) + 1 = 3 * n + f + 8 from by ring]
  rw [show (4 * n + 6 : ℕ) = 0 + (4 * n + 6) from by ring]
  exact c_to_b (4 * n + 6) 0 0 (3 * n + f + 8)

theorem middle_odd (n f : ℕ) :
    ⟨2, 2 * n + 3, 0, 0, n + f + 2⟩ [fm]⊢* ⟨0, 4 * n + 8, 0, 0, 3 * n + f + 9⟩ := by
  step fm
  step fm
  rw [show n + f + 2 = n + (f + 1) + 1 from by ring]
  apply stepStar_trans (interleaved_odd n 2 1 (f + 1))
  rw [show 2 + 2 * n + 2 = 2 * n + 4 from by ring,
      show 1 + n + 1 = 0 + (n + 2) from by ring]
  apply stepStar_trans (r3r2r2_chain (n + 2) (2 * n + 4) 0 (f + 2))
  show ⟨0, 0, 2 * n + 4 + 2 * (n + 2), 0, f + 2 + 3 * (n + 2) + 1⟩ [fm]⊢* _
  rw [show 2 * n + 4 + 2 * (n + 2) = 4 * n + 8 from by ring,
      show f + 2 + 3 * (n + 2) + 1 = 3 * n + f + 9 from by ring]
  rw [show (4 * n + 8 : ℕ) = 0 + (4 * n + 8) from by ring]
  exact c_to_b (4 * n + 8) 0 0 (3 * n + f + 9)

theorem main_trans (b k : ℕ) :
    ⟨0, b + 1, 0, 0, b + k + 2⟩ [fm]⊢⁺ ⟨0, 2 * b + 2, 0, 0, 2 * b + k + 4⟩ := by
  step fm
  step fm
  rcases b with _ | _ | b'
  · -- b = 0
    simp only [Nat.zero_add]
    rw [show 2 * 0 + 2 = 2 from by ring, show 2 * 0 + k + 4 = k + 4 from by ring]
    exact middle_b0 k
  · -- b = 1
    rw [show (0 : ℕ) + 1 + k = k + 1 from by ring,
        show 2 * (0 + 1) + 2 = 4 from by ring,
        show 2 * (0 + 1) + k + 4 = k + 6 from by ring]
    exact middle_b1 k
  · -- b = b' + 2
    rcases Nat.even_or_odd b' with ⟨n, hn⟩ | ⟨n, hn⟩
    · -- b' = 2n, b = 2n+2
      subst hn
      -- goal: (2, n+n+1+1, 0, 0, n+n+1+1+k) ⊢* (0, 2*(n+n+1+1)+2, 0, 0, 2*(n+n+1+1)+k+4)
      rw [show n + n + 1 + 1 + k = n + (n + k) + 2 from by ring,
          show 2 * (n + n + 1 + 1) + 2 = 4 * n + 6 from by ring,
          show 2 * (n + n + 1 + 1) + k + 4 = 3 * n + (n + k) + 8 from by ring,
          show n + n + 1 + 1 = 2 * n + 2 from by ring]
      exact middle_even n (n + k)
    · -- b' = 2n+1, b = 2n+3
      subst hn
      -- goal: (2, 2*n+1+1+1, 0, 0, 2*n+1+1+1+k) ⊢* (0, 2*(2*n+1+1+1)+2, 0, 0, 2*(2*n+1+1+1)+k+4)
      rw [show 2 * n + 1 + 1 + 1 + k = n + (n + k + 1) + 2 from by ring,
          show 2 * (2 * n + 1 + 1 + 1) + 2 = 4 * n + 8 from by ring,
          show 2 * (2 * n + 1 + 1 + 1) + k + 4 = 3 * n + (n + k + 1) + 9 from by ring,
          show 2 * n + 1 + 1 + 1 = 2 * n + 3 from by ring]
      exact middle_odd n (n + k + 1)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 2⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, p.1 + 1, 0, 0, p.1 + p.2 + 2⟩) ⟨0, 0⟩
  intro ⟨b, k⟩
  refine ⟨⟨2 * b + 1, k + 1⟩, ?_⟩
  show ⟨0, b + 1, 0, 0, b + k + 2⟩ [fm]⊢⁺ ⟨0, (2 * b + 1) + 1, 0, 0, (2 * b + 1) + (k + 1) + 2⟩
  rw [show (2 * b + 1) + 1 = 2 * b + 2 from by ring,
      show (2 * b + 1) + (k + 1) + 2 = 2 * b + k + 4 from by ring]
  exact main_trans b k
