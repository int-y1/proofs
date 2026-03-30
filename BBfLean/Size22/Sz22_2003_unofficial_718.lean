import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #718: [35/6, 4/55, 1331/2, 3/7, 35/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  3
 0  1  0 -1  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_718

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 3))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem r2r1r1_cycle : ∀ k, ∀ c d e, ⟨0, 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem r2r1r1_odd : ∀ k, ∀ c d e, ⟨0, 2 * k + 1, c + 1, d, e + k + 1⟩ [fm]⊢* ⟨1, 0, c + k + 1, d + 2 * k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

-- Even case: after first R3 step we have (2k+1, 0, 0, 2k+1, (2k+1)^2+3)
-- The issue is that after step fm from (2k+2, ...), we get expressions with Nat.add
-- which don't match our lemma signatures. So we use show/suffices to reset.
theorem main_even_star (k : ℕ) :
    ⟨2 * k + 1, 0, 0, 2 * k + 1, (2 * k + 1) * (2 * k + 1) + 3⟩ [fm]⊢*
    ⟨2 * k + 3, 0, 0, 2 * k + 2, (2 * k + 2) * (2 * k + 2)⟩ := by
  -- R3 chain (2k+1 steps)
  have h1 := r3_chain (2 * k + 1) 0 (2 * k + 1) ((2 * k + 1) * (2 * k + 1) + 3)
  rw [show 0 + (2 * k + 1) = 2 * k + 1 from by ring,
      show (2 * k + 1) * (2 * k + 1) + 3 + 3 * (2 * k + 1) = 4 * k * k + 10 * k + 7 from by ring] at h1
  apply stepStar_trans h1
  -- R4 chain (2k+1 steps)
  have h2 := r4_chain (2 * k + 1) 0 (4 * k * k + 10 * k + 7)
  rw [show 0 + (2 * k + 1) = 2 * k + 1 from by ring] at h2
  apply stepStar_trans h2
  -- R5 step
  rw [show 4 * k * k + 10 * k + 7 = (4 * k * k + 10 * k + 6) + 1 from by ring]
  step fm
  -- r2r1r1_odd (k)
  have h3 := r2r1r1_odd k 0 1 (4 * k * k + 9 * k + 5)
  rw [show 0 + k + 1 = k + 1 from by ring,
      show 1 + 2 * k + 1 = 2 * k + 2 from by ring] at h3
  rw [show 4 * k * k + 10 * k + 6 = (4 * k * k + 9 * k + 5) + k + 1 from by ring]
  apply stepStar_trans h3
  -- R2 chain (k+1)
  rw [show (2 * k + 2) * (2 * k + 2) = 4 * k * k + 8 * k + 4 from by ring]
  have h4 := r2_chain (k + 1) 1 0 (2 * k + 2) (4 * k * k + 8 * k + 4)
  rw [show 0 + (k + 1) = k + 1 from by ring,
      show (4 * k * k + 8 * k + 4) + (k + 1) = 4 * k * k + 9 * k + 5 from by ring,
      show 1 + 2 * (k + 1) = 2 * k + 3 from by ring] at h4
  exact h4

theorem main_even (k : ℕ) :
    ⟨2 * k + 2, 0, 0, 2 * k + 1, (2 * k + 1) * (2 * k + 1)⟩ [fm]⊢⁺
    ⟨2 * k + 3, 0, 0, 2 * k + 2, (2 * k + 2) * (2 * k + 2)⟩ := by
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm
  exact main_even_star k

theorem main_odd_star (k : ℕ) :
    ⟨2 * k + 2, 0, 0, 2 * k + 2, (2 * k + 2) * (2 * k + 2) + 3⟩ [fm]⊢*
    ⟨2 * k + 4, 0, 0, 2 * k + 3, (2 * k + 3) * (2 * k + 3)⟩ := by
  have h1 := r3_chain (2 * k + 2) 0 (2 * k + 2) ((2 * k + 2) * (2 * k + 2) + 3)
  rw [show 0 + (2 * k + 2) = 2 * k + 2 from by ring,
      show (2 * k + 2) * (2 * k + 2) + 3 + 3 * (2 * k + 2) = 4 * k * k + 14 * k + 13 from by ring] at h1
  apply stepStar_trans h1
  have h2 := r4_chain (2 * k + 2) 0 (4 * k * k + 14 * k + 13)
  rw [show 0 + (2 * k + 2) = 2 * k + 2 from by ring] at h2
  apply stepStar_trans h2
  rw [show 4 * k * k + 14 * k + 13 = (4 * k * k + 14 * k + 12) + 1 from by ring]
  step fm
  have h3 := r2r1r1_cycle (k + 1) 0 1 (4 * k * k + 13 * k + 11)
  rw [show 0 + (k + 1) + 1 = k + 2 from by ring,
      show 1 + 2 * (k + 1) = 2 * k + 3 from by ring] at h3
  rw [show 4 * k * k + 14 * k + 12 = (4 * k * k + 13 * k + 11) + (k + 1) from by ring,
      show 2 * k + 2 = 2 * (k + 1) from by ring]
  apply stepStar_trans h3
  rw [show (2 * k + 3) * (2 * k + 3) = 4 * k * k + 12 * k + 9 from by ring]
  have h4 := r2_chain (k + 2) 0 0 (2 * k + 3) (4 * k * k + 12 * k + 9)
  rw [show 0 + (k + 2) = k + 2 from by ring,
      show (4 * k * k + 12 * k + 9) + (k + 2) = 4 * k * k + 13 * k + 11 from by ring,
      show 0 + 2 * (k + 2) = 2 * k + 4 from by ring] at h4
  exact h4

theorem main_odd (k : ℕ) :
    ⟨2 * k + 3, 0, 0, 2 * k + 2, (2 * k + 2) * (2 * k + 2)⟩ [fm]⊢⁺
    ⟨2 * k + 4, 0, 0, 2 * k + 3, (2 * k + 3) * (2 * k + 3)⟩ := by
  rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring]
  step fm
  exact main_odd_star k

theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, n + 1, (n + 1) * (n + 1)⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, n + 2, (n + 2) * (n + 2)⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    exact main_even k
  · subst hk
    rw [show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
        show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
        show 2 * k + 1 + 3 = 2 * k + 4 from by ring,
        show (2 * k + 1 + 1) * (2 * k + 1 + 1) = (2 * k + 2) * (2 * k + 2) from by ring,
        show (2 * k + 1 + 2) * (2 * k + 1 + 2) = (2 * k + 3) * (2 * k + 3) from by ring]
    exact main_odd k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 1, (n + 1) * (n + 1)⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_718
