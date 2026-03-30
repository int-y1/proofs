import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #832: [35/6, 8/55, 847/2, 3/7, 5/11]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_832

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem d_to_b : ∀ k b d, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b + 1) d); ring_nf; finish

theorem r3_drain : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm; apply stepStar_trans (ih (d + 1) (e + 2)); ring_nf; finish

theorem r2_drain : ∀ k a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 3) d e); ring_nf; finish

theorem one_round : ∀ b c d, ⟨3, b + 3, c, d, e + 1⟩ [fm]⊢* ⟨3, b, c + 2, d + 3, e⟩ := by
  intro b c d; step fm; step fm; step fm; step fm; ring_nf; finish

theorem rounds : ∀ k b c d e, ⟨3, b + 3 * k, c, d, e + k⟩ [fm]⊢* ⟨3, b, c + 2 * k, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 3) c d (e + 1))
    apply stepStar_trans (one_round b (c + 2 * k) (d + 3 * k) (e := e)); ring_nf; finish

-- (0, 0, 0, d, e+2) →* (3, d, 0, 0, e)
theorem opening (d : ℕ) : ⟨0, 0, 0, d, e + 2⟩ [fm]⊢* ⟨3, d, 0, 0, e⟩ := by
  apply stepStar_trans
  · rw [show (d : ℕ) = 0 + d from by ring]
    exact d_to_b d 0 0
  rw [show (0 + d : ℕ) = d from by ring, show e + 2 = e + 1 + 1 from by ring]
  step fm; step fm; ring_nf; finish

-- (0, 0, 0, 3*n+3, e+3*n+5) →⁺ (0, 0, 0, 9*n+12, e+12*n+18)
theorem transition (n e : ℕ) :
    ⟨0, 0, 0, 3 * n + 3, e + 3 * n + 5⟩ [fm]⊢⁺
    ⟨0, 0, 0, 9 * n + 12, e + 12 * n + 18⟩ := by
  -- Opening: →* (3, 3*n+3, 0, 0, e+3*n+3)
  rw [show e + 3 * n + 5 = (e + 3 * n + 3) + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (opening (3 * n + 3) (e := e + 3 * n + 3))
  -- Rounds (n+1 rounds)
  rw [show 3 * n + 3 = 0 + 3 * (n + 1) from by ring,
      show e + 3 * n + 3 = e + 2 * n + 2 + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (rounds (n + 1) 0 0 0 (e + 2 * n + 2))
  -- R2 drain: (3, 0, 0+2*(n+1), 0+3*(n+1), e+2*n+2) →* (6*n+9, 0, 0, 3*n+3, e)
  rw [show (0 + 2 * (n + 1) : ℕ) = 2 * n + 2 from by ring,
      show (0 + 3 * (n + 1) : ℕ) = 3 * n + 3 from by ring,
      show e + 2 * n + 2 = e + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r2_drain (2 * n + 2) 3 (3 * n + 3) e)
  -- R3 drain: (6*n+9, 0, 0, 3*n+3, e) →⁺ (0, 0, 0, 9*n+12, e+12*n+18)
  rw [show 3 + 3 * (2 * n + 2) = 6 * n + 9 from by ring]
  have h := r3_drain (6 * n + 9) (3 * n + 3) e
  rw [show 3 * n + 3 + (6 * n + 9) = 9 * n + 12 from by ring,
      show e + 2 * (6 * n + 9) = e + 12 * n + 18 from by ring] at h
  exact stepStar_stepPlus h (by simp only [Q, ne_eq, Prod.mk.injEq]; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 6, 9⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n e, q = ⟨0, 0, 0, 3 * n + 3, e + 3 * n + 5⟩)
  · intro c ⟨n, e, hq⟩; subst hq
    exact ⟨⟨0, 0, 0, 9 * n + 12, e + 12 * n + 18⟩,
      ⟨3 * n + 3, e + 3 * n + 4, by ring_nf⟩,
      transition n e⟩
  · exact ⟨1, 1, by ring_nf⟩
