import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1759: [9/10, 22/21, 2401/2, 5/11, 3/7]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  1
-1  0  0  4  0
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1759

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+4, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 4 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 4))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ c e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a b d e, ⟨a, b + k, 0, d + k, e⟩ [fm]⊢* ⟨a + k, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b d (e + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ b c d e, ⟨0, b + 2, c + k, d + k + 2, e⟩ [fm]⊢*
    ⟨0, b + k + 2, c, d + 2, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = c + k + 1 from by ring,
        show d + (k + 1) + 2 = d + k + 2 + 1 from by ring]
    step fm
    step fm
    rw [show b + 2 + 1 = (b + 1) + 2 from by ring]
    apply stepStar_trans (ih (b + 1) c d (e + 1))
    ring_nf; finish

theorem main_trans : ⟨n + 1, 0, 0, 2, 2 * n + 1⟩ [fm]⊢⁺ ⟨2 * n + 2, 0, 0, 2, 4 * n + 3⟩ := by
  have ph1 : ⟨n + 1, 0, 0, 2, 2 * n + 1⟩ [fm]⊢* ⟨0, 0, 0, 4 * n + 6, 2 * n + 1⟩ := by
    rw [show n + 1 = 0 + (n + 1) from by ring,
        show 4 * n + 6 = 2 + 4 * (n + 1) from by ring]
    exact r3_chain (n + 1) 0 2
  have ph2 : ⟨0, 0, 0, 4 * n + 6, 2 * n + 1⟩ [fm]⊢* ⟨0, 0, 2 * n + 1, 4 * n + 6, 0⟩ := by
    rw [show (2 * n + 1 : ℕ) = 0 + (2 * n + 1) from by ring]
    exact r4_chain (2 * n + 1) 0 0
  have ph3a : ⟨0, 0, 2 * n + 1, 4 * n + 6, 0⟩ [fm]⊢⁺ ⟨0, 2, 2 * n, 4 * n + 4, 1⟩ := by
    step fm; step fm; step fm; finish
  have ph3b : ⟨0, 2, 2 * n, 4 * n + 4, 1⟩ [fm]⊢* ⟨0, 2 * n + 2, 0, 2 * n + 4, 2 * n + 1⟩ := by
    have h := r2r1_chain (2 * n) 0 0 (2 * n + 2) 1
    -- h : (0, 0+2, 0+2*n, (2*n+2)+2*n+2, 1) →* (0, 0+2*n+2, 0, (2*n+2)+2, 1+2*n)
    -- Normalize h's type to match our goal
    simp only [Nat.zero_add] at h
    rw [show 2 * n + 2 + 2 * n + 2 = 4 * n + 4 from by omega,
        show 2 * n + 2 + 2 = 2 * n + 4 from by omega,
        show 1 + 2 * n = 2 * n + 1 from by omega] at h
    exact h
  have ph4 : ⟨0, 2 * n + 2, 0, 2 * n + 4, 2 * n + 1⟩ [fm]⊢* ⟨2 * n + 2, 0, 0, 2, 4 * n + 3⟩ := by
    have h := r2_chain (2 * n + 2) 0 0 2 (2 * n + 1)
    simp only [Nat.zero_add] at h
    rw [show 2 + (2 * n + 2) = 2 * n + 4 from by omega,
        show 2 * n + 1 + (2 * n + 2) = 4 * n + 3 from by omega] at h
    exact h
  exact stepStar_stepPlus_stepPlus (stepStar_trans ph1 ph2)
    (stepPlus_stepStar_stepPlus ph3a (stepStar_trans ph3b ph4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 2, 2 * n + 1⟩) 0
  intro n; exists 2 * n + 1
  have h := @main_trans n
  -- h : (n+1, 0, 0, 2, 2*n+1) ⊢⁺ (2*n+2, 0, 0, 2, 4*n+3)
  -- goal: (n+1, 0, 0, 2, 2*n+1) ⊢⁺ (2*n+1+1, 0, 0, 2, 2*(2*n+1)+1)
  rw [show 2 * n + 1 + 1 = 2 * n + 2 from by omega,
      show 2 * (2 * n + 1) + 1 = 4 * n + 3 from by omega]
  exact h

end Sz22_2003_unofficial_1759
