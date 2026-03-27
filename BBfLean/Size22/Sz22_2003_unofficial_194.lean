import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #194: [1/6, 225/77, 7/3, 2/35, 363/2]

Vector representation:
```
-1 -1  0  0  0
 0  2  2 -1 -1
 0 -1  0  1  0
 1  0 -1 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_194

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c+2, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- drain b to d (rule 3), with a=0, e=0
theorem b_drain : ∀ k, ∀ c d, ⟨0, k, c, d, 0⟩ [fm]⊢* ⟨0, 0, c, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  rw [show d + (k + 1) = (d + 1) + k from by ring]
  step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- drain c and d to a (rule 4), with b=0, e=0
theorem cd_to_a : ∀ k, ∀ a c d, ⟨a, 0, c+k, d+k, 0⟩ [fm]⊢* ⟨a+k, 0, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

-- drain a by 2 via (rule 5, rule 1) pair
theorem a_drain_step2 : ∀ k, ∀ a c e, ⟨a+2*k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + 2 * (k + 1) = (a + 2 * k) + 1 + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih a c (e + 2)); ring_nf; finish

-- bounce: (rule2, rule3) pairs
theorem bounce_pair : ∀ k, ∀ b c e,
    ⟨0, b, c, 1, e+k⟩ [fm]⊢* ⟨0, b+k, c+2*k, 1, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih (b + 1) (c + 2) e); ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 2*n+1, (n+1)^2, 0, 0⟩ [fm]⊢⁺ ⟨0, 2*n+3, (n+2)^2, 0, 0⟩ := by
  -- Phase 1: drain b to d
  apply stepStar_stepPlus_stepPlus
  · have h := b_drain (2*n+1) ((n+1)^2) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: cd_to_a
  apply stepStar_stepPlus_stepPlus
  · have h := cd_to_a (2*n+1) 0 (n^2) 0
    simp only [Nat.zero_add, show n^2 + (2*n+1) = (n+1)^2 from by ring] at h; exact h
  -- Phase 3: drain a by 2s: (2n+1, 0, n^2, 0, 0) ⊢* (1, 0, n^2, 0, 2n)
  apply stepStar_stepPlus_stepPlus
  · have h := a_drain_step2 n 1 (n^2) 0
    simp only [Nat.zero_add, show 1 + 2*n = 2*n+1 from by ring] at h; exact h
  -- (1, 0, n^2, 0, 2*n) ⊢ (0, 1, n^2, 0, 2*n+2) via rule 5
  step fm
  -- (0, 1, n^2, 0, 2*n+2) ⊢ (0, 0, n^2, 1, 2*n+2) via rule 3
  step fm
  -- bounce: (0, 0, n^2, 1, 2*n+2) = (0, 0, n^2, 1, 1 + (2*n+1))
  -- ⊢* (0, 2*n+1, n^2+2*(2*n+1), 1, 1)
  apply stepStar_trans
  · have h := bounce_pair (2*n+1) 0 (n^2) 1
    simp only [Nat.zero_add, show 1 + (2*n+1) = 2*n+2 from by ring] at h; exact h
  -- final rule 2: (0, 2*n+1, n^2+2*(2*n+1), 1, 1) ⊢ (0, 2*n+3, (n+2)^2, 0, 0)
  -- rule 2 adds 2 to b and 2 to c
  -- After step fm we get (0, 2*n+1+2, n^2+2*(2*n+1)+2, 0, 0)
  -- Need to show 2*n+1+2 = 2*n+3 and n^2+2*(2*n+1)+2 = (n+2)^2
  step fm
  show ⟨0, 2*n+1+2, n^2+2*(2*n+1)+2, 0, 0⟩ [fm]⊢* ⟨0, 2*n+3, (n+2)^2, 0, 0⟩
  have h1 : 2*n+1+2 = 2*n+3 := by ring
  have h2 : n^2+2*(2*n+1)+2 = (n+2)^2 := by ring
  rw [h1, h2]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2*1+1, (1+1)^2, 0, 0⟩)
  · show c₀ [fm]⊢* ⟨0, 3, 4, 0, 0⟩
    execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2*n+1, (n+1)^2, 0, 0⟩) 1
  intro n
  exact ⟨n+1, main_trans n⟩

end Sz22_2003_unofficial_194
