import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1913: [9/385, 50/7, 7/15, 11/2, 21/11]

Vector representation:
```
 0  2 -1 -1 -1
 1  0  2 -1  0
 0 -1 -1  1  0
-1  0  0  0  1
 0  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1913

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a c (e + 1))
    ring_nf; finish

-- R4+R5+R1 combined: (a+2, 0, c+2, 0, 0) →* (0, 3, c+1, 0, a)
theorem r4_r5_r1 : ⟨a + 2, 0, c + 2, 0, 0⟩ [fm]⊢* ⟨0, 3, c + 1, 0, a⟩ := by
  rw [show a + 2 = 0 + (a + 2) from by ring]
  apply stepStar_trans (r4_chain (a + 2) 0 (c + 2) 0)
  rw [show 0 + (a + 2) = (a + 1) + 1 from by ring]
  step fm
  -- state: (0, 1, c+1+1, 1, a+1) ⊢* (0, 3, c+1, 0, a)
  -- R1 fires: c+1+1 = (c+1)+1 matches c'+1, 1 = 0+1 matches d'+1, a+1 matches e'+1
  rw [show c + 1 + 1 = (c + 1) + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  finish

theorem r3r1_chain : ∀ k, ∀ b c e, ⟨0, b + 1, c + 2 * k, 0, e + k⟩ [fm]⊢*
    ⟨0, b + k + 1, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 1) c e)
    ring_nf; finish

theorem subloop : ∀ k, ∀ b, ⟨0, b + 1, 0, 1, k⟩ [fm]⊢* ⟨1, b + 2 * k + 1, 2, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · step fm; finish
  · step fm; step fm; step fm; step fm; step fm
    rw [show b + 2 + 1 = (b + 2) + 1 from by ring]
    apply stepStar_trans (ih (b + 2))
    ring_nf; finish

theorem r3r2_chain : ∀ k, ∀ a b c, ⟨a, b + k + 1, c + 1, 0, 0⟩ [fm]⊢*
    ⟨a + k + 1, b, c + k + 2, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · step fm; step fm; finish
  · rw [show b + (k + 1) + 1 = (b + k + 1) + 1 from by ring]
    step fm; step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) b (c + 1))
    ring_nf; finish

-- Remaining phases after r4_r5_r1: (0, 3, C, 0, E) →⁺ canonical
-- For odd: C = 2m+5, E = 2m+3
-- R3/R1 chain → R3 → subloop → R3/R2 chain
theorem phases_odd (m : ℕ) : ⟨0, 3, 2 * m + 5, 0, 2 * m + 3⟩ [fm]⊢⁺
    ⟨3 * m + 7, 0, 3 * m + 8, 0, 0⟩ := by
  show ⟨0, 2 + 1, 2 * m + 5, 0, 2 * m + 3⟩ [fm]⊢⁺ _
  rw [show 2 * m + 5 = 1 + 2 * (m + 2) from by ring,
      show 2 * m + 3 = (m + 1) + (m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r3r1_chain (m + 2) 2 1 (m + 1))
  rw [show 2 + (m + 2) + 1 = (m + 4) + 1 from by ring]
  -- R3: (0, (m+4)+1, 1, 0, m+1) → (0, m+4, 0, 1, m+1)
  step fm
  rw [show m + 4 = (m + 3) + 1 from by ring]
  apply stepStar_trans (subloop (m + 1) (m + 3))
  rw [show m + 3 + 2 * (m + 1) + 1 = 3 * m + 6 from by ring]
  show ⟨1, 3 * m + 6, 2, 0, 0⟩ [fm]⊢* _
  rw [show 3 * m + 6 = 0 + (3 * m + 5) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (3 * m + 5) 1 0 1)
  ring_nf; finish

-- For even: C = 2m+6, E = 2m+4
-- R3/R1 chain → R5 → subloop → R3/R2 chain
theorem phases_even (m : ℕ) : ⟨0, 3, 2 * m + 6, 0, 2 * m + 4⟩ [fm]⊢⁺
    ⟨3 * m + 8, 0, 3 * m + 9, 0, 0⟩ := by
  show ⟨0, 2 + 1, 2 * m + 6, 0, 2 * m + 4⟩ [fm]⊢⁺ _
  rw [show 2 * m + 6 = 0 + 2 * (m + 3) from by ring,
      show 2 * m + 4 = (m + 1) + (m + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (r3r1_chain (m + 3) 2 0 (m + 1))
  rw [show 2 + (m + 3) + 1 = m + 6 from by ring]
  -- (0, m+6, 0, 0, m+1). R5 fires since m+1 matches e+1
  step fm
  -- (0, m+6+1, 0, 0+1, m) = (0, m+7, 0, 1, m)
  rw [show m + 6 + 1 = (m + 6) + 1 from by ring]
  apply stepStar_trans (subloop m (m + 6))
  rw [show m + 6 + 2 * m + 1 = 3 * m + 7 from by ring]
  show ⟨1, 3 * m + 7, 2, 0, 0⟩ [fm]⊢* _
  rw [show 3 * m + 7 = 0 + (3 * m + 6) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (3 * m + 6) 1 0 1)
  ring_nf; finish

theorem odd_trans (m : ℕ) : ⟨2 * m + 5, 0, 2 * m + 6, 0, 0⟩ [fm]⊢⁺
    ⟨3 * m + 7, 0, 3 * m + 8, 0, 0⟩ := by
  rw [show 2 * m + 5 = (2 * m + 3) + 2 from by ring,
      show 2 * m + 6 = (2 * m + 4) + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_r5_r1 (a := 2 * m + 3) (c := 2 * m + 4))
  rw [show 2 * m + 4 + 1 = 2 * m + 5 from by ring]
  exact phases_odd m

theorem even_trans (m : ℕ) : ⟨2 * m + 6, 0, 2 * m + 7, 0, 0⟩ [fm]⊢⁺
    ⟨3 * m + 8, 0, 3 * m + 9, 0, 0⟩ := by
  rw [show 2 * m + 6 = (2 * m + 4) + 2 from by ring,
      show 2 * m + 7 = (2 * m + 5) + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_r5_r1 (a := 2 * m + 4) (c := 2 * m + 5))
  rw [show 2 * m + 5 + 1 = 2 * m + 6 from by ring]
  exact phases_even m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 6, 0, 0⟩) (by execute fm 50)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 5, 0, n + 6, 0, 0⟩) 0
  intro n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    refine ⟨3 * k + 2, ?_⟩
    show ⟨k + k + 5, 0, k + k + 6, 0, 0⟩ [fm]⊢⁺ ⟨3 * k + 2 + 5, 0, 3 * k + 2 + 6, 0, 0⟩
    rw [show k + k + 5 = 2 * k + 5 from by ring,
        show k + k + 6 = 2 * k + 6 from by ring,
        show 3 * k + 2 + 5 = 3 * k + 7 from by ring,
        show 3 * k + 2 + 6 = 3 * k + 8 from by ring]
    exact odd_trans k
  · subst hk
    refine ⟨3 * k + 3, ?_⟩
    show ⟨2 * k + 1 + 5, 0, 2 * k + 1 + 6, 0, 0⟩ [fm]⊢⁺ ⟨3 * k + 3 + 5, 0, 3 * k + 3 + 6, 0, 0⟩
    rw [show 2 * k + 1 + 5 = 2 * k + 6 from by ring,
        show 2 * k + 1 + 6 = 2 * k + 7 from by ring,
        show 3 * k + 3 + 5 = 3 * k + 8 from by ring,
        show 3 * k + 3 + 6 = 3 * k + 9 from by ring]
    exact even_trans k
