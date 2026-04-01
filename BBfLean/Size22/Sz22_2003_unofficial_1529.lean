import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1529: [7/30, 18/77, 22/3, 5/11, 9/2]

Vector representation:
```
-1 -1 -1  1  0
 1  2  0 -1 -1
 1 -1  0  0  1
 0  0  1  0 -1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1529

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- Phase 1 (R4 chain): transfer e to c.
-- (a, 0, c, 0, e+k) ⊢* (a, 0, c+k, 0, e)
theorem e_to_c : ∀ k, ∀ c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c e; exists 0
  · intro c e; rw [Nat.add_succ]
    step fm
    apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- Phase 2 (R5+R1+R1 chain): drain c by 2 per round, a by 3, d up by 2.
-- (a+3k, 0, c+2k, d, 0) ⊢* (a, 0, c, d+2k, 0)
theorem r5r1r1_chain : ∀ k, ∀ a c d, ⟨a + 3 * k, 0, c + 2 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih
  · intro a c d; exists 0
  · intro a c d
    rw [show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 2)); ring_nf; finish

-- Phase 3 (R3+R2 chain): k rounds of (R3, R2). Each round: a+=2, b+=1, d-=1.
theorem r3r2_chain : ∀ k, ∀ a b d, ⟨a + 1, b + 1, 0, d + k, 0⟩ [fm]⊢* ⟨a + 2 * k + 1, b + k + 1, 0, d, 0⟩ := by
  intro k; induction' k with k ih
  · intro a b d; exists 0
  · intro a b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show a + 1 = a + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 2) (b + 1) d); ring_nf; finish

-- Phase 4 (R3 chain): drain b, build e.
-- (a+1, b+k, 0, 0, e) ⊢* (a+k+1, b, 0, 0, e+k)
theorem r3_chain : ∀ k, ∀ a b e, ⟨a + 1, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a b e; exists 0
  · intro a b e
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show a + 1 = a + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 1) b (e + 1)); ring_nf; finish

-- Main transition: (3n+4+F, 0, 0, 0, 2n+2) ⊢⁺ (6n+8+F, 0, 0, 0, 2n+4)
theorem main_trans (F n : ℕ) :
    ⟨3 * n + 4 + F, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨6 * n + 8 + F, 0, 0, 0, 2 * n + 4⟩ := by
  -- Phase 1: e to c.
  rw [show (0 : ℕ) = 0 + 0 from rfl,
      show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (2 * n + 2) 0 0 (a := 3 * n + 4 + F))
  rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring]
  -- Phase 2: R5+R1+R1 chain, n+1 rounds.
  rw [show 3 * n + 4 + F = (F + 1) + 3 * (n + 1) from by ring,
      show 2 * n + 2 = 0 + 2 * (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1r1_chain (n + 1) (F + 1) 0 0)
  rw [show 0 + 2 * (n + 1) = 2 * n + 2 from by ring]
  -- Phase 3: R5 then one manual R3+R2, then r3r2_chain, then r3_chain.
  step fm
  step fm; step fm
  rw [show (F + 1 + 1 : ℕ) = (F + 1) + 1 from by ring,
      show (3 : ℕ) = 2 + 1 from rfl,
      show 2 * n + 1 = 0 + (2 * n + 1) from by ring]
  apply stepStar_trans (r3r2_chain (2 * n + 1) (F + 1) 2 0)
  rw [show F + 1 + 2 * (2 * n + 1) + 1 = (F + 4 * n + 3) + 1 from by ring,
      show 2 + (2 * n + 1) + 1 = 0 + (2 * n + 4) from by ring,
      show (0 : ℕ) = 0 + 0 from rfl]
  apply stepStar_trans (r3_chain (2 * n + 4) (F + 4 * n + 3) 0 0)
  rw [show F + 4 * n + 3 + (2 * n + 4) + 1 = 6 * n + 8 + F from by ring,
      show 0 + (2 * n + 4) = 2 * n + 4 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 2⟩) (by execute fm 14)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, n⟩ ↦ ⟨3 * (n + 1) + 1 + F, 0, 0, 0, 2 * (n + 1)⟩) ⟨1, 0⟩
  intro ⟨F, n⟩
  exact ⟨⟨F + 3 * n + 1, n + 1⟩, by
    show ⟨3 * (n + 1) + 1 + F, 0, 0, 0, 2 * (n + 1)⟩ [fm]⊢⁺
         ⟨3 * (n + 1 + 1) + 1 + (F + 3 * n + 1), 0, 0, 0, 2 * (n + 1 + 1)⟩
    rw [show 3 * (n + 1) + 1 + F = 3 * n + 4 + F from by ring,
        show 2 * (n + 1) = 2 * n + 2 from by ring,
        show 3 * (n + 1 + 1) + 1 + (F + 3 * n + 1) = 6 * n + 8 + F from by ring,
        show 2 * (n + 1 + 1) = 2 * n + 4 from by ring]
    exact main_trans F n⟩

end Sz22_2003_unofficial_1529
