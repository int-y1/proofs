import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #43: [1/15, 49/3, 6/77, 5/49, 3993/2]

Vector representation:
```
 0 -1 -1  0  0
 0 -1  0  2  0
 1  1  0 -1 -1
 0  0  1 -2  0
-1  1  0  0  3
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_43

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+3⟩
  | _ => none

theorem r3r2_chain : ∀ k a d, ⟨a, 0, 0, d + 1, k⟩ [fm]⊢* ⟨a + k, 0, 0, d + 1 + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm; step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (d + 1))
    ring_nf; finish

theorem r4_chain : ∀ k a c d, ⟨a, 0, c, d + 2 * k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [Nat.mul_succ, ← Nat.add_assoc]
    step fm
    apply stepStar_trans (ih a _ d)
    ring_nf; finish

theorem r5r1_drain : ∀ k a e, ⟨a + k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih a _)
    ring_nf; finish

theorem even_trans (k a : ℕ) : ⟨a + 1, 0, 0, 0, 2 * k⟩ [fm]⊢⁺ ⟨a + k + 3, 0, 0, 0, 3 * k + 2⟩ := by
  -- R5, R2
  step fm; step fm
  -- R3R2 chain (2k+3 rounds): (a, 0, 0, 2, 2k+3) → (a+2k+3, 0, 0, 2k+5, 0)
  change ⟨a, 0, 0, 1 + 1, 2 * k + 3⟩ [fm]⊢* _
  apply stepStar_trans (r3r2_chain (2 * k + 3) a 1)
  -- R4 chain (k+2 rounds): (a+2k+3, 0, 0, 2k+5, 0) → (a+2k+3, 0, k+2, 1, 0)
  rw [show 1 + 1 + (2 * k + 3) = 1 + 2 * (k + 2) from by ring]
  apply stepStar_trans (r4_chain (k + 2) _ 0 1)
  simp only [Nat.zero_add]
  -- 4 fixed steps (R5, R1, R3, R1): → (a+2k+3, 0, k, 0, 2)
  step fm; step fm; step fm; step fm
  -- R5R1 drain (k rounds): → (a+k+3, 0, 0, 0, 3k+2)
  rw [show a + 2 * k + 2 + 1 = (a + k + 3) + k from by ring]
  apply stepStar_trans (r5r1_drain k (a + k + 3) 2)
  ring_nf; finish

theorem odd_trans (k a : ℕ) : ⟨a + 1, 0, 0, 0, 2 * k + 1⟩ [fm]⊢⁺ ⟨a + k + 1, 0, 0, 0, 3 * k + 9⟩ := by
  -- R5, R2
  step fm; step fm
  -- R3R2 chain (2k+4 rounds)
  rw [show 2 * k + 1 + 3 = 2 * k + 4 from by ring]
  change ⟨a, 0, 0, 1 + 1, 2 * k + 4⟩ [fm]⊢* _
  apply stepStar_trans (r3r2_chain (2 * k + 4) a 1)
  -- R4 chain (k+3 rounds): 2k+6 = 0 + 2*(k+3)
  rw [show 1 + 1 + (2 * k + 4) = 0 + 2 * (k + 3) from by ring]
  apply stepStar_trans (r4_chain (k + 3) _ 0 0)
  simp only [Nat.zero_add]
  -- R5R1 drain (k+3 rounds)
  rw [show a + (2 * k + 4) = (a + k + 1) + (k + 3) from by ring]
  apply stepStar_trans (r5r1_drain (k + 3) (a + k + 1) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + 1, 0, 0, 0, e⟩) ⟨0, 0⟩
  intro ⟨a, e⟩
  rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [show k + k = 2 * k from by ring]
    exact ⟨⟨a + k + 2, 3 * k + 2⟩, even_trans k a⟩
  · subst hk
    exact ⟨⟨a + k, 3 * k + 9⟩, odd_trans k a⟩

end Sz22_2003_unofficial_43
