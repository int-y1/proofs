import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1275: [54/35, 5/33, 7/3, 11/49, 15/2]

Vector representation:
```
 1  3 -1 -1  0
 0 -1  1  0 -1
 0 -1  0  1  0
 0  0  0 -2  1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1275

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 repeated: drain d by pairs into e
theorem r4_drain : ∀ k, ⟨a, 0, 0, d + 2 * k, 0⟩ [fm]⊢* ⟨a, 0, 0, d, k⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (d := d + 2))
    step fm; finish

-- R3 repeated: drain b into d
theorem r3_drain : ∀ k, ∀ a b d, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (d + 1))
    ring_nf; finish

-- R2 four times: drain 4 from b and e, build c
theorem r2_four : ⟨a, 4, 0, 0, k + 4⟩ [fm]⊢* ⟨a, 0, 4, 0, k⟩ := by
  step fm; step fm; step fm; step fm; finish

-- R5+R2 alternating: each pair transfers 1 from a and e to c
theorem r5r2_chain : ∀ k, ∀ a c, ⟨a + k, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    step fm
    rw [show c + 1 + 1 = c + 2 from by ring]
    apply stepStar_trans (ih a (c + 2))
    ring_nf; finish

-- R1+R3 spiral: converts c into a and b
theorem r1r3_spiral : ∀ n, ∀ a b, ⟨a, b, n + 1, 1, 0⟩ [fm]⊢* ⟨a + n + 1, b + 3 + 2 * n, 0, 0, 0⟩ := by
  intro n; induction' n with n ih <;> intro a b
  · step fm; finish
  · step fm
    step fm
    apply stepStar_trans (ih (a + 1) (b + 2))
    ring_nf; finish

-- Canonical state (a+k+1, 0, 0, 2(k+4)+1, 0) transitions to (a+2k+5, 0, 0, 2(2k+5)+1, 0)
theorem main_trans (a k : ℕ) :
    ⟨a + k + 1, 0, 0, 2 * (k + 4) + 1, 0⟩ [fm]⊢⁺ ⟨a + 2 * k + 5, 0, 0, 2 * (2 * k + 5) + 1, 0⟩ := by
  rw [show 2 * (k + 4) + 1 = 1 + 2 * (k + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (k + 4) (a := a + k + 1) (d := 1))
  step fm
  step fm
  show ⟨a + k + 1, 4, 0, 0, k + 4⟩ [fm]⊢* _
  apply stepStar_trans (r2_four (a := a + k + 1) (k := k))
  rw [show a + k + 1 = a + 1 + k from by ring]
  apply stepStar_trans (r5r2_chain k (a + 1) 4)
  rw [show 4 + 2 * k = 2 * k + 4 from by ring]
  step fm
  rw [show 2 * k + 4 + 1 = 2 * k + 5 from by ring]
  step fm
  show ⟨a, 0, (2 * k + 4) + 1, 1, 0⟩ [fm]⊢* _
  apply stepStar_trans (r1r3_spiral (2 * k + 4) a 0)
  rw [show a + (2 * k + 4) + 1 = a + 2 * k + 5 from by ring,
      show 0 + 3 + 2 * (2 * k + 4) = 0 + (4 * k + 11) from by ring]
  apply stepStar_trans (r3_drain (4 * k + 11) (a + 2 * k + 5) 0 0)
  rw [show 0 + (4 * k + 11) = 2 * (2 * k + 5) + 1 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 2 * 7 + 1, 0⟩) (by execute fm 72)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, k⟩ ↦ ⟨a + k + 1, 0, 0, 2 * (k + 4) + 1, 0⟩) ⟨3, 3⟩
  intro ⟨a, k⟩
  refine ⟨⟨a + 3, 2 * k + 1⟩, ?_⟩
  show ⟨a + k + 1, 0, 0, 2 * (k + 4) + 1, 0⟩ [fm]⊢⁺ ⟨a + 3 + (2 * k + 1) + 1, 0, 0, 2 * (2 * k + 1 + 4) + 1, 0⟩
  rw [show a + 3 + (2 * k + 1) + 1 = a + 2 * k + 5 from by ring,
      show 2 * (2 * k + 1 + 4) + 1 = 2 * (2 * k + 5) + 1 from by ring]
  exact main_trans a k

end Sz22_2003_unofficial_1275
