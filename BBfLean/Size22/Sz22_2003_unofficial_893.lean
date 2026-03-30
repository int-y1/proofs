import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #893: [4/15, 147/22, 25/2, 11/7, 21/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  2 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_893

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 repeated: d+k → d, e → e+k
theorem d_to_e : ∀ k e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e + 1))
    ring_nf; finish

-- R3 repeated: a → 0, c → c+2*a
theorem r3_drain : ∀ a, ⟨a, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * a, d, 0⟩ := by
  intro a; induction' a with a ih generalizing c
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 2))
    ring_nf; finish

-- R2+R1 spiral: k rounds
theorem spiral : ∀ k a c d e, ⟨a + 1, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 1 + k, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c (d + 2) e)
    ring_nf; finish

-- Main transition
theorem main_trans (n d : ℕ) : ⟨0, 0, n + d + 2, d, 0⟩ [fm]⊢⁺ ⟨0, 0, n + 2 * d + 4, 2 * d + 1, 0⟩ := by
  -- d_to_e phase
  have h1 : ⟨0, 0, n + d + 2, d, 0⟩ [fm]⊢* ⟨0, 0, n + d + 2, 0, d⟩ := by
    have := d_to_e d 0 (c := n + d + 2) (d := 0)
    simp only [Nat.zero_add] at this
    exact this
  apply stepStar_stepPlus_stepPlus h1
  -- R5 step
  rw [show n + d + 2 = (n + d + 1) + 1 from by ring]
  step fm
  -- R1 step
  rw [show n + d + 1 = (n + d) + 1 from by ring]
  step fm
  -- spiral phase
  have h3 : ⟨2, 0, n + d, 1, d⟩ [fm]⊢* ⟨d + 2, 0, n, 2 * d + 1, 0⟩ := by
    have := spiral d 1 n 1 0
    simp only [Nat.zero_add] at this
    rw [show 1 + 1 = 2 from by ring,
        show 1 + 1 + d = d + 2 from by ring,
        show 1 + 2 * d = 2 * d + 1 from by ring] at this
    exact this
  apply stepStar_trans h3
  -- R3 drain
  apply stepStar_trans (r3_drain (d + 2) (c := n) (d := 2 * d + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c, d, 0⟩ ∧ c ≥ d + 2)
  · intro q ⟨c, d, hq, hcd⟩; subst hq
    obtain ⟨n, rfl⟩ : ∃ n, c = n + d + 2 := ⟨c - d - 2, by omega⟩
    exact ⟨⟨0, 0, n + 2 * d + 4, 2 * d + 1, 0⟩,
      ⟨n + 2 * d + 4, 2 * d + 1, rfl, by omega⟩, main_trans n d⟩
  · exact ⟨2, 0, rfl, by omega⟩

end Sz22_2003_unofficial_893
