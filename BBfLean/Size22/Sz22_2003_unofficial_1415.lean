import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1415: [7/15, 121/3, 36/77, 5/2, 21/5]

Vector representation:
```
 0 -1 -1  1  0
 0 -1  0  0  2
 2  2  0 -1 -1
-1  0  1  0  0
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1415

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: move a to c.
theorem r4_chain : ∀ k, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (c := c + 1))
    ring_nf; finish

-- R3+R1+R1 chain: interleaved phase draining c by 2 each round.
theorem r3r1r1_chain : ∀ k, ∀ a d E,
    ⟨a, 0, 2 * k, d + 1, E + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + k + 1, E⟩ := by
  intro k; induction' k with k ih <;> intro a d E
  · ring_nf; finish
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    step fm  -- R3
    step fm  -- R1
    step fm  -- R1
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) (d + 1) E)
    ring_nf; finish

-- R3+R2+R2 chain: drain d, building a and e.
theorem r3r2r2_chain : ∀ k, ∀ a d E,
    ⟨a, 0, 0, d + k, E + 1⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, E + 3 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d E
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R3
    step fm  -- R2
    step fm  -- R2
    apply stepStar_trans (ih (a + 2) d (E + 3))
    ring_nf; finish

-- Main transition: (2*(a+1), 0, 0, 0, e+a+5) ⊢⁺ (4*(a+1), 0, 0, 0, e+3*a+11)
theorem main_trans (a e : ℕ) :
    ⟨2 * (a + 1), 0, 0, 0, e + a + 5⟩ [fm]⊢⁺ ⟨4 * (a + 1), 0, 0, 0, e + 3 * a + 11⟩ := by
  -- Phase 1: R4 chain, move 2*(a+1) from register a to c.
  have h1 : ⟨2 * (a + 1), 0, 0, 0, e + a + 5⟩ [fm]⊢*
      ⟨0, 0, 2 * (a + 1), 0, e + a + 5⟩ := by
    rw [show 2 * (a + 1) = 0 + 2 * (a + 1) from by ring]
    apply stepStar_trans (r4_chain (2 * (a + 1)) (a := 0) (c := 0))
    ring_nf; finish
  -- Phase 2: R5 + R1.
  have h2 : ⟨0, 0, 2 * (a + 1), 0, e + a + 5⟩ [fm]⊢⁺
      ⟨0, 0, 2 * a, 2, e + a + 5⟩ := by
    rw [show 2 * (a + 1) = 2 * a + 1 + 1 from by ring]
    step fm  -- R5
    step fm  -- R1
    ring_nf; finish
  -- Phase 3: R3+R1+R1 chain with k = a rounds.
  have h3 : ⟨0, 0, 2 * a, 2, e + a + 5⟩ [fm]⊢*
      ⟨2 * a, 0, 0, a + 2, e + 5⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show e + a + 5 = (e + 5) + a from by ring]
    apply stepStar_trans (r3r1r1_chain a 0 1 (e + 5))
    ring_nf; finish
  -- Phase 4: R3+R2+R2 chain with k = a+2 rounds.
  have h4 : ⟨2 * a, 0, 0, a + 2, e + 5⟩ [fm]⊢*
      ⟨4 * (a + 1), 0, 0, 0, e + 3 * a + 11⟩ := by
    rw [show a + 2 = 0 + (a + 2) from by ring,
        show e + 5 = (e + 4) + 1 from by ring]
    apply stepStar_trans (r3r2r2_chain (a + 2) (2 * a) 0 (e + 4))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 5⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨2 * (a + 1), 0, 0, 0, e + a + 5⟩) ⟨0, 0⟩
  intro ⟨a, e⟩
  refine ⟨⟨2 * a + 1, e + a + 5⟩, ?_⟩
  show ⟨2 * (a + 1), 0, 0, 0, e + a + 5⟩ [fm]⊢⁺ ⟨2 * (2 * a + 1 + 1), 0, 0, 0, e + a + 5 + (2 * a + 1) + 5⟩
  convert main_trans a e using 2; ring_nf

end Sz22_2003_unofficial_1415
