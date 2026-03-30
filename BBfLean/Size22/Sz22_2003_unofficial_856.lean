import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #856: [36/35, 5/33, 49/3, 11/2, 15/11]

Vector representation:
```
 2  2 -1 -1  0
 0 -1  1  0 -1
 0 -1  0  2  0
-1  0  0  0  1
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_856

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ⟨k + a, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · ring_nf; finish
  · rw [show k + 1 + a = (k + a) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a, k + b, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih generalizing b d
  · ring_nf; finish
  · rw [show k + 1 + b = (k + b) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

theorem r1r2_loop : ∀ k, ⟨a, b, 1, d + k, k⟩ [fm]⊢* ⟨a + 2 * k, b + k, 1, d, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a + 2) (b := b + 1))
    ring_nf; finish

-- Full transition from (0, 0, 0, d, e+1) where d = e+1+g
-- Result: (2e+2, 0, 0, d+e+5, 0) = (2e+2, 0, 0, 2e+g+6, 0)
theorem spiral : ∀ e, ⟨0, 0, 0, e + 1 + g, e + 1⟩ [fm]⊢* ⟨2 * e + 2, 0, 0, 2 * e + g + 6, 0⟩ := by
  intro e; induction' e with e ih generalizing g
  · -- e = 0: (0,0,0,1+g,1)
    -- R5: (0,1,1,1+g,0), R1: (2,3,0,g,0), R3 x3: (2,0,0,g+6,0)
    rw [show (0 : ℕ) + 1 + g = g + 1 from by ring]
    step fm  -- R5
    step fm  -- R1
    rw [show (3 : ℕ) = 3 + 0 from by ring]
    apply stepStar_trans (r3_chain 3 (a := 2) (b := 0) (d := g))
    ring_nf; finish
  · -- e+1: (0,0,0,e+2+g,e+2)
    -- R5: (0,1,1,e+2+g,e+1)
    -- R1: (2,3,0,e+1+g,e+1)
    -- R2: (2,2,1,e+1+g,e)
    -- r1r2_loop(e): (2+2e,2+e,1,1+g,0)
    -- R1: (2e+4,e+4,0,g,0)
    -- R3 x(e+4): (2e+4,0,0,g+2e+8,0)
    rw [show e + 1 + 1 + g = (e + 1 + g) + 1 from by ring,
        show e + 1 + 1 = (e + 1) + 1 from by ring]
    step fm  -- R5: (0, 1, 1, (e+1+g)+1, e+1)
    -- After step fm normalization, state might be (0, 1, 1, e+1+g+1, e+1)
    -- Need d+1 pattern for R1
    rw [show e + 1 + g + 1 = (e + g) + 1 + 1 from by ring]
    step fm  -- R1: (2, 3, 0, (e+g)+1, e+1)
    -- After step fm normalization: (2, 3, 0, e+g+1, e+1)
    -- R2: b=3≥1, e=e+1≥1
    step fm  -- R2: (2, 2, 1, e+g+1, e)
    rw [show e + g + 1 = (g + 1) + e from by ring]
    apply stepStar_trans (r1r2_loop e (a := 2) (b := 2) (d := g + 1))
    -- (2+2*e, 2+e, 1, g+1, 0)
    step fm  -- R1: (2+2*e+2, 2+e+2, 0, g, 0)
    show ⟨2 + 2 * e + 2, 2 + e + 2, 0, g, 0⟩ [fm]⊢* ⟨2 * (e + 1) + 2, 0, 0, 2 * (e + 1) + g + 6, 0⟩
    rw [show 2 + e + 2 = (e + 4) + 0 from by ring,
        show 2 + 2 * e + 2 = 2 * (e + 1) + 2 from by ring]
    apply stepStar_trans (r3_chain (e + 4) (a := 2 * (e + 1) + 2) (b := 0) (d := g))
    ring_nf; finish

theorem main_trans (a g : ℕ) : ⟨a + 1, 0, 0, a + 1 + g, 0⟩ [fm]⊢⁺ ⟨2 * a + 2, 0, 0, 2 * a + g + 6, 0⟩ := by
  step fm  -- R4: (a, 0, 0, a+1+g, 1)
  rw [show (a : ℕ) = a + 0 from by ring]
  apply stepStar_trans (r4_chain a (a := 0) (d := a + 1 + g) (e := 1))
  show ⟨0, 0, 0, a + 1 + g, 1 + a⟩ [fm]⊢* ⟨2 * a + 2, 0, 0, 2 * a + g + 6, 0⟩
  rw [show 1 + a = a + 1 from by ring]
  exact spiral a (g := g)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 5, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, g⟩ ↦ ⟨a + 1, 0, 0, a + 1 + g, 0⟩) ⟨1, 3⟩
  intro ⟨a, g⟩
  exact ⟨⟨2 * a + 1, g + 4⟩, by
    show ⟨a + 1, 0, 0, a + 1 + g, 0⟩ [fm]⊢⁺ ⟨2 * a + 1 + 1, 0, 0, 2 * a + 1 + 1 + (g + 4), 0⟩
    rw [show 2 * a + 1 + 1 = 2 * a + 2 from by ring,
        show 2 * a + 1 + 1 + (g + 4) = 2 * a + g + 6 from by ring]
    exact main_trans a g⟩

end Sz22_2003_unofficial_856
