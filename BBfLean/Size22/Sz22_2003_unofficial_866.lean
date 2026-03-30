import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #866: [4/105, 45/2, 11/5, 49/33, 5/7]

Vector representation:
```
 2 -1 -1 -1  0
-1  2  1  0  0
 0  0 -1  0  1
 0 -1  0  2 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_866

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 repeated: move c to e.
theorem c_to_e : ∀ k, ∀ c e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (e + 1))
    ring_nf; finish

-- R4 repeated: move b,e to d.
theorem e_to_d : ∀ k, ∀ b d, ⟨0, b + k, 0, d, k⟩ [fm]⊢* ⟨0, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih b (d + 2))
    ring_nf; finish

-- R1R2 interleaved chain.
theorem r1r2_chain : ∀ d, ∀ a b, ⟨a, b + 1, 1, d + 1, 0⟩ [fm]⊢* ⟨a + d + 2, b + d, 0, 0, 0⟩ := by
  intro d; induction' d with d ih <;> intro a b
  · step fm; ring_nf; finish
  · rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 1))
    ring_nf; finish

-- R2 repeated: convert a to b,c.
theorem r2_chain : ∀ k, ∀ a b c, ⟨a + k, b, c, 0, 0⟩ [fm]⊢* ⟨a, b + 2 * k, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2) (c + 1))
    ring_nf; finish

-- Combined phases as stepStar.
theorem phases_star (B' C' : ℕ) :
    ⟨0, B' + C' + 2, C' + 1, 0, 0⟩ [fm]⊢* ⟨0, B' + 6 * C' + 4, 2 * C' + 2, 0, 0⟩ := by
  -- Phase 1: c_to_e: move C'+1 from c to e
  apply stepStar_trans
  · rw [show C' + 1 = 0 + (C' + 1) from by ring]
    exact c_to_e (C' + 1) 0 0 (b := B' + C' + 2)
  rw [show (0 : ℕ) + (C' + 1) = C' + 1 from by ring]
  -- Phase 2: e_to_d: move C'+1 from b,e to d
  apply stepStar_trans
  · rw [show B' + C' + 2 = (B' + 1) + (C' + 1) from by ring]
    exact e_to_d (C' + 1) (B' + 1) 0
  rw [show 0 + 2 * (C' + 1) = 2 * C' + 2 from by ring]
  -- Phase 3: R5 step
  rw [show 2 * C' + 2 = (2 * C' + 1) + 1 from by ring]
  step fm
  -- Phase 4: r1r2_chain
  rw [show B' + 1 = B' + 1 from rfl]
  apply stepStar_trans (r1r2_chain (2 * C') 0 B')
  rw [show 0 + 2 * C' + 2 = 2 * C' + 2 from by ring]
  -- Phase 5: r2_chain
  rw [show 2 * C' + 2 = 0 + (2 * C' + 2) from by ring]
  apply stepStar_trans (r2_chain (2 * C' + 2) 0 (B' + 2 * C') 0)
  ring_nf; finish

-- Convert to stepPlus.
theorem main_transition (B' C' : ℕ) :
    ⟨0, B' + C' + 2, C' + 1, 0, 0⟩ [fm]⊢⁺ ⟨0, B' + 6 * C' + 4, 2 * C' + 2, 0, 0⟩ := by
  apply stepStar_stepPlus (phases_star B' C')
  intro h
  have := congr_arg (fun q : Q ↦ q.2.2.1) h
  simp at this; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 1, 0, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, p.1 + p.2 + 2, p.2 + 1, 0, 0⟩) ⟨0, 0⟩
  intro ⟨B', C'⟩
  refine ⟨⟨B' + 4 * C' + 1, 2 * C' + 1⟩, ?_⟩
  show ⟨0, B' + C' + 2, C' + 1, 0, 0⟩ [fm]⊢⁺ ⟨0, (B' + 4 * C' + 1) + (2 * C' + 1) + 2, (2 * C' + 1) + 1, 0, 0⟩
  rw [show (B' + 4 * C' + 1) + (2 * C' + 1) + 2 = B' + 6 * C' + 4 from by ring,
      show (2 * C' + 1) + 1 = 2 * C' + 2 from by ring]
  exact main_transition B' C'

end Sz22_2003_unofficial_866
