import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1920: [9/70, 11/5, 50/21, 7/11, 21/2]

Vector representation:
```
-1  2 -1 -1  0
 0  0 -1  0  1
 1 -1  2 -1  0
 0  0  0  1 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1920

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4: transfer e to d
theorem e_to_d_fwd : ∀ k, ∀ d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · apply stepStar_trans
    · apply step_stepStar
      show fm ⟨a, 0, 0, d, k + 1⟩ = some ⟨a, 0, 0, d + 1, k⟩
      simp [fm]
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

-- R1R1R3 round
theorem r1r1r3_step : ⟨a + 2, b, 2, d + 3, 0⟩ [fm]⊢⁺ ⟨a + 1, b + 3, 2, d, 0⟩ := by
  step fm; step fm; step fm; finish

-- R1R1R3 chain: k rounds, consuming 3k from d
-- (a+1+k, b, 2, 3*k+r, 0) ⊢* (a+1, b+3*k, 2, r, 0)
-- The +1 offset on a ensures a >= 1 throughout for R1R1.
theorem r1r1r3_chain : ∀ k, ∀ a b, ⟨a + 1 + k, b, 2, 3 * k + r, 0⟩ [fm]⊢* ⟨a + 1, b + 3 * k, 2, r, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · simp; exists 0
  · rw [show a + 1 + (k + 1) = a + 1 + k + 1 from by ring,
        show 3 * (k + 1) + r = (3 * k + r) + 3 from by ring,
        show a + 1 + k + 1 = (a + k) + 2 from by ring]
    apply stepStar_trans (stepPlus_stepStar (r1r1r3_step (a := a + k) (b := b) (d := 3 * k + r)))
    rw [show a + k + 1 = a + 1 + k from by ring]
    apply stepStar_trans (ih a (b + 3))
    ring_nf; finish

-- b-drain cycle
theorem b_drain_step : ⟨a, b + 1, 2, 0, e⟩ [fm]⊢⁺ ⟨a + 1, b, 2, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; finish

-- b-drain chain
theorem b_drain_chain : ∀ k, ∀ a e, ⟨a, k, 2, 0, e⟩ [fm]⊢* ⟨a + k, 0, 2, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · simp; exists 0
  · apply stepStar_trans (stepPlus_stepStar (b_drain_step (a := a) (b := k) (e := e)))
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- b-drain end
theorem b_drain_end : ⟨a, 0, 2, 0, e⟩ [fm]⊢* ⟨a, 0, 0, e + 2, 0⟩ := by
  step fm; step fm
  show ⟨a, 0, 0, 0, e + 2⟩ [fm]⊢* ⟨a, 0, 0, e + 2, 0⟩
  have := e_to_d_fwd (e + 2) 0 (a := a)
  simp at this
  exact this

-- Full b-drain
theorem full_b_drain : ⟨a, b, 2, 0, e⟩ [fm]⊢* ⟨a + b, 0, 0, e + b + 2, 0⟩ := by
  apply stepStar_trans (b_drain_chain b a e)
  apply stepStar_trans (b_drain_end (a := a + b) (e := e + b))
  ring_nf; finish

-- Opening: R5 then R3
theorem opening : ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 1, 0, 2, d, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, d, 0⟩ = some ⟨a, 1, 0, d + 1, 0⟩; simp [fm]
  apply step_stepStar
  show fm ⟨a, 1, 0, d + 1, 0⟩ = some ⟨a + 1, 0, 2, d, 0⟩; simp [fm]

-- Transition D = 3m
theorem trans_d3m : ⟨a + m + 1, 0, 0, 3 * m, 0⟩ [fm]⊢⁺ ⟨a + 3 * m + 1, 0, 0, 3 * m + 2, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (opening (a := a + m) (d := 3 * m))
  show ⟨a + m + 1, 0, 2, 3 * m, 0⟩ [fm]⊢* ⟨a + 3 * m + 1, 0, 0, 3 * m + 2, 0⟩
  rw [show 3 * m = 3 * m + 0 from by ring,
      show a + m + 1 = a + 1 + m from by ring]
  apply stepStar_trans (r1r1r3_chain m a 0 (r := 0))
  rw [show (0 : ℕ) + 3 * m = 3 * m from by ring, show (0 : ℕ) = 0 from rfl]
  apply stepStar_trans (full_b_drain (a := a + 1) (b := 3 * m) (e := 0))
  ring_nf; finish

-- Transition D = 3m + 2
theorem trans_d3m2 : ⟨a + m + 3, 0, 0, 3 * m + 2, 0⟩ [fm]⊢⁺ ⟨a + 3 * m + 5, 0, 0, 3 * m + 6, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (opening (a := a + m + 2) (d := 3 * m + 2))
  show ⟨a + m + 3, 0, 2, 3 * m + 2, 0⟩ [fm]⊢* ⟨a + 3 * m + 5, 0, 0, 3 * m + 6, 0⟩
  rw [show a + m + 3 = (a + 2) + 1 + m from by ring]
  apply stepStar_trans (r1r1r3_chain m (a + 2) 0 (r := 2))
  rw [show (0 : ℕ) + 3 * m = 3 * m from by ring]
  -- At (a+3, 3m, 2, 2, 0). R1 R1 R5 R3 then b-drain.
  step fm; step fm
  -- At (a+1, 3m+4, 0, 0, 0)
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨a + 1, 3 * m + 4, 0, 0, 0⟩ = some ⟨a, 3 * m + 5, 0, 1, 0⟩; simp [fm]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨a, 3 * m + 5, 0, 1, 0⟩ = some ⟨a + 1, 3 * m + 4, 2, 0, 0⟩; simp [fm]
  apply stepStar_trans (full_b_drain (a := a + 1) (b := 3 * m + 4) (e := 0))
  ring_nf; finish

-- 2-step macro
theorem macro_trans (f k : ℕ) :
    ⟨f + 2 * k + 3, 0, 0, 6 * k + 6, 0⟩ [fm]⊢⁺ ⟨f + 10 * k + 13, 0, 0, 6 * k + 12, 0⟩ := by
  apply stepPlus_trans
  · rw [show f + 2 * k + 3 = f + (2 * k + 2) + 1 from by ring,
        show 6 * k + 6 = 3 * (2 * k + 2) from by ring]
    exact trans_d3m (a := f) (m := 2 * k + 2)
  · rw [show f + 3 * (2 * k + 2) + 1 = (f + 4 * k + 2) + (2 * k + 2) + 3 from by ring,
        show 3 * (2 * k + 2) + 2 = 3 * (2 * k + 2) + 2 from rfl]
    have h := trans_d3m2 (a := f + 4 * k + 2) (m := 2 * k + 2)
    rw [show f + 4 * k + 2 + 3 * (2 * k + 2) + 5 = f + 10 * k + 13 from by ring,
        show 3 * (2 * k + 2) + 6 = 6 * k + 12 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 6, 0⟩) (by execute fm 54)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨f, k⟩ ↦ ⟨f + 2 * k + 3, 0, 0, 6 * k + 6, 0⟩) ⟨2, 0⟩
  intro ⟨f, k⟩
  refine ⟨⟨f + 8 * k + 8, k + 1⟩, ?_⟩
  show ⟨f + 2 * k + 3, 0, 0, 6 * k + 6, 0⟩ [fm]⊢⁺ ⟨f + 8 * k + 8 + 2 * (k + 1) + 3, 0, 0, 6 * (k + 1) + 6, 0⟩
  rw [show f + 8 * k + 8 + 2 * (k + 1) + 3 = f + 10 * k + 13 from by ring,
      show 6 * (k + 1) + 6 = 6 * k + 12 from by ring]
  exact macro_trans f k

end Sz22_2003_unofficial_1920
