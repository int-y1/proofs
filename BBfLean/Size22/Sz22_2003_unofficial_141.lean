import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #141: [1/45, 20/21, 11/3, 3/2, 441/11]

Vector representation:
```
 0 -2 -1  0  0
 2 -1  1 -1  0
 0 -1  0  0  1
-1  1  0  0  0
 0  2  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_141

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d+2, e⟩
  | _ => none

/-- pump_up: transfer d to a and c via rules 4,2. -/
theorem pump_up : ∀ k, ∀ a c e, ⟨a+1, 0, c, k, e⟩ [fm]⊢* ⟨a+1+k, 0, c+k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  -- (a+1, 0, c, k+1, e) -> rule 4 -> (a, 1, c, k+1, e) -> rule 2 -> (a+2, 0, c+1, k, e)
  step fm; step fm
  apply stepStar_trans (ih (a + 1) (c + 1) e)
  ring_nf; finish

/-- drain_a: transfer a to e via rules 4,3. -/
theorem drain_a : ∀ k, ∀ c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  -- (k+1, 0, c, 0, e) -> rule 4 -> (k, 1, c, 0, e) -> rule 3 -> (k, 0, c, 0, e+1)
  step fm; step fm
  apply stepStar_trans (ih c (e + 1))
  ring_nf; finish

/-- drain_c: transfer c to d via rules 5,1, consuming e. -/
theorem drain_c : ∀ k, ∀ d e, ⟨0, 0, k, d, e+k⟩ [fm]⊢* ⟨0, 0, 0, d+2*k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  -- (0, 0, k+1, d, e+(k+1)) -> rule 5 -> (0, 2, k+1, d+2, e+k) -> rule 1 -> (0, 0, k, d+2, e+k)
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih (d + 2) e)
  ring_nf; finish

/-- Main transition: (0, 0, 0, d, e+1) ⊢⁺ (0, 0, 0, 2*d+4, e+2). -/
theorem main_step : ∀ d e, ⟨0, 0, 0, d, e+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*d+4, e+2⟩ := by
  intro d e
  -- Step 1: rule 5: (0, 0, 0, d, e+1) -> (0, 2, 0, d+2, e)
  step fm
  -- Step 2: rules 2,2: (0, 2, 0, d+2, e) -> (2, 1, 1, d+1, e) -> (4, 0, 2, d, e)
  step fm; step fm
  -- Step 3: pump_up with a=3, c=2, k=d
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (pump_up d 3 2 e)
  -- Now at (3+1+d, 0, 2+d, 0, e) = (d+4, 0, d+2, 0, e)
  -- Step 4: drain_a with k=d+4
  rw [show 3 + 1 + d = d + 4 from by ring,
      show 2 + d = d + 2 from by ring]
  apply stepStar_trans (drain_a (d + 4) (d + 2) e)
  -- Now at (0, 0, d+2, 0, e+d+4) = (0, 0, d+2, 0, (e+2)+(d+2))
  -- Step 5: drain_c with k=d+2, d₀=0, e₀=e+2
  rw [show e + (d + 4) = (e + 2) + (d + 2) from by ring]
  apply stepStar_trans (drain_c (d + 2) 0 (e + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) ->* (0,0,0,0,1) = C(0,0) in 2 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1⟩)
  · execute fm 2
  -- Use progress_nonhalt_simple with C(d,e) = (0, 0, 0, d, e+1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (C := fun p ↦ ⟨0, 0, 0, p.1, p.2 + 1⟩) (i₀ := ⟨0, 0⟩)
  intro ⟨d, e⟩
  exact ⟨⟨2 * d + 4, e + 1⟩, main_step d e⟩

end Sz22_2003_unofficial_141
