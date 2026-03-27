import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #321: [16/15, 33/14, 55/2, 7/11, 3/7]

Vector representation:
```
 4 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  1
 0  0  0  1 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_321

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+4, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Rule 3 loop: (k+1, 0, c, 0, e) ->* (0, 0, c+k+1, 0, e+k+1)
theorem rule3_loop : ∀ k c e,
    ⟨k + 1, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k + 1, 0, e + k + 1⟩ := by
  intro k; induction k with
  | zero => intro c e; step fm; ring_nf; finish
  | succ k ih =>
    intro c e; step fm
    apply stepStar_trans (ih (c + 1) (e + 1))
    ring_nf; finish

-- Rule 4 loop: (0, 0, c, d, e+1) ->* (0, 0, c, d+e+1, 0)
theorem rule4_loop : ∀ e c d,
    ⟨0, 0, c, d, e + 1⟩ [fm]⊢* ⟨0, 0, c, d + e + 1, 0⟩ := by
  intro e; induction e with
  | zero => intro c d; step fm; ring_nf; finish
  | succ e ih =>
    intro c d; step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

-- Rule 2+1 loop: (a+1, 0, c+1, d+1, e) ->* (a + 3*c + 4, 0, 0, d-c, e+c+1)
-- Parameterize: induction on c, with d = g + c (g is the "gap", d after loop).
-- (a+1, 0, c+1, g+c+1, e) ->* (a+3*c+4, 0, 0, g, e+c+1)
theorem rule21_loop : ∀ c a g e,
    ⟨a + 1, 0, c + 1, g + c + 1, e⟩ [fm]⊢* ⟨a + 3 * c + 4, 0, 0, g, e + c + 1⟩ := by
  intro c; induction c with
  | zero => intro a g e; step fm; step fm; ring_nf; finish
  | succ c ih =>
    intro a g e
    -- State: (a+1, 0, c+2, g+c+2, e)
    -- rule 2: (a, 1, c+2, g+c+1, e+1)
    -- rule 1: (a+4, 0, c+1, g+c+1, e+1)
    -- Apply IH with a' = a+3, same g, e' = e+1
    rw [show g + (c + 1) + 1 = g + c + 1 + 1 from by ring,
        show c + 1 + 1 = (c + 1) + 1 from rfl]
    step fm; step fm
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) g (e + 1))
    ring_nf; finish

-- Rule 2 loop on d: (a+d+1, b, 0, d+1, e) ->* (a, b+d+1, 0, 0, e+d+1)
-- Induction on d.
theorem rule2_loop : ∀ d a b e,
    ⟨a + d + 1, b, 0, d + 1, e⟩ [fm]⊢* ⟨a, b + d + 1, 0, 0, e + d + 1⟩ := by
  intro d; induction d with
  | zero => intro a b e; step fm; ring_nf; finish
  | succ d ih =>
    intro a b e
    -- State: (a+d+2, b, 0, d+2, e)
    -- rule 2: (a+d+1, b+1, 0, d+1, e+1)
    rw [show a + (d + 1) + 1 = (a + d + 1) + 1 from by ring,
        show (d + 1) + 1 = (d + 1) + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (b + 1) (e + 1))
    ring_nf; finish

-- Rule 3+1 loop: (a+1, b+1, 0, 0, e) ->* (a+3*b+4, 0, 0, 0, e+b+1)
-- Each step: rule 3 then rule 1.
theorem rule31_loop : ∀ b a e,
    ⟨a + 1, b + 1, 0, 0, e⟩ [fm]⊢* ⟨a + 3 * b + 4, 0, 0, 0, e + b + 1⟩ := by
  intro b; induction b with
  | zero => intro a e; step fm; step fm; ring_nf; finish
  | succ b ih =>
    intro a e
    -- State: (a+1, b+2, 0, 0, e)
    -- rule 3: (a, b+2, 1, 0, e+1)
    -- rule 1: (a+4, b+1, 0, 0, e+1)
    rw [show b + 1 + 1 = (b + 1) + 1 from rfl]
    step fm; step fm
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (e + 1))
    ring_nf; finish

-- Main: (A+1, 0, 0, 0, E) ⊢⁺ (3A+2E+4, 0, 0, 0, A+2E) when E ≤ A
theorem main_trans : ∀ A E, E ≤ A →
    ⟨A + 1, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨3 * A + 2 * E + 4, 0, 0, 0, A + 2 * E⟩ := by
  intro A E hle
  -- First step (rule 3) to get ⊢⁺
  apply step_stepStar_stepPlus
  · show fm ⟨A + 1, 0, 0, 0, E⟩ = some ⟨A, 0, 1, 0, E + 1⟩
    match E with
    | 0 => unfold fm; simp
    | _ + 1 => unfold fm; simp
  -- Now at (A, 0, 1, 0, E+1)
  -- Rest of phase 1 + all other phases
  match A with
  | 0 =>
    -- E = 0 since E ≤ 0
    have hE : E = 0 := Nat.eq_zero_of_le_zero hle; subst hE
    -- (0, 0, 1, 0, 1) -> rule4 -> (0, 0, 1, 1, 0)
    -- -> rule5 -> (0, 1, 1, 0, 0) -> rule1 -> (4, 0, 0, 0, 0)
    execute fm 3
  | A + 1 =>
    -- (A+1, 0, 1, 0, E+1). Rule 3 loop for remaining A+1 steps.
    apply stepStar_trans (rule3_loop A 1 (E + 1))
    -- (0, 0, A+2, 0, E+A+2)
    rw [show 1 + A + 1 = A + 2 from by ring,
        show E + 1 + A + 1 = E + A + 2 from by ring]
    -- Rule 4 loop
    rw [show E + A + 2 = (E + A + 1) + 1 from by ring]
    apply stepStar_trans (rule4_loop (E + A + 1) (A + 2) 0)
    rw [show 0 + (E + A + 1) + 1 = E + A + 2 from by ring]
    -- (0, 0, A+2, E+A+2, 0)
    -- Phase 3a: rule5 + rule1
    rw [show A + 2 = (A + 1) + 1 from by ring,
        show E + A + 2 = (E + A + 1) + 1 from by ring]
    step fm; step fm
    -- (4, 0, A+1, E+A+1, 0)
    -- Phase 3b: rule21_loop with c = A, g = E, a = 3, e = 0
    -- Need: (3+1, 0, A+1, E+A+1, 0)
    rw [show E + A + 1 = E + A + 1 from rfl]
    apply stepStar_trans (rule21_loop A 3 E 0)
    -- (3+3*A+4, 0, 0, E, 0+A+1) = (3A+7, 0, 0, E, A+1)
    rw [show 3 + 3 * A + 4 = 3 * A + 7 from by ring,
        show 0 + A + 1 = A + 1 from by ring]
    -- Now at (3A+7, 0, 0, E, A+1)
    match E with
    | 0 =>
      -- (3A+7, 0, 0, 0, A+1). Target: (3*(A+1)+4, ..., (A+1)) = (3A+7, ..., A+1). Done.
      ring_nf; finish
    | E + 1 =>
      -- hle : E + 1 + 1 ≤ A + 1 + 1, i.e., E + 1 ≤ A + 1, i.e., E ≤ A
      -- Phase 3c: rule2_loop E.
      -- Need form: (a+d+1, b, 0, d+1, e)
      -- (3A+7, 0, 0, E+1, A+1) = ((3A+5-E)+(E+1)+1... hmm no.
      -- rule2_loop d a b e: (a+d+1, b, 0, d+1, e) ->* (a, b+d+1, 0, 0, e+d+1)
      -- d = E, a = 3A+7-(E+1) = 3A+6-E, b = 0, e = A+1
      -- (3A+6-E+E+1, 0, 0, E+1, A+1) = (3A+7, 0, 0, E+1, A+1). Good.
      -- But 3A+6-E uses natural subtraction. Since E ≤ A, 3A+6-E ≥ 2A+6 > 0.
      -- In Lean: we need `3*A+6-E` but omega should handle the rewrite.
      rw [show 3 * A + 7 = (3 * A + 6 - E) + E + 1 from by omega]
      apply stepStar_trans (rule2_loop E (3 * A + 6 - E) 0 (A + 1))
      -- (3A+6-E, E+1, 0, 0, A+1+E+1) = (3A+6-E, E+1, 0, 0, A+E+2)
      rw [show 0 + E + 1 = E + 1 from by ring,
          show A + 1 + E + 1 = A + E + 2 from by ring]
      -- Phase 3d: rule31_loop E.
      -- Need form: (a+1, b+1, 0, 0, e)
      -- (3A+6-E, E+1, 0, 0, A+E+2) with a = 3A+5-E, b = E, e = A+E+2
      -- Need 3A+6-E >= 1, i.e., 3A+5 >= E. Since E ≤ A, yes.
      rw [show 3 * A + 6 - E = (3 * A + 5 - E) + 1 from by omega]
      apply stepStar_trans (rule31_loop E (3 * A + 5 - E) (A + E + 2))
      -- Result: (3A+5-E+3E+4, 0, 0, 0, A+E+2+E+1) = (3A+2E+9, 0, 0, 0, A+2E+3)
      -- Target: (3*(A+1)+2*(E+1)+4, 0, 0, 0, (A+1)+2*(E+1)) = (3A+2E+9, 0, 0, 0, A+2E+3)
      have h1 : 3 * A + 5 - E + 3 * E + 4 = 3 * (A + 1) + 2 * (E + 1) + 4 := by omega
      have h2 : A + E + 2 + E + 1 = (A + 1) + 2 * (E + 1) := by omega
      rw [h1, h2]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩)
  · exists 0
  apply progress_nonhalt (fun c => ∃ A E, E ≤ A ∧ c = (⟨A + 1, 0, 0, 0, E⟩ : Q))
  · intro c ⟨A, E, hle, hc⟩
    refine ⟨⟨3 * A + 2 * E + 4, 0, 0, 0, A + 2 * E⟩,
            ⟨3 * A + 2 * E + 3, A + 2 * E, ?_, rfl⟩, ?_⟩
    · omega
    · rw [hc]; exact main_trans A E hle
  · exact ⟨0, 0, le_refl 0, rfl⟩

end Sz22_2003_unofficial_321
