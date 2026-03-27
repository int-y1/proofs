import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #443: [27/35, 65/33, 182/3, 11/13, 3/2]

Vector representation:
```
 0  3 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  1  0  1
 0  0  0  0  1 -1
-1  1  0  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_443

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+3, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

theorem f_to_e : ∀ j a d e f,
    ⟨a, 0, 0, d, e, f + j⟩ [fm]⊢* (⟨a, 0, 0, d, e + j, f⟩ : Q) := by
  intro j; induction' j with j ih <;> intro a d e f
  · exists 0
  rw [show f + (j + 1) = (f + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  rw [show (e + 1) + j = e + (j + 1) from by ring]
  finish

theorem inner_loop : ∀ j a b d e f,
    ⟨a, b + 1, 0, d + j, e + j, f⟩ [fm]⊢* (⟨a, b + 2 * j + 1, 0, d, e, f + j⟩ : Q) := by
  intro j; induction' j with j ih <;> intro a b d e f
  · exists 0
  rw [show d + (j + 1) = (d + j) + 1 from by ring,
      show e + (j + 1) = (e + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ (b + 2) _ _ _)
  rw [show (b + 2) + 2 * j + 1 = b + 2 * (j + 1) + 1 from by ring,
      show (f + 1) + j = f + (j + 1) from by ring]
  finish

theorem consume_e : ∀ j a b c f,
    ⟨a, b + j, c, 0, j, f⟩ [fm]⊢* (⟨a, b, c + j, 0, 0, f + j⟩ : Q) := by
  intro j; induction' j with j ih <;> intro a b c f
  · exists 0
  rw [show b + (j + 1) = (b + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  rw [show (c + 1) + j = c + (j + 1) from by ring,
      show (f + 1) + j = f + (j + 1) from by ring]
  finish

theorem r3r1_loop : ∀ j a b c f,
    ⟨a, b + 1, c + j, 0, 0, f⟩ [fm]⊢* (⟨a + j, b + 2 * j + 1, c, 0, 0, f + j⟩ : Q) := by
  intro j; induction' j with j ih <;> intro a b c f
  · exists 0
  rw [show c + (j + 1) = (c + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ (b + 2) _ _)
  rw [show (a + 1) + j = a + (j + 1) from by ring,
      show (b + 2) + 2 * j + 1 = b + 2 * (j + 1) + 1 from by ring,
      show (f + 1) + j = f + (j + 1) from by ring]
  finish

theorem r3_chain : ∀ j a b d f,
    ⟨a, b + j, 0, d, 0, f⟩ [fm]⊢* (⟨a + j, b, 0, d + j, 0, f + j⟩ : Q) := by
  intro j; induction' j with j ih <;> intro a b d f
  · exists 0
  rw [show b + (j + 1) = (b + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  rw [show (a + 1) + j = a + (j + 1) from by ring,
      show (d + 1) + j = d + (j + 1) from by ring,
      show (f + 1) + j = f + (j + 1) from by ring]
  finish

-- Main transition.
-- From (a+1, 0, 0, d+1, 0, d+g+1) where g < 2*d+3:
-- Phase A: f_to_e (d+g+1): -> (a+1, 0, 0, d+1, d+g+1, 0)
-- Phase B: rule 5: -> (a, 1, 0, d+1, d+g+1, 0) i.e. (a, 0+1, 0, d+1, d+g+1, 0)
-- Phase C: inner_loop (d+1) with b=0, d'=0, e'=g, f'=0:
--   (a, 0+1, 0, 0+(d+1), g+(d+1), 0) ->* (a, 0+2*(d+1)+1, 0, 0, g, 0+(d+1))
--   = (a, 2*d+3, 0, 0, g, d+1)
-- Phase D: consume_e g with b=(2*d+3-g), c=0, f=(d+1):
--   (a, (2*d+3-g)+g, 0, 0, g, d+1) ->* (a, 2*d+3-g, 0+g, 0, 0, (d+1)+g)
--   = (a, 2*d+3-g, g, 0, 0, d+g+1)
--   Need: 2*d+3-g+g = 2*d+3. Since g < 2*d+3, 2*d+3-g >= 1.
-- Phase E: r3r1_loop g with b=(2*d+3-g-1), c=0, f=(d+g+1):
--   Need b+1 = 2*d+3-g, so b = 2*d+2-g. Need b >= 0, i.e., g <= 2*d+2.
--   (a, (2*d+2-g)+1, 0+g, 0, 0, d+g+1) ->* (a+g, (2*d+2-g)+2*g+1, 0, 0, 0, (d+g+1)+g)
--   = (a+g, 2*d+g+3, 0, 0, 0, d+2*g+1)
-- Phase F: r3_chain (2*d+g+3) with a'=(a+g), b=0, d'=0, f'=(d+2*g+1):
--   (a+g, 0+(2*d+g+3), 0, 0, 0, d+2*g+1) ->* (a+g+(2*d+g+3), 0, 0, 0+(2*d+g+3), 0, (d+2*g+1)+(2*d+g+3))
--   = (a+2*d+2*g+3, 0, 0, 2*d+g+3, 0, 3*d+3*g+4)
theorem main_trans (a d g : ℕ) (hg : g ≤ 2 * d + 2) :
    ⟨a + 1, 0, 0, d + 1, 0, d + g + 1⟩ [fm]⊢⁺
      (⟨a + 2 * d + 2 * g + 3, 0, 0, 2 * d + g + 3, 0, 3 * d + 3 * g + 4⟩ : Q) := by
  -- Phase A
  apply stepStar_stepPlus_stepPlus
  · have h := f_to_e (d + g + 1) (a + 1) (d + 1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase B
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, d + 1, d + g + 1, 0⟩ = some ⟨a, 1, 0, d + 1, d + g + 1, 0⟩; rfl
  -- Phase C
  apply stepStar_trans
  · have h := inner_loop (d + 1) a 0 0 g 0
    rw [show g + (d + 1) = d + g + 1 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- State: (a, 2*d+3, 0, 0, g, d+1)
  -- = (a, (2*d+2-g) + 1 + g, 0, 0, g, d+1) since g ≤ 2*d+2
  -- For consume_e: (a, (2*d+2-g+1)+g, 0, 0, g, d+1) but we need the form (a, b+j, c, 0, j, f)
  -- That is b = 2*d+3-g, j = g: (a, (2*d+3-g)+g, 0, 0, g, d+1)
  -- Phase D
  apply stepStar_trans
  · have h := consume_e g a (2 * d + 3 - g) 0 (d + 1)
    rw [show 2 * d + 3 - g + g = 2 * d + 3 from by omega] at h
    simp only [Nat.zero_add] at h; exact h
  -- State: (a, 2*d+3-g, g, 0, 0, d+1+g)
  -- Phase E: r3r1_loop g
  -- Need: (a, (2*d+3-g-1)+1, 0+g, 0, 0, d+1+g) i.e. b = 2*d+2-g
  apply stepStar_trans
  · have h := r3r1_loop g a (2 * d + 2 - g) 0 (d + 1 + g)
    rw [show 2 * d + 2 - g + 1 = 2 * d + 3 - g from by omega,
        show (0 : ℕ) + g = g from by ring] at h
    exact h
  -- State: (a+g, (2*d+2-g)+2*g+1, 0, 0, 0, d+1+g+g)
  -- Rewrite b-component before applying r3_chain
  rw [show (2 * d + 2 - g) + 2 * g + 1 = 2 * d + g + 3 from by omega]
  -- Phase F: r3_chain (2*d+g+3)
  apply stepStar_trans
  · have h := r3_chain (2 * d + g + 3) (a + g) 0 0 (d + 1 + g + g)
    rw [show (0 : ℕ) + (2 * d + g + 3) = 2 * d + g + 3 from by ring] at h
    exact h
  rw [show a + g + (2 * d + g + 3) = a + 2 * d + 2 * g + 3 from by ring,
      show d + 1 + g + g + (2 * d + g + 3) = 3 * d + 3 * g + 4 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 0, 1⟩) (by execute fm 2)
  refine progress_nonhalt (fm := fm)
    (fun c ↦ ∃ a d g, c = (⟨a + 1, 0, 0, d + 1, 0, d + g + 1⟩ : Q) ∧ g ≤ 2 * d + 2) ?_ ?_
  · intro c ⟨a, d, g, hc, hg⟩
    refine ⟨⟨a + 2 * d + 2 * g + 3, 0, 0, 2 * d + g + 3, 0, 3 * d + 3 * g + 4⟩,
      ⟨a + 2 * d + 2 * g + 2, 2 * d + g + 2, d + 2 * g + 1, ?_, ?_⟩,
      hc ▸ main_trans a d g hg⟩
    · ring_nf
    · omega
  · exact ⟨0, 0, 0, rfl, by omega⟩

end Sz22_2003_unofficial_443
