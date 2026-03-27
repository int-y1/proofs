import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #496: [28/15, 3/22, 25/2, 121/7, 21/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  2
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_496

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

-- R2+R1 interleaved: each pair consumes 1 from c and 1 from e, adds 1 to a and d
theorem r2r1_chain : ∀ k, ∀ a c d e, ⟨a+1, 0, c+k, d, e+k⟩ [fm]⊢* ⟨a+k+1, 0, c, d+k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  -- State: (a+1, 0, c+(k+1), d, e+(k+1))
  -- Rewrite e+(k+1) to show it matches e'+1
  rw [show e + (k + 1) = e + k + 1 from by ring]
  step fm  -- R2 fires (a+1 matches a'+1, e+k+1 matches e'+1): (a, 1, c+(k+1), d, e+k)
  rw [show c + (k + 1) = c + k + 1 from by ring]
  step fm  -- R1 fires (b=1, c+k+1 matches c'+1): (a+2, 0, c+k, d+1, e+k)
  apply stepStar_trans (ih _ _ _ _); ring_nf; finish

theorem r2_drain : ∀ k, ∀ a b d e, ⟨a+k, b, 0, d, e+k⟩ [fm]⊢* ⟨a, b+k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = a + k + 1 from by ring,
      show e + (k + 1) = e + k + 1 from by ring]
  step fm  -- R2: (a+k, b+1, 0, d, e+k)
  apply stepStar_trans (ih _ _ _ _); ring_nf; finish

-- Each round: R3, R1, R1 consumes 2 from b, adds 3 to a and 2 to d
theorem r3r1r1_chain : ∀ k, ∀ a d,
    ⟨a+1, 2*(k+1), 0, d, 0⟩ [fm]⊢* ⟨a+3*(k+1)+1, 0, 0, d+2*(k+1), 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · -- Single round
    step fm; step fm; step fm; ring_nf; finish
  · -- (k+2) rounds: do one round, then apply IH
    rw [show 2 * (k + 1 + 1) = 2 * (k + 1) + 2 from by ring]
    step fm  -- R3: (a, 2*(k+1)+2, 2, d, 0)
    rw [show 2 * (k + 1) + 2 = 2 * (k + 1) + 1 + 1 from by ring]
    step fm  -- R1: (a+2, 2*(k+1)+1, 1, d+1, 0). Need b≥1 ✓, c=1≥1 ✓
    rw [show 2 * (k + 1) + 1 = 2 * (k + 1) + 0 + 1 from by ring]
    step fm  -- R1: (a+4, 2*(k+1), 0, d+2, 0)
    apply stepStar_trans (ih _ _); ring_nf; finish

theorem main_trans (h g : ℕ) :
    ⟨h+g+2, 0, 0, h+2*g+2, 0⟩ [fm]⊢⁺ ⟨2*h+3*g+5, 0, 0, 2*h+4*g+6, 0⟩ := by
  -- Phase 1: R3 chain: (h+g+2, 0, 0, h+2*g+2, 0) ->* (0, 0, 2*(h+g+2), h+2*g+2, 0)
  apply stepStar_stepPlus_stepPlus
  · have h1 := a_to_c (h+g+2) 0 0 (h+2*g+2)
    simp only [Nat.zero_add] at h1; exact h1
  -- Phase 2: R4 chain: ->* (0, 0, 2*(h+g+2), 0, 2*(h+2*g+2))
  apply stepStar_stepPlus_stepPlus
  · have h2 := d_to_e (h+2*g+2) (2*(h+g+2)) 0 0
    simp only [Nat.zero_add] at h2; exact h2
  -- Phase 3: R5 + R1 opening
  -- State: (0, 0, 2*(h+g+2), 0, 2*(h+2*g+2))
  -- R5: (0, 1, 2*(h+g+2)-1, 1, 2*(h+2*g+2))
  -- R1: (2, 0, 2*(h+g+2)-2, 2, 2*(h+2*g+2))
  rw [show 2 * (h + g + 2) = (2*h + 2*g + 3) + 1 from by ring]
  step fm  -- R5: (0, 1, 2*h+2*g+3, 1, 2*(h+2*g+2))
  rw [show 2 * h + 2 * g + 3 = (2*h + 2*g + 2) + 1 from by ring]
  step fm  -- R1: (2, 0, 2*h+2*g+2, 2, 2*(h+2*g+2))
  -- Phase 4: R2+R1 chain × (2*h+2*g+2)
  -- (2, 0, 2*h+2*g+2, 2, 2*(h+2*g+2))
  -- = (1+1, 0, 0+(2*h+2*g+2), 2, (2*g+2)+(2*h+2*g+2))
  apply stepStar_trans
  · have h4 := r2r1_chain (2*h+2*g+2) 1 0 2 (2*g+2)
    simp only [Nat.zero_add] at h4
    rw [show 2 * g + 2 + (2 * h + 2 * g + 2) = 2 * (h + 2 * g + 2) from by ring,
        show 1 + (2 * h + 2 * g + 2) + 1 = 2 * h + 2 * g + 4 from by ring,
        show 2 + (2 * h + 2 * g + 2) = 2 * h + 2 * g + 4 from by ring] at h4
    exact h4
  -- State: (2*h+2*g+4, 0, 0, 2*h+2*g+4, 2*g+2)
  -- Phase 5: R2 drain × (2*g+2)
  -- (2*h+2*g+4, 0, 0, 2*h+2*g+4, 2*g+2)
  -- = ((2*h+2)+(2*g+2), 0, 0, 2*h+2*g+4, 0+(2*g+2))
  apply stepStar_trans
  · have h5 := r2_drain (2*g+2) (2*h+2) 0 (2*h+2*g+4) 0
    simp only [Nat.zero_add] at h5
    rw [show 2 * h + 2 + (2 * g + 2) = 2 * h + 2 * g + 4 from by ring] at h5
    exact h5
  -- State: (2*h+2, 2*g+2, 0, 2*h+2*g+4, 0)
  -- Phase 6: R3+R1+R1 chain × (g+1) rounds
  -- = ((2*h+1)+1, 2*(g+1), 0, 2*h+2*g+4, 0)
  -- Result: ((2*h+1)+3*(g+1)+1, 0, 0, (2*h+2*g+4)+2*(g+1), 0)
  -- = (2*h+3*g+5, 0, 0, 2*h+4*g+6, 0) ✓
  have h6 := r3r1r1_chain g (2*h+1) (2*h+2*g+4)
  rw [show 2 * h + 1 + 1 = 2 * h + 2 from by ring,
      show 2 * (g + 1) = 2 * g + 2 from by ring,
      show 2 * h + 1 + 3 * (g + 1) + 1 = 2 * h + 3 * g + 5 from by ring] at h6
  rw [show 2 * h + 4 * g + 6 = 2 * h + 2 * g + 4 + (2 * g + 2) from by ring]
  exact h6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨h, g⟩ ↦ ⟨h+g+2, 0, 0, h+2*g+2, 0⟩) ⟨0, 0⟩
  intro ⟨h, g⟩
  refine ⟨⟨2*h+2*g+2, g+1⟩, ?_⟩
  show ⟨h+g+2, 0, 0, h+2*g+2, 0⟩ [fm]⊢⁺ ⟨(2*h+2*g+2)+(g+1)+2, 0, 0, (2*h+2*g+2)+2*(g+1)+2, 0⟩
  rw [show (2*h+2*g+2)+(g+1)+2 = 2*h+3*g+5 from by ring,
      show (2*h+2*g+2)+2*(g+1)+2 = 2*h+4*g+6 from by ring]
  exact main_trans h g

end Sz22_2003_unofficial_496
