import BBfLean.FM

/-!
# sz22_2003_unofficial #317: [154/15, 3/7, 1/3, 125/2, 1/55, 3/5]

Vector representation:
```
 1 -1 -1  1  1
 0  1  0 -1  0
 0 -1  0  0  0
-1  0  3  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_317

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1+R2 chain: (k, 1, c, 0, k) ->* (k+c, 1, 0, 0, k+c) when c >= 0
-- Each iteration: R1 then R2
-- (k, 1, c+1, 0, k) -> (k+1, 0, c, 1, k+1) -> (k+1, 1, c, 0, k+1)
theorem r1r2_chain : ∀ c k, ⟨k, 1, c, 0, k⟩ [fm]⊢* ⟨k+c, 1, 0, 0, k+c⟩ := by
  intro c; induction' c with c ih <;> intro k
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (k+1))
    show ⟨k + 1 + c, 1, 0, 0, k + 1 + c⟩ [fm]⊢* ⟨k + (c + 1), 1, 0, 0, k + (c + 1)⟩
    have : k + 1 + c = k + (c + 1) := by omega
    rw [this]; finish

-- R4 chain: (a, 0, c, 0, e) ->* (0, 0, c+3*a, 0, e)
theorem r4_chain : ∀ a c e, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+3*a, 0, e⟩ := by
  intro a; induction' a with a ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c+3) e)
    show ⟨0, 0, c + 3 + 3 * a, 0, e⟩ [fm]⊢* ⟨0, 0, c + 3 * (a + 1), 0, e⟩
    have : c + 3 + 3 * a = c + 3 * (a + 1) := by omega
    rw [this]; finish

-- R5 chain: (0, 0, c+e, 0, e) ->* (0, 0, c, 0, 0)
theorem r5_chain : ∀ e c, ⟨0, 0, c+e, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro e; induction' e with e ih <;> intro c
  · exists 0
  · step fm
    apply stepStar_trans (ih c)
    show ⟨0, 0, c, 0, 0⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩
    finish

-- Main transition: (0, 0, c+2, 0, 0) ->+ (0, 0, 2*c+2, 0, 0) for c >= 0
-- Proof: c+2 >= 2, so c' = c+2, gives 2*(c+2)-2 = 2*c+2
theorem main_trans (c : ℕ) : ⟨0, 0, c+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*c+2, 0, 0⟩ := by
  -- Step 1: R6: (0, 0, c+2, 0, 0) -> (0, 1, c+1, 0, 0)
  step fm
  -- Step 2: R1+R2 chain: (0, 1, c+1, 0, 0) ->* (c+1, 1, 0, 0, c+1)
  apply stepStar_trans (r1r2_chain (c+1) 0)
  -- Step 3: R3: (c+1, 1, 0, 0, c+1) -> (c+1, 0, 0, 0, c+1)
  simp only [Nat.zero_add]
  step fm
  -- Step 4: R4 chain: (c+1, 0, 0, 0, c+1) ->* (0, 0, 3*(c+1), 0, c+1)
  apply stepStar_trans (r4_chain (c+1) 0 (c+1))
  -- Step 5: R5 chain: (0, 0, 3*(c+1), 0, c+1) ->* (0, 0, 2*(c+1), 0, 0)
  have h := r5_chain (c+1) (2*(c+1))
  have h1 : 2 * (c + 1) + (c + 1) = 0 + 3 * (c + 1) := by omega
  have h2 : 2 * (c + 1) = 2 * c + 2 := by omega
  rw [h1, h2] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, n+3, 0, 0⟩) 0
  intro n
  exists 2*n+1
  show ⟨0, 0, n + 3, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, (2 * n + 1) + 3, 0, 0⟩
  have h := main_trans (n+1)
  have h1 : n + 1 + 2 = n + 3 := by omega
  have h2 : 2 * (n + 1) + 2 = (2 * n + 1) + 3 := by omega
  rw [h1, h2] at h; exact h

end Sz22_2003_unofficial_317
