import BBfLean.FM

/-!
# sz22_2003_unofficial #589: [35/6, 121/2, 28/55, 3/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  1 -1
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_589

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: (0, b, 0, d+k, e) →* (0, b+k, 0, d, e)
theorem d_to_b : ∀ k b, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b; exists 0
  | succ k ih =>
    intro b; rw [show d + (k + 1) = (d + k) + 1 from by omega]
    step fm
    have h := ih (b + 1)
    rw [show (b + 1) + k = b + (k + 1) from by omega] at h
    exact h

-- R1,R1,R3 chain: (2, 2*j, c, d, e+j) →* (2, 0, c+j, d+3*j, e)
theorem r1r1r3_chain : ∀ j, ∀ c d e, ⟨2, 2 * j, c, d, e + j⟩ [fm]⊢*
    ⟨2, 0, c + j, d + 3 * j, e⟩ := by
  intro j; induction j with
  | zero => intro c d e; exists 0
  | succ j ih =>
    intro c d e
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by omega,
        show e + (j + 1) = (e + j) + 1 from by omega]
    step fm; step fm; step fm
    have h := ih (c + 1) (d + 1 + 1 + 1) e
    rw [show (c + 1) + j = c + (j + 1) from by omega,
        show (d + 1 + 1 + 1) + 3 * j = d + 3 * (j + 1) from by omega] at h
    exact h

-- R2,R2,R3 drain: (2, 0, c+k, d, e) →* (2, 0, c, d+k, e+3*k)
theorem r2r2r3_chain : ∀ k, ∀ d e, ⟨2, 0, c + k, d, e⟩ [fm]⊢*
    ⟨2, 0, c, d + k, e + 3 * k⟩ := by
  intro k; induction k with
  | zero => intro d e; exists 0
  | succ k ih =>
    intro d e
    rw [show c + (k + 1) = (c + k) + 1 from by omega]
    step fm; step fm; step fm
    have h := ih (d + 1) (e + 1 + 2)
    rw [show (d + 1) + k = d + (k + 1) from by omega,
        show (e + 1 + 2) + 3 * k = e + 3 * (k + 1) from by omega] at h
    exact h

-- Main transition: (0, 0, 0, 2m+1, 2m+3) →⁺ (0, 0, 0, 4m+3, 4m+5)
theorem main_trans : ⟨0, 0, 0, 2 * m + 1, 2 * m + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + 3, 4 * m + 5⟩ := by
  -- Phase 1: R4 chain → (0, 2m+1, 0, 0, 2m+3)
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by omega]
  apply stepStar_stepPlus_stepPlus (d_to_b (2 * m + 1) 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5, R1, R3 → (2, 2m, 0, 3, m+m)
  rw [show 2 * m + 3 = (2 * m + 2) + 1 from by omega]
  step fm
  rw [show 2 * m + 1 = (2 * m) + 1 from by omega]
  step fm
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by omega]
  step fm
  -- State: (2, 2*m, 0, 3, 2*m+1)
  -- Phase 3: R1,R1,R3 chain → (2, 0, m, 3m+3, m+1)
  rw [show 2 * m + 1 = (m + 1) + m from by omega]
  have h3 := r1r1r3_chain m 0 3 (m + 1)
  rw [show 0 + m = m from by omega,
      show 3 + 3 * m = 3 * m + 3 from by omega] at h3
  apply stepStar_trans h3
  -- Phase 4: R2,R2,R3 drain → (2, 0, 0, 4m+3, 4m+1)
  have h4 := @r2r2r3_chain 0 m (3 * m + 3) (m + 1)
  simp only [Nat.zero_add] at h4
  rw [show (3 * m + 3) + m = 4 * m + 3 from by omega,
      show (m + 1) + 3 * m = 4 * m + 1 from by omega] at h4
  apply stepStar_trans h4
  -- Phase 5: R2,R2 → (0, 0, 0, 4m+3, 4m+5)
  step fm; step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨0, 0, 0, 2 * m + 1, 2 * m + 3⟩) 0
  intro m
  refine ⟨2 * m + 1, ?_⟩
  show ⟨0, 0, 0, 2 * m + 1, 2 * m + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * (2 * m + 1) + 1, 2 * (2 * m + 1) + 3⟩
  rw [show 2 * (2 * m + 1) + 1 = 4 * m + 3 from by omega,
      show 2 * (2 * m + 1) + 3 = 4 * m + 5 from by omega]
  exact main_trans

end Sz22_2003_unofficial_589
