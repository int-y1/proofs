import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #280: [14/15, 3993/2, 1/3, 5/11, 1/35, 3/5]

Vector representation:
```
 1 -1 -1  1  0
-1  1  0  0  3
 0 -1  0  0  0
 0  0  1  0 -1
 0  0 -1 -1  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_280

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+3⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: e → c
theorem e_to_c : ∀ k c d e, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c+k, d, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R5 repeated: c,d cancel
theorem cd_cancel : ∀ k c d, ⟨0, 0, c+k, d+k, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R1+R2 loop: (0,1,c+k,d,e) →* (0,1,c,d+k,e+3k)
theorem r1r2_loop : ∀ k c d e, ⟨0, 1, c+k, d, e⟩ [fm]⊢* ⟨(0 : ℕ), 1, c, d+k, e+3*k⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Main transition: (0,0,0,d+1,3*(d+1)) ⊢⁺ (0,0,0,2*d+1,3*(2*d+1))
theorem main_trans (d : ℕ) : ⟨0, 0, 0, d+1, 3*(d+1)⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*d+1, 3*(2*d+1)⟩ := by
  -- Phase 1 (R4): (0,0,0,d+1,3(d+1)) →* (0,0,3(d+1),d+1,0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3*(d+1), d+1, 0⟩)
  · have h := e_to_c (3*(d+1)) 0 (d+1) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2 (R5): (0,0,3(d+1),d+1,0) →* (0,0,2d+2,0,0)
  -- cd_cancel (d+1) (2d+2) 0: (0,0,(2d+2)+(d+1),0+(d+1),0) →* (0,0,2d+2,0,0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2*d+2, 0, 0⟩)
  · have h := cd_cancel (d+1) (2*d+2) 0
    rw [show 2 * d + 2 + (d + 1) = 3 * (d + 1) from by ring,
        show 0 + (d + 1) = d + 1 from by ring] at h
    exact h
  -- Phase 3 (R6): (0,0,2d+2,0,0) → (0,1,2d+1,0,0)
  -- Phase 4 (R1,R2 loop): (0,1,2d+1,0,0) →* (0,1,0,2d+1,3*(2d+1))
  -- Phase 5 (R3): (0,1,0,2d+1,3*(2d+1)) → (0,0,0,2d+1,3*(2d+1))
  -- Combined: (0,0,2d+2,0,0) ⊢⁺ (0,0,0,2d+1,3*(2d+1))
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 2*d+1, 0, 0⟩)
  · rw [show 2 * d + 2 = (2 * d + 1) + 1 from by ring]; simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 1, 0, 2*d+1, 3*(2*d+1)⟩)
  · have h := r1r2_loop (2*d+1) 0 0 0
    simp only [Nat.zero_add] at h; exact h
  · step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 6⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d+2, 3*(d+2)⟩) 0
  intro d
  refine ⟨2*d+1, ?_⟩
  show ⟨0, 0, 0, d + 2, 3 * (d + 2)⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 1 + 2, 3 * (2 * d + 1 + 2)⟩
  rw [show d + 2 = (d + 1) + 1 from by ring,
      show 2 * d + 1 + 2 = 2 * (d + 1) + 1 from by ring,
      show 3 * ((d + 1) + 1) = 3 * (d + 1 + 1) from by ring,
      show 3 * (2 * (d + 1) + 1) = 3 * (2 * (d + 1) + 1) from by ring]
  exact main_trans (d + 1)

end Sz22_2003_unofficial_280
