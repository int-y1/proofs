import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1518: [7/15, 99/14, 4/3, 5/11, 363/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  1
 2 -1  0  0  0
 0  0  1  0 -1
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1518

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R4: transfer e to c
theorem e_to_c : ∀ k, ∀ a c, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c; exists 0
  · intro a c; rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih a (c + 1)); ring_nf; finish

-- R2R1R1 chain
theorem r2r1r1_chain : ∀ k, ∀ a c d e,
    ⟨a + k, 0, c + 2 * k, d + 1, e⟩ [fm]⊢* ⟨a, 0, c, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a c d e; exists 0
  · intro a c d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 1) (e + 1)); ring_nf; finish

-- R2 drain
theorem r2_drain : ∀ k, ∀ a b e,
    ⟨a + k, b, 0, d + k, e⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a b e; exists 0
  · intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2) (e + 1)); ring_nf; finish

-- R3 drain
theorem r3_drain : ∀ k, ∀ a e,
    ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a e; exists 0
  · intro a e
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) e); ring_nf; finish

-- R2R1 partial round: when c=1, do R2 then R1
-- (a+1, 0, 1, d+1, e) -R2-> (a, 2, 1, d, e+1) -R1-> (a, 1, 0, d+1, e+1)
theorem r2_r1_partial : ∀ a d e,
    ⟨a + 1, 0, 1, d + 1, e⟩ [fm]⊢* ⟨a, 1, 0, d + 1, e + 1⟩ := by
  intro a d e
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (step_stepStar (show fm ⟨a + 1, 0, 0 + 1, d + 1, e⟩ = some ⟨a, 2, 0 + 1, d, e + 1⟩ from rfl))
  apply stepStar_trans (step_stepStar (show fm ⟨a, 1 + 1, 0 + 1, d, e + 1⟩ = some ⟨a, 1, 0, d + 1, e + 1⟩ from rfl))
  exists 0

-- Main transition
theorem main_trans (n : ℕ) :
    ⟨n * n + 4 * n + 5, 0, 0, 0, 2 * n + 4⟩ [fm]⊢⁺
    ⟨n * n + 6 * n + 10, 0, 0, 0, 2 * n + 6⟩ := by
  -- Phase 1: R4 x (2n+4): e -> c
  rw [show (2 * n + 4 : ℕ) = 0 + (2 * n + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (2 * n + 4) (n * n + 4 * n + 5) 0 (e := 0))
  rw [show 0 + (2 * n + 4) = 2 * n + 4 from by ring]
  -- State: (n^2+4n+5, 0, 2n+4, 0, 0)
  -- Phase 2: R5
  rw [show n * n + 4 * n + 5 = (n * n + 4 * n + 4) + 1 from by ring]
  step fm
  -- State: (n^2+4n+4, 1, 2n+4, 0, 2)
  -- Phase 3: R1
  rw [show 2 * n + 4 = (2 * n + 3) + 1 from by ring]
  step fm
  -- State: (n^2+4n+4, 0, 2n+3, 1, 2)
  -- Phase 4: R2R1R1 chain x (n+1)
  rw [show n * n + 4 * n + 4 = (n * n + 3 * n + 3) + (n + 1) from by ring,
      show 2 * n + 3 = 1 + 2 * (n + 1) from by ring]
  apply stepStar_trans (r2r1r1_chain (n + 1) (n * n + 3 * n + 3) 1 0 2)
  rw [show 0 + (n + 1) + 1 = n + 2 from by ring,
      show 2 + (n + 1) = n + 3 from by ring]
  -- State: (n^2+3n+3, 0, 1, n+2, n+3)
  -- Phase 5: R2+R1 partial round
  rw [show n * n + 3 * n + 3 = (n * n + 3 * n + 2) + 1 from by ring,
      show (n + 2 : ℕ) = (n + 1) + 1 from by ring]
  apply stepStar_trans (r2_r1_partial (n * n + 3 * n + 2) (n + 1) (n + 3))
  -- State: (n^2+3n+2, 1, 0, n+2, n+4)
  rw [show n + 3 + 1 = n + 4 from by ring,
      show n + 1 + 1 = n + 2 from by ring]
  -- Phase 6: R2 drain x (n+2)
  -- State: (n^2+3n+2, 1, 0, n+2, n+4)
  -- r2_drain needs (a+k, b, 0, d+k, e) form
  -- a = n^2+2n, k = n+2, b = 1, d = 0, e = n+4
  have h6 := r2_drain (n + 2) (n * n + 2 * n) 1 (n + 4) (d := 0)
  rw [show n * n + 2 * n + (n + 2) = n * n + 3 * n + 2 from by ring,
      show 0 + (n + 2) = n + 2 from by ring] at h6
  apply stepStar_trans h6
  rw [show 1 + 2 * (n + 2) = 2 * n + 5 from by ring,
      show n + 4 + (n + 2) = 2 * n + 6 from by ring]
  -- State: (n^2+2n, 2n+5, 0, 0, 2n+6)
  -- Phase 7: R3 drain x (2n+5)
  rw [show (2 * n + 5 : ℕ) = 0 + (2 * n + 5) from by ring]
  apply stepStar_trans (r3_drain (2 * n + 5) (n * n + 2 * n) (2 * n + 6) (b := 0))
  rw [show n * n + 2 * n + 2 * (2 * n + 5) = n * n + 6 * n + 10 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 4⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n * n + 4 * n + 5, 0, 0, 0, 2 * n + 4⟩) 0
  intro n; exact ⟨n + 1, by
    rw [show (n + 1) * (n + 1) + 4 * (n + 1) + 5 = n * n + 6 * n + 10 from by ring,
        show 2 * (n + 1) + 4 = 2 * n + 6 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_1518
