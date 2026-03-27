import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #220: [10/3, 66/35, 1/5, 49/2, 1/77, 5/7]

Vector representation:
```
 1 -1  1  0  0
 1  1 -1 -1  1
 0  0 -1  0  0
-1  0  0  2  0
 0  0  0 -1 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_220

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r2r1_loop : ∀ k a e, ⟨a, 0, 1, k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 1, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; exists 0
  | succ k ih =>
    intro a e
    rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    step fm
    apply stepStar_trans (ih (a + 2) (e + 1))
    ring_nf; finish

theorem r4_drain : ∀ a d e, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * a, e⟩ := by
  intro a; induction a with
  | zero => intro d e; simp; exists 0
  | succ a ih =>
    intro d e
    step fm
    apply stepStar_trans (ih (d + 2) e)
    ring_nf; finish

theorem r5_drain : ∀ k d, ⟨0, 0, 0, d + k, k⟩ [fm]⊢* ⟨0, 0, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intro d; simp; exists 0
  | succ k ih =>
    intro d
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    exact ih d

theorem main_cycle (n : ℕ) : ⟨0, 0, 0, n + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * n + 3, 0⟩ := by
  -- R6: (0,0,0,n+2,0) -> (0,0,1,n+1,0)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, (n + 1) + 1, 0⟩ = some ⟨0, 0, 1, n + 1, 0⟩
    unfold fm; simp
  -- R2/R1 loop: (0,0,1,n+1,0) ->* (2*(n+1), 0, 1, 0, n+1)
  apply stepStar_trans (r2r1_loop (n + 1) 0 0)
  simp only [Nat.zero_add]
  -- R3: (2*(n+1), 0, 1, 0, n+1) -> (2*(n+1), 0, 0, 0, n+1)
  rw [show 2 * (n + 1) = 2 * n + 2 from by ring]
  step fm
  -- R4 drain: (2*n+2, 0, 0, 0, n+1) ->* (0, 0, 0, 2*(2*n+2), n+1) = (0, 0, 0, 4*n+4, n+1)
  apply stepStar_trans (r4_drain (2 * n + 2) 0 (n + 1))
  simp only [Nat.zero_add]
  -- R5 drain: (0, 0, 0, 4*n+4, n+1) = (0, 0, 0, (3*n+3)+(n+1), n+1) ->* (0, 0, 0, 3*n+3, 0)
  rw [show 2 * (2 * n + 2) = (3 * n + 3) + (n + 1) from by ring]
  exact r5_drain (n + 1) (3 * n + 3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by unfold c₀; execute fm 1)
  show ¬halts fm (⟨0, 0, 0, 0 + 2, 0⟩ : Q)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, 0, n + 2, 0⟩) 0
  intro n
  exact ⟨3 * n + 1, by
    show ⟨0, 0, 0, n + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, (3 * n + 1) + 2, 0⟩
    rw [show (3 * n + 1) + 2 = 3 * n + 3 from by ring]
    exact main_cycle n⟩

end Sz22_2003_unofficial_220
