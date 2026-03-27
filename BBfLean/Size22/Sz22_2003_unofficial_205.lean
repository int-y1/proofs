import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #205: [1/6, 35/2, 4/55, 3267/7, 5/3]

Vector representation:
```
-1 -1  0  0  0
-1  0  1  1  0
 2  0 -1  0 -1
 0  3  0 -1  2
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_205

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- 7-step c reduction: (0, 0, c+2, d+1, 0) →* (0, 0, c+1, d+1, 0)
theorem c_drain_one (c d : ℕ) :
    ⟨0, 0, c + 2, d + 1, 0⟩ [fm]⊢* ⟨0, 0, c + 1, d + 1, 0⟩ := by
  step fm
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; step fm
  finish

-- Repeated c drain
theorem c_drain : ∀ k c d,
    ⟨0, 0, c + 1 + k, d + 1, 0⟩ [fm]⊢* ⟨0, 0, c + 1, d + 1, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d
    rw [show c + 1 + (k + 1) = (c + k) + 2 from by ring]
    apply stepStar_trans (c_drain_one (c + k) d)
    rw [show c + k + 1 = c + 1 + k from by ring]
    exact ih c d

-- d drain via repeated rule 4
theorem d_full_drain : ∀ d b e,
    ⟨0, b, 0, d, e⟩ [fm]⊢* ⟨0, b + 3 * d, 0, 0, e + 2 * d⟩ := by
  intro d; induction d with
  | zero => intro b e; simp; exists 0
  | succ d ih =>
    intro b e
    step fm
    apply stepStar_trans (ih (b + 3) (e + 2))
    ring_nf; finish

-- b drain one step: (0, b+3, 0, 0, e+1) →* (0, b, 0, 0, e)
theorem b_drain_one (b e : ℕ) :
    ⟨0, b + 3, 0, 0, e + 1⟩ [fm]⊢* ⟨0, b, 0, 0, e⟩ := by
  rw [show b + 3 = b + 2 + 1 from by ring]
  step fm; step fm; step fm; step fm
  finish

-- Repeated b drain
theorem b_drain : ∀ k b e,
    ⟨0, b + 3 * k, 0, 0, e + k⟩ [fm]⊢* ⟨0, b, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro b e; simp; exists 0
  | succ k ih =>
    intro b e
    rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans (b_drain_one (b + 3 * k) (e + k))
    exact ih b e

-- Build one step: (0, 0, c+1, 2*c, e+1) →* (0, 0, c+2, 2*c+2, e)
theorem build_one (c e : ℕ) :
    ⟨0, 0, c + 1, 2 * c, e + 1⟩ [fm]⊢* ⟨0, 0, c + 2, 2 * c + 2, e⟩ := by
  step fm; step fm; step fm
  ring_nf; finish

-- Repeated build
theorem build : ∀ k c,
    ⟨0, 0, c + 1, 2 * c, k⟩ [fm]⊢* ⟨0, 0, c + k + 1, 2 * (c + k), 0⟩ := by
  intro k; induction k with
  | zero => intro c; simp; exists 0
  | succ k ih =>
    intro c
    apply stepStar_trans (build_one c k)
    rw [show 2 * c + 2 = 2 * (c + 1) from by ring]
    apply stepStar_trans (ih (c + 1))
    ring_nf; finish

-- Main transition: first step makes it stepPlus, rest is stepStar
theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 2, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * n + 3, 4 * n + 4, 0⟩ := by
  -- First step: rule 4 (d = 2n+2 = (2n+1)+1 ≥ 1)
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  -- Now at (0, 3, n+2, 2n+1, 2). Rewrite for rule 3.
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm; step fm; step fm
  -- Now at (0, 1, n+1, 2n+1, 1). Rule 3.
  step fm; step fm; step fm
  -- Now at (0, 0, n+1, 2n+2, 0). C_drain.
  rw [show n + 1 = 0 + 1 + n from by ring,
      show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  apply stepStar_trans (c_drain n 0 (2 * n + 1))
  -- At (0, 0, 1, 2n+2, 0)
  rw [show (0 : ℕ) + 1 = 1 from by ring,
      show 2 * n + 1 + 1 = (2 * n + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm
  -- At (0, 1, 0, 2n+1, 1). d_full_drain.
  apply stepStar_trans (d_full_drain (2 * n + 1) 1 1)
  -- At (0, 1+3(2n+1), 0, 0, 1+2(2n+1)). b_drain.
  rw [show 1 + 2 * (2 * n + 1) = (2 * n + 2) + (2 * n + 1) from by ring]
  apply stepStar_trans (b_drain (2 * n + 1) 1 (2 * n + 2))
  -- At (0, 1, 0, 0, 2n+2). 4 steps.
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm
  -- At (0, 0, 2, 2, 2n+1). Build.
  change ⟨0, 0, 1 + 1, 2 * 1, 2 * n + 1⟩ [fm]⊢* ⟨0, 0, 2 * n + 3, 4 * n + 4, 0⟩
  apply stepStar_trans (build (2 * n + 1) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 4, 0⟩) (by unfold c₀; execute fm 32)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 2 * n + 2, 0⟩) 1
  intro n
  refine ⟨2 * n + 1, ?_⟩
  show ⟨0, 0, n + 2, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, (2 * n + 1) + 2, 2 * (2 * n + 1) + 2, 0⟩
  rw [show (2 * n + 1) + 2 = 2 * n + 3 from by ring,
      show 2 * (2 * n + 1) + 2 = 4 * n + 4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_205
