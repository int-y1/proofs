import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #212: [1/6, 77/15, 99/7, 4/11, 75/2]

Vector representation:
```
-1 -1  0  0  0
 0 -1 -1  1  1
 0  2  0 -1  1
 2  0  0  0 -1
-1  1  2  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_212

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+2, d, e⟩
  | _ => none

-- 3-step cd drain: (0, 0, c+2, d+1, e) →* (0, 0, c, d+2, e+3)
theorem cd_drain_one (c d e : ℕ) :
    ⟨0, 0, c + 2, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 2, e + 3⟩ := by
  step fm
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm; step fm
  ring_nf; finish

-- Repeated cd drain: (0, 0, c+2k, d+1, e) →* (0, 0, c, d+k+1, e+3k)
theorem cd_drain : ∀ k c d e,
    ⟨0, 0, c + 2 * k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + k + 1, e + 3 * k⟩ := by
  intro k; induction k with
  | zero => intro c d e; simp; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    apply stepStar_trans (cd_drain_one (c + 2 * k) d e)
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih c (d + 1) (e + 3))
    ring_nf; finish

-- d drain: (0, b, 0, d, e) →* (0, b + 2*d, 0, 0, e + d)
theorem d_drain : ∀ d b e,
    ⟨0, b, 0, d, e⟩ [fm]⊢* ⟨0, b + 2 * d, 0, 0, e + d⟩ := by
  intro d; induction d with
  | zero => intro b e; simp; exists 0
  | succ d ih =>
    intro b e
    step fm
    apply stepStar_trans (ih (b + 2) (e + 1))
    ring_nf; finish

-- be drain one round: (0, b+2, 0, 0, e+1) →* (0, b, 0, 0, e)
theorem be_drain_one (b e : ℕ) :
    ⟨0, b + 2, 0, 0, e + 1⟩ [fm]⊢* ⟨0, b, 0, 0, e⟩ := by
  step fm
  rw [show b + 2 = (b + 1) + 1 from by ring]
  step fm; step fm
  finish

-- Repeated be drain: (0, b + 2*k, 0, 0, e + k) →* (0, b, 0, 0, e)
theorem be_drain : ∀ k b e,
    ⟨0, b + 2 * k, 0, 0, e + k⟩ [fm]⊢* ⟨0, b, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro b e; simp; exists 0
  | succ k ih =>
    intro b e
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans (be_drain_one (b + 2 * k) (e + k))
    exact ih b e

-- e to a: (a, 0, 0, 0, e) →* (a + 2*e, 0, 0, 0, 0)
theorem e_to_a : ∀ e a,
    ⟨a, 0, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * e, 0, 0, 0, 0⟩ := by
  intro e; induction e with
  | zero => intro a; simp; exists 0
  | succ e ih =>
    intro a
    step fm
    apply stepStar_trans (ih (a + 2))
    ring_nf; finish

-- a to c one pair: (a+2, 0, c, 0, 0) →* (a, 0, c+2, 0, 0)
theorem a_to_c_one (a c : ℕ) :
    ⟨a + 2, 0, c, 0, 0⟩ [fm]⊢* ⟨a, 0, c + 2, 0, 0⟩ := by
  rw [show a + 2 = (a + 1) + 1 from by ring]
  step fm; step fm
  finish

-- Repeated a to c: (a + 2*k, 0, c, 0, 0) →* (a, 0, c + 2*k, 0, 0)
theorem a_to_c : ∀ k a c,
    ⟨a + 2 * k, 0, c, 0, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; simp; exists 0
  | succ k ih =>
    intro a c
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring]
    apply stepStar_trans (a_to_c_one (a + 2 * k) c)
    apply stepStar_trans (ih a (c + 2))
    ring_nf; finish

-- Main transition: (1, 0, 2*m, 0, 0) →⁺ (1, 0, 6*m + 4, 0, 0)
theorem main_trans (m : ℕ) :
    ⟨1, 0, 2 * m, 0, 0⟩ [fm]⊢⁺ ⟨1, 0, 6 * m + 4, 0, 0⟩ := by
  -- rule5: (1, 0, 2m, 0, 0) → (0, 1, 2m+2, 0, 0)
  step fm
  -- rule2: (0, 1, 2m+2, 0, 0) → (0, 0, 2m+1, 1, 1)
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm
  -- cd drain m steps: (0, 0, 2m+1, 1, 1) →* (0, 0, 1, m+1, 3m+1)
  rw [show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (cd_drain m 1 0 1)
  -- At (0, 0, 1, m+1, 3m+1). Partial drain: rule3 then rule2.
  rw [show (0 : ℕ) + m + 1 = m + 1 from by ring,
      show 1 + 3 * m = 3 * m + 1 from by ring,
      show m + 1 = m + 1 from rfl]
  step fm
  -- At (0, 2, 1, m, 3m+2)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  -- At (0, 1, 0, m+1, 3m+3)
  -- d drain: (0, 1, 0, m+1, 3m+3) →* (0, 1+2*(m+1), 0, 0, 3m+3+(m+1))
  apply stepStar_trans (d_drain (m + 1) 1 (3 * m + 3))
  -- At (0, 2m+3, 0, 0, 4m+4)
  -- be drain: (0, 2m+3, 0, 0, 4m+4) = (0, 1+2*(m+1), 0, 0, (3m+3)+(m+1))
  rw [show 1 + 2 * (m + 1) = 1 + 2 * (m + 1) from rfl,
      show 3 * m + 3 + (m + 1) = (3 * m + 3) + (m + 1) from rfl]
  apply stepStar_trans (be_drain (m + 1) 1 (3 * m + 3))
  -- At (0, 1, 0, 0, 3m+3). Tail: rule4, rule1.
  rw [show 3 * m + 3 = (3 * m + 2) + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- At (1, 0, 0, 0, 3m+2). e_to_a.
  apply stepStar_trans (e_to_a (3 * m + 2) 1)
  -- At (1+2*(3m+2), 0, 0, 0, 0) = (6m+5, 0, 0, 0, 0). a_to_c.
  rw [show 1 + 2 * (3 * m + 2) = 1 + 2 * (3 * m + 2) from rfl]
  apply stepStar_trans (a_to_c (3 * m + 2) 1 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by unfold c₀; exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 2 * n, 0, 0⟩) 0
  intro n
  refine ⟨3 * n + 2, ?_⟩
  show ⟨1, 0, 2 * n, 0, 0⟩ [fm]⊢⁺ ⟨1, 0, 2 * (3 * n + 2), 0, 0⟩
  rw [show 2 * (3 * n + 2) = 6 * n + 4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_212
