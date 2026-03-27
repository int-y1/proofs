import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #265: [14/15, 1/77, 9/7, 11/9, 875/2]

Vector representation:
```
 1 -1 -1  1  0
 0  0  0 -1 -1
 0  2  0 -1  0
 0 -2  0  0  1
-1  0  3  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_265

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+2, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d+1, e⟩
  | _ => none

theorem r311_chain : ∀ k a c d,
    ⟨a, 0, c + 2 * k, d + 1, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d + k + 1, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; finish
  | succ k ih =>
    intro a c d
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show a + 1 + 1 = a + 2 from by ring,
        show d + 1 + 1 = d + 2 from by ring]
    apply stepStar_trans (ih (a + 2) c (d + 1))
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring,
        show d + 1 + k + 1 = d + (k + 1) + 1 from by ring]; finish

theorem c1_tail (a d : ℕ) : ⟨a, 0, 1, d + 1, 0⟩ [fm]⊢* ⟨a + 1, 3, 0, d, 0⟩ := by
  step fm; step fm; step fm; finish

theorem r3_drain : ∀ d a b,
    ⟨a, b, 0, d, 0⟩ [fm]⊢* ⟨a, b + 2 * d, 0, 0, 0⟩ := by
  intro d; induction d with
  | zero => intro a b; simp; finish
  | succ d ih =>
    intro a b; step fm
    apply stepStar_trans (ih a (b + 2))
    rw [show b + 2 + 2 * d = b + 2 * (d + 1) from by ring]; finish

theorem r4_drain_even : ∀ k a e,
    ⟨a, 2 * k, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; finish
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) = (2 * k) + 1 + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (e + 1))
    rw [show e + 1 + k = e + (k + 1) from by ring]; finish

theorem r4_drain_odd : ∀ k a e,
    ⟨a, 2 * k + 1, 0, 0, e⟩ [fm]⊢* ⟨a, 1, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; finish
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (e + 1))
    rw [show e + 1 + k = e + (k + 1) from by ring]; finish

theorem r52_chain : ∀ k a c,
    ⟨a + k, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; simp; finish
  | succ k ih =>
    intro a c
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (c + 3))
    rw [show c + 3 + 3 * k = c + 3 * (k + 1) from by ring]; finish

-- R5, R1, R2, R2 bridge in the even case.
theorem mid_even (a e : ℕ) : ⟨a + 1, 1, 0, 0, e + 2⟩ [fm]⊢* ⟨a + 1, 0, 2, 0, e⟩ := by
  have h1 : fm ⟨a + 1, 1, 0, 0, e + 2⟩ = some ⟨a, 1, 3, 1, e + 2⟩ := by simp [fm]
  have h2 : fm ⟨a, 1, 3, 1, e + 2⟩ = some ⟨a + 1, 0, 2, 2, e + 2⟩ := by simp [fm]
  have h3 : fm ⟨a + 1, 0, 2, 2, e + 2⟩ = some ⟨a + 1, 0, 2, 1, e + 1⟩ := by simp [fm]
  have h4 : fm ⟨a + 1, 0, 2, 1, e + 1⟩ = some ⟨a + 1, 0, 2, 0, e⟩ := by simp [fm]
  exact ⟨4, by
    show stepNat fm 4 ⟨a + 1, 1, 0, 0, e + 2⟩ = some ⟨a + 1, 0, 2, 0, e⟩
    simp [stepNat, Nat.repeat, Option.bind, h1, h2, h3, h4]⟩

theorem macro_odd (a n : ℕ) :
    ⟨a + 1, 0, 2 * n + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + n + 1, 0, 3 * n + 9, 0, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 2 * n + 1, 0, 0⟩ = some ⟨a, 0, 2 * n + 4, 1, 0⟩; rfl
  rw [show 2 * n + 4 = 0 + 2 * (n + 2) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r311_chain (n + 2) a 0 0)
  rw [show a + 2 * (n + 2) = a + 2 * n + 4 from by ring,
      show 0 + (n + 2) + 1 = n + 3 from by ring]
  apply stepStar_trans (r3_drain (n + 3) (a + 2 * n + 4) 0)
  rw [show 0 + 2 * (n + 3) = 2 * (n + 3) from by ring]
  apply stepStar_trans (r4_drain_even (n + 3) (a + 2 * n + 4) 0)
  rw [show 0 + (n + 3) = n + 3 from by ring,
      show a + 2 * n + 4 = (a + n + 1) + (n + 3) from by ring]
  apply stepStar_trans (r52_chain (n + 3) (a + n + 1) 0)
  rw [show 0 + 3 * (n + 3) = 3 * n + 9 from by ring]; finish

theorem macro_even (a n : ℕ) :
    ⟨a + 1, 0, 2 * n, 0, 0⟩ [fm]⊢⁺ ⟨a + n + 3, 0, 3 * n + 2, 0, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 2 * n, 0, 0⟩ = some ⟨a, 0, 2 * n + 3, 1, 0⟩; rfl
  rw [show 2 * n + 3 = 1 + 2 * (n + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r311_chain (n + 1) a 1 0)
  rw [show a + 2 * (n + 1) = a + 2 * n + 2 from by ring,
      show 0 + (n + 1) + 1 = n + 2 from by ring,
      show n + 2 = (n + 1) + 1 from by ring]
  apply stepStar_trans (c1_tail (a + 2 * n + 2) (n + 1))
  apply stepStar_trans (r3_drain (n + 1) (a + 2 * n + 3) 3)
  rw [show 3 + 2 * (n + 1) = 2 * (n + 2) + 1 from by ring]
  apply stepStar_trans (r4_drain_odd (n + 2) (a + 2 * n + 3) 0)
  rw [show 0 + (n + 2) = n + 2 from by ring,
      show a + 2 * n + 3 = (a + 2 * n + 2) + 1 from by ring,
      show n + 2 = n + 2 from rfl]
  apply stepStar_trans (mid_even (a + 2 * n + 2) n)
  rw [show (a + 2 * n + 2) + 1 = (a + n + 3) + n from by ring]
  apply stepStar_trans (r52_chain n (a + n + 3) 2)
  rw [show 2 + 3 * n = 3 * n + 2 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2 + 1, 0, 2, 0, 0⟩)
  · unfold c₀; execute fm 14
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + 1, 0, p.2, 0, 0⟩) (2, 2)
  intro ⟨a, c⟩
  rcases Nat.even_or_odd c with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · -- c = n + n (even)
    refine ⟨(a + n + 2, 3 * n + 2), ?_⟩
    change ⟨a + 1, 0, n + n, 0, 0⟩ [fm]⊢⁺ ⟨a + n + 2 + 1, 0, 3 * n + 2, 0, 0⟩
    rw [show n + n = 2 * n from by ring,
        show a + n + 2 + 1 = a + n + 3 from by ring]
    exact macro_even a n
  · -- c = 2*n+1 (odd)
    refine ⟨(a + n, 3 * n + 9), ?_⟩
    change ⟨a + 1, 0, 2 * n + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + n + 1, 0, 3 * n + 9, 0, 0⟩
    exact macro_odd a n

end Sz22_2003_unofficial_265
