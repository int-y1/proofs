import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1422: [7/15, 18/77, 484/3, 5/2, 3/5]

Vector representation:
```
 0 -1 -1  1  0
 1  2  0 -1 -1
 2 -1  0  0  2
-1  0  1  0  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1422

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: (a+k, 0, c, 0, e) ⊢* (a, 0, c+k, 0, e)
theorem r4_chain : ∀ k, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [Nat.add_succ a k]
    step fm
    apply stepStar_trans (ih (a := a) (c := c + 1))
    ring_nf; finish

-- R3 chain: (a, k, 0, 0, e) ⊢* (a+2k, 0, 0, 0, e+2k) when d=0
theorem r3_chain : ∀ k, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 2) (e := e + 2))
    ring_nf; finish

-- R2,R1,R1 chain: (n, 0, c+2k, d+1, e+k) ⊢* (n+k, 0, c, d+k+1, e)
theorem r2r1r1_chain : ∀ k, ∀ n c d e,
    ⟨n, 0, c + 2 * k, d + 1, e + k⟩ [fm]⊢* ⟨n + k, 0, c, d + k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro n c d e
  · simp; exists 0
  · rw [show c + 2 * (k + 1) = c + 2 + 2 * k from by ring,
        Nat.add_succ e k]
    step fm
    rw [show c + 2 + 2 * k = (c + 1 + 2 * k) + 1 from by ring]
    step fm
    rw [show c + 1 + 2 * k = (c + 2 * k) + 1 from by ring]
    step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (n + 1) c (d + 1) e)
    ring_nf; finish

-- R2/R3 combo: (a, b, 0, d, e) ⊢* (a+2b+5d, 0, 0, 0, e+2b+3d)
-- Requires: d = 0 or b + e ≥ 1.
theorem r2r3_combo : ∀ d, ∀ a b e, (d = 0 ∨ b + e ≥ 1) →
    ⟨a, b, 0, d, e⟩ [fm]⊢* ⟨a + 2 * b + 5 * d, 0, 0, 0, e + 2 * b + 3 * d⟩ := by
  intro d; induction' d with d ih <;> intro a b e h
  · simp only [Nat.mul_zero, Nat.add_zero]
    exact r3_chain b
  · rcases e with _ | e
    · rcases b with _ | b
      · simp at h
      · step fm
        rw [show (2 : ℕ) = 1 + 1 from by ring]
        step fm
        apply stepStar_trans (ih (a + 3) (b + 2) 1 (by omega))
        ring_nf; finish
    · step fm
      apply stepStar_trans (ih (a + 1) (b + 2) e (by omega))
      ring_nf; finish

-- Even case: (2m+2, 0, 0, 0, e+2) ⊢⁺ (6m+5, 0, 0, 0, e+2m+5)
theorem main_trans_even (m e : ℕ) (he : e + 1 ≥ m) :
    ⟨2 * m + 2, 0, 0, 0, e + 2⟩ [fm]⊢⁺ ⟨6 * m + 5, 0, 0, 0, e + 2 * m + 5⟩ := by
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by omega]
  step fm
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by omega]
  apply stepStar_trans (r4_chain (2 * m + 1) (a := 0) (c := 1) (e := e + 2))
  rw [show 1 + (2 * m + 1) = (2 * m + 1) + 1 from by ring]
  step fm
  step fm
  rw [show (2 * m : ℕ) = 0 + 2 * m from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show e + 2 = (e + 2 - m) + m from by omega]
  apply stepStar_trans (r2r1r1_chain m 0 0 0 (e + 2 - m))
  simp only [Nat.zero_add]
  apply stepStar_trans (r2r3_combo (m + 1) m 0 (e + 2 - m) (by omega))
  rw [show m + 2 * 0 + 5 * (m + 1) = 6 * m + 5 from by ring,
      show e + 2 - m + 2 * 0 + 3 * (m + 1) = e + 2 * m + 5 from by omega]
  finish

-- Odd case: (2m+3, 0, 0, 0, e+2) ⊢⁺ (6m+8, 0, 0, 0, e+2m+6)
theorem main_trans_odd (m e : ℕ) (he : e ≥ m) :
    ⟨2 * m + 3, 0, 0, 0, e + 2⟩ [fm]⊢⁺ ⟨6 * m + 8, 0, 0, 0, e + 2 * m + 6⟩ := by
  rw [show 2 * m + 3 = (2 * m + 2) + 1 from by omega]
  step fm
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by omega]
  apply stepStar_trans (r4_chain (2 * m + 2) (a := 0) (c := 1) (e := e + 2))
  rw [show 1 + (2 * m + 2) = (2 * m + 2) + 1 from by ring]
  step fm
  rw [show (2 * m + 2 : ℕ) = (2 * m + 1) + 1 from by ring]
  step fm
  rw [show (2 * m + 1 : ℕ) = 1 + 2 * m from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show e + 2 = (e + 2 - m) + m from by omega]
  apply stepStar_trans (r2r1r1_chain m 0 1 0 (e + 2 - m))
  simp only [Nat.zero_add]
  rw [show e + 2 - m = (e + 1 - m) + 1 from by omega]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  apply stepStar_trans (r2r3_combo (m + 1) (m + 1) 1 (e + 1 - m) (by omega))
  rw [show m + 1 + 2 * 1 + 5 * (m + 1) = 6 * m + 8 from by ring,
      show e + 1 - m + 2 * 1 + 3 * (m + 1) = e + 2 * m + 6 from by omega]
  finish

-- Combined main transition: (a+2, 0, 0, 0, e+2) ⊢⁺ (3a+5, 0, 0, 0, a+e+5)
theorem main_trans (a e : ℕ) (h : 2 * e + 2 ≥ a) :
    ⟨a + 2, 0, 0, 0, e + 2⟩ [fm]⊢⁺ ⟨3 * a + 5, 0, 0, 0, a + e + 5⟩ := by
  rcases Nat.even_or_odd a with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    rw [show 3 * (2 * m) + 5 = 6 * m + 5 from by ring,
        show 2 * m + e + 5 = e + 2 * m + 5 from by ring]
    exact main_trans_even m e (by omega)
  · subst hm
    rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 3 * (2 * m + 1) + 5 = 6 * m + 8 from by ring,
        show 2 * m + 1 + e + 5 = e + 2 * m + 6 from by ring]
    exact main_trans_odd m e (by omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩)
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 2, 0, 0, 0, e + 2⟩ ∧ 2 * e + 2 ≥ a)
  · intro c ⟨a, e, hq, hae⟩; subst hq
    exact ⟨⟨3 * a + 5, 0, 0, 0, a + e + 5⟩,
      ⟨3 * a + 3, a + e + 3, rfl, by omega⟩, main_trans a e hae⟩
  · exact ⟨0, 0, rfl, by omega⟩
