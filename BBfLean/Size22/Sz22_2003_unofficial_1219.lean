import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1219: [5/6, 539/2, 484/35, 3/11, 5/3]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  2
 0  1  0  0 -1
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1219

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: move e to b
theorem e_to_b : ∀ k b d e, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih
  · intro b d e; exists 0
  · intro b d e
    rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R3,R1,R1 chain: k rounds
theorem r3r1r1_chain : ∀ k, ∀ b c d e,
    ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e⟩ [fm]⊢*
    ⟨(0 : ℕ), b, c + k + 1, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro b c d e; simp; exists 0
  · intro b c d e
    rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    rw [show b + 2 = (b + 1) + 1 from by ring,
        show c + k + 1 = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + k + 2 = c + (k + 1) + 1 from by ring,
        show e + 2 * k + 2 = e + 2 * (k + 1) from by ring]
    finish

-- R3,R2,R2 chain: k rounds
theorem r3r2r2_chain : ∀ k, ∀ c d e,
    ⟨(0 : ℕ), 0, c + k, d + 1, e⟩ [fm]⊢*
    ⟨(0 : ℕ), 0, c, d + 3 * k + 1, e + 4 * k⟩ := by
  intro k; induction' k with k ih
  · intro c d e; simp; exists 0
  · intro c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 4))
    ring_nf; finish

-- Transition for odd E: (0,0,0,D+m+1,2m+1) →⁺ (0,0,0,D+3m+4,6m+4)
theorem main_trans_odd (D m : ℕ) :
    ⟨(0 : ℕ), 0, 0, D + m + 1, 2 * m + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, D + 3 * m + 4, 6 * m + 4⟩ := by
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m + 1) 0 (D + m + 1) 0)
  rw [show (0 : ℕ) + (2 * m + 1) = 2 * m + 1 from by ring]
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm
  rw [show 2 * m = 0 + 2 * m from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show D + m + 1 = (D + 1) + m from by ring]
  apply stepStar_trans (r3r1r1_chain m 0 0 (D + 1) 0)
  rw [show 0 + m + 1 = 0 + (m + 1) from by ring,
      show D + 1 = D + 1 from rfl,
      show 0 + 2 * m = 2 * m from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 1) 0 D (2 * m))
  rw [show D + 3 * (m + 1) + 1 = D + 3 * m + 4 from by ring,
      show 2 * m + 4 * (m + 1) = 6 * m + 4 from by ring]
  finish

-- Transition for even E: (0,0,0,D+m+2,2m+2) →⁺ (0,0,0,D+3m+6,6m+7)
theorem main_trans_even (D m : ℕ) :
    ⟨(0 : ℕ), 0, 0, D + m + 2, 2 * m + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, D + 3 * m + 6, 6 * m + 7⟩ := by
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m + 2) 0 (D + m + 2) 0)
  rw [show (0 : ℕ) + (2 * m + 2) = 2 * m + 2 from by ring]
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm
  rw [show 2 * m + 1 = 1 + 2 * m from by ring,
      show D + m + 2 = (D + 2) + m from by ring]
  apply stepStar_trans (r3r1r1_chain m 1 0 (D + 2) 0)
  rw [show 0 + m + 1 = m + 1 from by ring,
      show 0 + 2 * m = 2 * m from by ring]
  rw [show m + 1 = m + 1 from rfl,
      show D + 2 = (D + 1) + 1 from by ring]
  step fm; step fm; step fm
  rw [show m + 1 = 0 + (m + 1) from by ring,
      show D + 3 = (D + 2) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 1) 0 (D + 2) (2 * m + 3))
  rw [show D + 2 + 3 * (m + 1) + 1 = D + 3 * m + 6 from by ring,
      show 2 * m + 3 + 4 * (m + 1) = 6 * m + 7 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 4⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨(0 : ℕ), 0, 0, d, e + 1⟩ ∧ 2 * d ≥ e + 3)
  · intro c ⟨d, e, hc, hd⟩
    subst hc
    rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- e = 2m, E = 2m+1 (odd)
      refine ⟨⟨0, 0, 0, d + 2 * m + 3, 6 * m + 4⟩,
        ⟨d + 2 * m + 3, 6 * m + 3, ?_, by omega⟩, ?_⟩
      · congr 1
      · have h := main_trans_odd (d - m - 1) m
        rw [show (d - m - 1) + m + 1 = d from by omega,
            show (d - m - 1) + 3 * m + 4 = d + 2 * m + 3 from by omega] at h
        have he : e + 1 = 2 * m + 1 := by omega
        rw [he]; exact h
    · -- e = 2m+1, E = 2m+2 (even)
      refine ⟨⟨0, 0, 0, d + 2 * m + 4, 6 * m + 7⟩,
        ⟨d + 2 * m + 4, 6 * m + 6, ?_, by omega⟩, ?_⟩
      · congr 1
      · have h := main_trans_even (d - m - 2) m
        rw [show (d - m - 2) + m + 2 = d from by omega,
            show (d - m - 2) + 3 * m + 6 = d + 2 * m + 4 from by omega] at h
        have he : e + 1 = 2 * m + 2 := by omega
        rw [he]; exact h
  · exact ⟨5, 3, rfl, by omega⟩

end Sz22_2003_unofficial_1219
