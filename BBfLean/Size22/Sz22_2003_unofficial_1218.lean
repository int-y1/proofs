import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1218: [5/6, 539/2, 484/35, 3/11, 2/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  2
 0  1  0  0 -1
 1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1218

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 chain: (0, b, 0, d, k) →* (0, b+k, 0, d, 0)
theorem e_to_b : ∀ k b d, ⟨(0:ℕ), b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- R1R1R3 chain: (2, b+2k, c, d+k, e) →* (2, b, c+k, d, e+2k)
theorem r1r1r3_chain : ∀ k b c d e, ⟨(2:ℕ), b + 2 * k, c, d + k, e⟩ [fm]⊢* ⟨2, b, c + k, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    rw [show b + 2 = (b + 1) + 1 from by ring,
        show (d + 1 : ℕ) = d + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + k + 1 = c + (k + 1) from by ring]
    finish

-- R2R2R3 chain: (2, 0, c+k, d, e) →* (2, 0, c, d+3*k, e+4*k)
theorem r2r2r3_chain : ∀ k c d e, ⟨(2:ℕ), 0, c + k, d, e⟩ [fm]⊢* ⟨2, 0, c, d + 3 * k, e + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 3) (e + 4))
    ring_nf; finish

-- Even case: e = 2m, transition from (0,0,0, m+δ+2, 2m+1)
theorem main_trans_even (m δ : ℕ) :
    ⟨(0:ℕ), 0, 0, m + δ + 2, 2 * m + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * m + δ + 4, 6 * m + 4⟩ := by
  -- R4 first step (establishes ⊢⁺)
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm
  -- R4 chain (2m steps)
  apply stepStar_trans (e_to_b (2 * m) 1 (m + δ + 2))
  -- R5
  rw [show 1 + 2 * m = 2 * m + 1 from by ring,
      show m + δ + 2 = (m + δ + 1) + 1 from by ring]
  step fm
  -- R1
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm
  -- R3
  rw [show m + δ + 1 = (m + δ) + 1 from by ring]
  step fm
  -- R1R1R3 chain (m rounds): (2, 2m, 0, m+δ, 2) → (2, 0, m, δ, 2+2m)
  rw [show (2 * m : ℕ) = 0 + 2 * m from by ring,
      show m + δ = δ + m from by ring]
  apply stepStar_trans (r1r1r3_chain m 0 0 δ 2)
  -- R2R2R3 chain (m rounds)
  apply stepStar_trans (r2r2r3_chain m 0 δ (2 + 2 * m))
  -- R2R2 final
  step fm; step fm
  ring_nf; finish

-- Odd case: e = 2m+1, transition from (0,0,0, m+δ+2, 2m+2)
theorem main_trans_odd (m δ : ℕ) :
    ⟨(0:ℕ), 0, 0, m + δ + 2, 2 * m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * m + δ + 5, 6 * m + 7⟩ := by
  -- R4 first step
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm
  -- R4 chain (2m+1 steps)
  apply stepStar_trans (e_to_b (2 * m + 1) 1 (m + δ + 2))
  -- R5
  rw [show 1 + (2 * m + 1) = 2 * m + 2 from by ring,
      show m + δ + 2 = (m + δ + 1) + 1 from by ring]
  step fm
  -- R1
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm
  -- R3
  rw [show m + δ + 1 = (m + δ) + 1 from by ring]
  step fm
  -- R1R1R3 chain (m rounds): (2, 2m+1, 0, m+δ, 2) → (2, 1, m, δ, 2+2m)
  rw [show (2 * m + 1 : ℕ) = 1 + 2 * m from by ring,
      show m + δ = δ + m from by ring]
  apply stepStar_trans (r1r1r3_chain m 1 0 δ 2)
  -- R1 (b=1): need to step from (2, 1, 0+m, δ, 2+2*m)
  -- The goal has (2, 1, 0+m, δ, 2+2*m). R1 needs a≥1,b≥1.
  -- Rewrite to expose the +1 patterns for matching
  rw [show (2:ℕ) = 1 + 1 from by ring, show (1:ℕ) = 0 + 1 from by ring]
  step fm
  -- R2 (a=1, b=0)
  step fm
  -- R3
  rw [show δ + 2 = (δ + 1) + 1 from by ring]
  step fm
  -- R2R2R3 chain (m rounds)
  apply stepStar_trans (r2r2r3_chain m 0 (δ + 1) ((2 + 2 * m) + 1 + 2))
  -- R2R2 final
  step fm; step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 2, e + 1⟩ ∧ 2 * d ≥ e)
  · intro c ⟨d, e, hq, hde⟩; subst hq
    refine ⟨⟨0, 0, 0, (d + e + 2) + 2, (3 * e + 3) + 1⟩,
      ⟨d + e + 2, 3 * e + 3, rfl, by omega⟩, ?_⟩
    show ⟨(0:ℕ), 0, 0, d + 2, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + e + 4, 3 * e + 4⟩
    rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- e even: e = m + m
      subst hm
      have hd : d ≥ m := by omega
      obtain ⟨δ, rfl⟩ : ∃ δ, d = m + δ := ⟨d - m, by omega⟩
      show ⟨(0:ℕ), 0, 0, (m + δ) + 2, (m + m) + 1⟩ [fm]⊢⁺
        ⟨0, 0, 0, (m + δ) + (m + m) + 4, 3 * (m + m) + 4⟩
      rw [show (m + m) + 1 = 2 * m + 1 from by ring,
          show (m + δ) + (m + m) + 4 = 3 * m + δ + 4 from by ring,
          show 3 * (m + m) + 4 = 6 * m + 4 from by ring]
      exact main_trans_even m δ
    · -- e odd: e = 2*m + 1
      subst hm
      have hd : d ≥ m := by omega
      obtain ⟨δ, rfl⟩ : ∃ δ, d = m + δ := ⟨d - m, by omega⟩
      show ⟨(0:ℕ), 0, 0, (m + δ) + 2, (2 * m + 1) + 1⟩ [fm]⊢⁺
        ⟨0, 0, 0, (m + δ) + (2 * m + 1) + 4, 3 * (2 * m + 1) + 4⟩
      rw [show (2 * m + 1) + 1 = 2 * m + 2 from by ring,
          show (m + δ) + (2 * m + 1) + 4 = 3 * m + δ + 5 from by ring,
          show 3 * (2 * m + 1) + 4 = 6 * m + 7 from by ring]
      exact main_trans_odd m δ
  · exact ⟨0, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1218
