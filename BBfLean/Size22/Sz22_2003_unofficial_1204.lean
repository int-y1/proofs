import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1204: [5/6, 539/2, 4/35, 3/11, 66/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  0
 0  1  0  0 -1
 1  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1204

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: move e to b
theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R3,R2,R2 drain
theorem drain : ∀ k, ⟨0, 0, c + k, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + 1 + 3 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 3) (e := e + 2))
    ring_nf; finish

-- R3,R1,R1 chain: (0, 2*k, c+1, d+k, 1) →* (0, 0, c+k+1, d, 1)
theorem chain : ∀ k, ∀ c d, ⟨0, 2 * k, c + 1, d + k, 1⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + k + 1, d, 1⟩ := by
  intro k; induction' k with k ih
  · intro c d; exists 0
  · intro c d
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm -- R3
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm -- R1
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm -- R1
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- R3,R1,R1 chain with b=1
theorem chain1 : ∀ k, ∀ c d, ⟨0, 1 + 2 * k, c + 1, d + k, 1⟩ [fm]⊢* ⟨(0 : ℕ), 1, c + k + 1, d, 1⟩ := by
  intro k; induction' k with k ih
  · intro c d; exists 0
  · intro c d
    rw [show 1 + 2 * (k + 1) = (1 + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm -- R3
    rw [show (1 + 2 * k) + 2 = (1 + 2 * k + 1) + 1 from by ring]
    step fm -- R1
    rw [show 1 + 2 * k + 1 = (1 + 2 * k) + 1 from by ring]
    step fm -- R1
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- Odd tail: (0, 1, c+1, d+1, 1) →⁺ (0, 0, c+1, d+2, 2)
theorem odd_tail : ⟨0, 1, c + 1, d + 1, 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, c + 1, d + 2, 2⟩ := by
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm -- R3: (2, 0+1, c, d, 1)
  step fm -- R1: (1, 0, c+1, d, 1)
  step fm -- R2: (0, 0, c+1, d+2, 2)
  finish

-- Full even transition
theorem full_even (m d : ℕ) (hd : d ≥ 1) :
    ⟨0, 0, 0, d + m + 1, 2 * m⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, d + 3 * m + 3, 2 * m + 3⟩ := by
  rw [show (2 * m : ℕ) = 0 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m) (b := 0) (d := d + m + 1) (e := 0))
  simp only [Nat.zero_add]
  rw [show d + m + 1 = (d + m) + 1 from by ring]
  step fm -- R5
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm -- R1: (0, 2*m, 1, d+m, 1)
  -- Now goal: (0, 2*m, 1, d+m, 1) ⊢* target
  -- chain m: (0, 2*m, 0+1, d+m, 1) →* (0, 0, 0+m+1, d, 1)
  -- The issue: chain m 0 d has 0+1 and the goal has 1.
  -- Use convert instead of apply.
  have h_chain := chain m 0 d
  simp only [Nat.zero_add] at h_chain
  apply stepStar_trans h_chain
  -- drain
  rw [show m + 1 = 0 + (m + 1) from by ring]
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  apply stepStar_trans (drain (m + 1) (c := 0) (d := d') (e := 1))
  ring_nf; finish

-- Full odd transition
theorem full_odd (m d : ℕ) (hd : d ≥ 1) :
    ⟨0, 0, 0, d + m + 1, 2 * m + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, d + 3 * m + 4, 2 * m + 4⟩ := by
  rw [show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m + 1) (b := 0) (d := d + m + 1) (e := 0))
  simp only [Nat.zero_add]
  rw [show d + m + 1 = (d + m) + 1 from by ring]
  step fm -- R5
  rw [show 2 * m + 1 + 1 = (2 * m + 1) + 1 from by ring]
  step fm -- R1: (0, 2*m+1, 1, d+m, 1)
  rw [show 2 * m + 1 = 1 + 2 * m from by ring]
  -- chain1 m 0 d: has 0+1 issue. Use simp.
  have h_chain := chain1 m 0 d
  simp only [Nat.zero_add] at h_chain
  -- h_chain: (0, 1+2*m, 1, d+m, 1) ⊢* (0, 1, m+1, d, 1)
  apply stepStar_trans h_chain
  -- goal: (0, 1, m+1, d, 1) ⊢* target
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  -- odd_tail: (0, 1, m+1, d'+1, 1) →⁺ (0, 0, m+1, d'+2, 2)
  apply stepStar_trans (stepPlus_stepStar (odd_tail (c := m) (d := d')))
  rw [show m + 1 = 0 + (m + 1) from by ring,
      show d' + 2 = (d' + 1) + 1 from by ring]
  apply stepStar_trans (drain (m + 1) (c := 0) (d := d' + 1) (e := 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 4⟩)
  · execute fm 10
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ E ≥ 2 ∧ D ≥ E + 1)
  · intro c ⟨D, E, hq, hE, hD⟩; subst hq
    rcases Nat.even_or_odd E with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- E even: E = m + m
      rw [show m + m = 2 * m from by ring] at hm; subst hm
      have hm1 : m ≥ 1 := by omega
      obtain ⟨d, rfl⟩ : ∃ d, D = d + m + 1 := ⟨D - m - 1, by omega⟩
      refine ⟨⟨0, 0, 0, d + 3 * m + 3, 2 * m + 3⟩,
        ⟨d + 3 * m + 3, 2 * m + 3, rfl, by omega, by omega⟩,
        full_even m d (by omega)⟩
    · -- E odd: E = 2*m + 1
      subst hm
      obtain ⟨d, rfl⟩ : ∃ d, D = d + m + 1 := ⟨D - m - 1, by omega⟩
      refine ⟨⟨0, 0, 0, d + 3 * m + 4, 2 * m + 4⟩,
        ⟨d + 3 * m + 4, 2 * m + 4, rfl, by omega, by omega⟩,
        full_odd m d (by omega)⟩
  · exact ⟨5, 4, rfl, by omega, by omega⟩
