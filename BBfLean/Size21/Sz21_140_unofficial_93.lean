import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #93: [5/6, 77/2, 8/35, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  1
 3  0 -1 -1  0
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_93

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: d → b transfer
theorem d_to_b : ∀ k, ∀ b d, ⟨(0 : ℕ), b, (0 : ℕ), d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- One full round of b-processing: R5, R1, R3, R1, R1, R1 (6 steps)
theorem full_round : ∀ b c e, ⟨(0 : ℕ), b + 4, c, (0 : ℕ), e + 1⟩ [fm]⊢* ⟨0, b, c + 3, 0, e⟩ := by
  intro b c e
  step fm
  rw [show b + 4 = (b + 3) + 1 from by ring]
  step fm; step fm
  rw [show b + 3 = (b + 2) + 1 from by ring]
  step fm
  rw [show b + 2 = (b + 1) + 1 from by ring]
  step fm; step fm; finish

-- m full rounds by induction
theorem full_rounds : ∀ m, ∀ r c e, ⟨(0 : ℕ), 4 * m + r, c, (0 : ℕ), e + m⟩ [fm]⊢* ⟨0, r, c + 3 * m, 0, e⟩ := by
  intro m; induction' m with m ih <;> intro r c e
  · simp; exists 0
  rw [show 4 * (m + 1) + r = (4 * m + r) + 4 from by ring,
      show e + (m + 1) = (e + m) + 1 from by ring]
  apply stepStar_trans (full_round (4 * m + r) c (e + m))
  have h := ih r (c + 3) e
  rw [show c + 3 + 3 * m = c + 3 * (m + 1) from by ring] at h
  exact h

-- Leftover b=1: R5, R1, R3 (3 steps)
theorem leftover_1 : ⟨(0 : ℕ), 1, c, (0 : ℕ), e + 1⟩ [fm]⊢* ⟨3, 0, c, 0, e⟩ := by
  step fm; step fm; step fm; finish

-- Leftover b=3: R5, R1, R3, R1, R1, R2, R3 (7 steps)
theorem leftover_3 : ⟨(0 : ℕ), 3, c, (0 : ℕ), e + 1⟩ [fm]⊢* ⟨3, 0, c + 1, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- R3+R2x3 rounds by induction
theorem r3r2_rounds : ∀ k, ∀ c d E, ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, E⟩ [fm]⊢* ⟨0, 0, c, d + 1 + 2 * k, E + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d E
  · simp; exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  -- R3, R2, R2, R2 (4 steps)
  step fm; step fm; step fm; step fm
  have h := ih c (d + 2) (E + 3)
  rw [show d + 2 + 1 + 2 * k = d + 1 + 2 * (k + 1) from by ring,
      show E + 3 + 3 * k = E + 3 * (k + 1) from by ring] at h
  apply stepStar_trans (c₂ := ⟨0, 0, c + k, (d + 2) + 1, E + 3⟩)
  · rw [show d + 2 + 1 = d + 3 from by ring]; finish
  exact h

-- Phase 3: (3, 0, c, 0, E) →* (0, 0, 0, 3+2c, E+3+3c)
theorem phase3 (c E : ℕ) : ⟨(3 : ℕ), (0 : ℕ), c, (0 : ℕ), E⟩ [fm]⊢* ⟨0, 0, 0, 3 + 2 * c, E + 3 + 3 * c⟩ := by
  -- R2x3: (3, 0, c, 0, E) →* (0, 0, c, 3, E+3)
  apply stepStar_trans (c₂ := ⟨0, 0, c, 3, E + 3⟩)
  · step fm; step fm; step fm; ring_nf; finish
  have h := @r3r2_rounds c 0 2 (E + 3)
  rw [show (0 : ℕ) + c = c from by ring,
      show 2 + 1 + 2 * c = 3 + 2 * c from by ring] at h
  exact h

-- Main transition case 1: d = 4m+1
theorem main_trans_1 (m e : ℕ) :
    ⟨(0 : ℕ), 0, 0, 4 * m + 1, e + m + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 6 * m + 3, e + 9 * m + 3⟩ := by
  -- R4 step to get ⊢⁺
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 0, 4 * m, e + m + 1⟩)
  · show fm ⟨0, 0, 0, (4 * m) + 1, e + m + 1⟩ = some ⟨0, 1, 0, 4 * m, e + m + 1⟩
    simp [fm]
  -- Remaining R4 steps: (0, 1, 0, 4m, e+m+1) →* (0, 4m+1, 0, 0, e+m+1)
  apply stepStar_trans (c₂ := ⟨0, 4 * m + 1, 0, 0, e + m + 1⟩)
  · have h := @d_to_b (e + m + 1) (4 * m) 1 0
    rw [show (0 : ℕ) + (4 * m) = 4 * m from by ring,
        show 1 + (4 * m) = 4 * m + 1 from by ring] at h
    exact h
  -- m full rounds: (0, 4m+1, 0, 0, (e+1)+m) →* (0, 1, 3m, 0, e+1)
  apply stepStar_trans (c₂ := ⟨0, 1, 3 * m, 0, e + 1⟩)
  · rw [show e + m + 1 = (e + 1) + m from by ring]
    have h := @full_rounds m 1 0 (e + 1)
    rw [show (0 : ℕ) + 3 * m = 3 * m from by ring] at h
    exact h
  -- Leftover b=1: (0, 1, 3m, 0, e+1) →* (3, 0, 3m, 0, e)
  apply stepStar_trans (c₂ := ⟨3, 0, 3 * m, 0, e⟩)
  · exact @leftover_1 (3 * m) e
  -- Phase 3: (3, 0, 3m, 0, e) →* (0, 0, 0, 3+6m, e+3+9m)
  apply stepStar_trans (phase3 (3 * m) e)
  ring_nf; finish

-- Main transition case 2: d = 4m+3
theorem main_trans_3 (m e : ℕ) :
    ⟨(0 : ℕ), 0, 0, 4 * m + 3, e + m + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 6 * m + 5, e + 9 * m + 7⟩ := by
  -- R4 step to get ⊢⁺
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 0, 4 * m + 2, e + m + 1⟩)
  · show fm ⟨0, 0, 0, (4 * m + 2) + 1, e + m + 1⟩ = some ⟨0, 1, 0, 4 * m + 2, e + m + 1⟩
    simp [fm]
  -- Remaining R4 steps
  apply stepStar_trans (c₂ := ⟨0, 4 * m + 3, 0, 0, e + m + 1⟩)
  · have h := @d_to_b (e + m + 1) (4 * m + 2) 1 0
    rw [show (0 : ℕ) + (4 * m + 2) = 4 * m + 2 from by ring,
        show 1 + (4 * m + 2) = 4 * m + 3 from by ring] at h
    exact h
  -- m full rounds: (0, 4m+3, 0, 0, (e+1)+m) →* (0, 3, 3m, 0, e+1)
  apply stepStar_trans (c₂ := ⟨0, 3, 3 * m, 0, e + 1⟩)
  · rw [show e + m + 1 = (e + 1) + m from by ring]
    have h := @full_rounds m 3 0 (e + 1)
    rw [show (0 : ℕ) + 3 * m = 3 * m from by ring] at h
    exact h
  -- Leftover b=3: (0, 3, 3m, 0, e+1) →* (3, 0, 3m+1, 0, e+1)
  apply stepStar_trans (c₂ := ⟨3, 0, 3 * m + 1, 0, e + 1⟩)
  · exact @leftover_3 (3 * m) e
  -- Phase 3: (3, 0, 3m+1, 0, e+1) →* (0, 0, 0, 3+6m+2, e+1+3+9m+3)
  apply stepStar_trans (phase3 (3 * m + 1) (e + 1))
  ring_nf; finish

-- Combined: from any (0,0,0,d,e) with d odd, d≥1, e≥d, reach another such state
theorem main_trans (d e : ℕ) (hd_odd : ∃ j, d = 2 * j + 1) (hd_pos : d ≥ 1) (he : e ≥ d) :
    ∃ d' e', (∃ j', d' = 2 * j' + 1) ∧ d' ≥ 1 ∧ e' ≥ d' ∧
    ⟨(0 : ℕ), 0, 0, d, e⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, d', e'⟩ := by
  obtain ⟨j, hj⟩ := hd_odd
  subst hj
  -- Split on j even/odd (d mod 4)
  rcases Nat.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- j = 2m, d = 4m+1
    subst hm
    have he_bound : e ≥ m + 1 := by omega
    set E := e - m - 1 with hE_def
    have hE : e = E + m + 1 := by omega
    refine ⟨6 * m + 3, E + 9 * m + 3, ⟨3 * m + 1, by ring⟩, by omega, by omega, ?_⟩
    rw [show 2 * (m + m) + 1 = 4 * m + 1 from by ring, hE]
    exact main_trans_1 m E
  · -- j = 2m+1, d = 4m+3
    subst hm
    have he_bound : e ≥ m + 1 := by omega
    set E := e - m - 1 with hE_def
    have hE : e = E + m + 1 := by omega
    refine ⟨6 * m + 5, E + 9 * m + 7, ⟨3 * m + 2, by ring⟩, by omega, by omega, ?_⟩
    rw [show 2 * (2 * m + 1) + 1 = 4 * m + 3 from by ring, hE]
    exact main_trans_3 m E

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) →* (0,0,0,3,3) in 8 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 3⟩) (by execute fm 8)
  -- Use progress_nonhalt with predicate
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨(0 : ℕ), 0, 0, d, e⟩ ∧ (∃ j, d = 2 * j + 1) ∧ d ≥ 1 ∧ e ≥ d)
  · intro c ⟨d, e, hq, hd_odd, hd_pos, he⟩
    subst hq
    obtain ⟨d', e', hd'_odd, hd'_pos, he', htrans⟩ := main_trans d e hd_odd hd_pos he
    exact ⟨⟨0, 0, 0, d', e'⟩, ⟨d', e', rfl, hd'_odd, hd'_pos, he'⟩, htrans⟩
  · exact ⟨3, 3, rfl, ⟨1, by ring⟩, by omega, by omega⟩
