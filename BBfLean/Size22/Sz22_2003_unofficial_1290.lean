import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1290: [63/10, 11/2, 4/33, 5/7, 20/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  1
 2 -1  0  0 -1
 0  0  1 -1  0
 2  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1290

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

theorem d_to_c : ∀ k c d, ⟨(0 : ℕ), (0 : ℕ), c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + k, d, e⟩ := by
  intro k; induction' k with k ih
  · intro c d; exists 0
  · intro c d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

theorem r3r1r1_chain : ∀ k B C D E, ⟨(0 : ℕ), B + 1, C + 2 * k, D, E + k⟩ [fm]⊢*
    ⟨(0 : ℕ), B + 3 * k + 1, C, D + 2 * k, E⟩ := by
  intro k; induction' k with k ih
  · intro B C D E; simp; exists 0
  · intro B C D E
    rw [show C + 2 * (k + 1) = (C + 2) + 2 * k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    apply stepStar_trans (ih B (C + 2) D (E + 1))
    rw [show B + 3 * k + 1 = (B + 3 * k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show B + 3 * k + 4 = B + 3 * (k + 1) + 1 from by ring,
        show D + 2 * k + 2 = D + 2 * (k + 1) from by ring]
    finish

theorem drain_b : ∀ B D E, ⟨(0 : ℕ), B, (0 : ℕ), D, E + 1⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D, E + B + 1⟩ := by
  intro B; induction' B with B ih
  · intro D E; exists 0
  · intro D E
    step fm; step fm; step fm
    rw [show E + 2 = (E + 1) + 1 from by ring]
    apply stepStar_trans (ih D (E + 1))
    rw [show E + 1 + B + 1 = E + (B + 1) + 1 from by ring]
    finish

theorem c1_handle (B D E : ℕ) : ⟨(0 : ℕ), B + 1, 1, D, E + 1⟩ [fm]⊢*
    ⟨(0 : ℕ), B + 2, (0 : ℕ), D + 1, E + 1⟩ := by
  step fm; step fm; step fm; finish

theorem main_d0 (F : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), F + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 1, F + 3⟩ := by
  step fm; step fm; step fm
  apply stepStar_trans (drain_b 2 1 F)
  rw [show F + 2 + 1 = F + 3 from by ring]; finish

-- Even c phase: chain (m+1) rounds then drain
theorem phase_even (m F : ℕ) :
    ⟨(0 : ℕ), 4, 2 * (m + 1), 2, F + m + 2 + (m + 1)⟩ [fm]⊢*
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 2 * m + 4, F + 4 * m + 9⟩ := by
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show 2 * (m + 1) = 0 + 2 * (m + 1) from by ring]
  apply stepStar_trans (r3r1r1_chain (m + 1) 3 0 2 (F + m + 2))
  rw [show 3 + 3 * (m + 1) + 1 = 3 * m + 7 from by ring,
      show F + m + 2 = (F + m + 1) + 1 from by ring]
  apply stepStar_trans (drain_b (3 * m + 7) (2 + 2 * (m + 1)) (F + m + 1))
  rw [show F + m + 1 + (3 * m + 7) + 1 = F + 4 * m + 9 from by ring,
      show 2 + 2 * (m + 1) = 2 * m + 4 from by ring]
  finish

-- Odd c phase: chain k rounds, c1_handle, drain
theorem phase_odd (k F : ℕ) :
    ⟨(0 : ℕ), 4, 2 * k + 1, 2, F + k + 2 + k⟩ [fm]⊢*
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 2 * k + 3, F + 4 * k + 7⟩ := by
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show 2 * k + 1 = 1 + 2 * k from by ring]
  apply stepStar_trans (r3r1r1_chain k 3 1 2 (F + k + 2))
  rw [show 3 + 3 * k + 1 = (3 * k + 3) + 1 from by ring,
      show F + k + 2 = (F + k + 1) + 1 from by ring]
  apply stepStar_trans (c1_handle (3 * k + 3) (2 + 2 * k) (F + k + 1))
  rw [show 3 * k + 3 + 2 = 3 * k + 5 from by ring,
      show 2 + 2 * k + 1 = 2 * k + 3 from by ring,
      show F + k + 1 + 1 = (F + k + 1) + 1 from by ring]
  apply stepStar_trans (drain_b (3 * k + 5) (2 * k + 3) (F + k + 1))
  rw [show F + k + 1 + (3 * k + 5) + 1 = F + 4 * k + 7 from by ring]
  finish

-- Main: (0,0,0,d+1,F+d+2) →⁺ (0,0,0,d+2,F+2d+5)
theorem main_transition (d F : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 1, F + d + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 2, F + 2 * d + 5⟩ := by
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (d + 1) 0 0 (e := F + d + 2))
  show ⟨(0 : ℕ), 0, 0 + (d + 1), 0, F + d + 2⟩ [fm]⊢⁺ _
  rw [show 0 + (d + 1) = d + 1 from by ring,
      show F + d + 2 = (F + d + 1) + 1 from by ring]
  step fm  -- R5
  rw [show d + 1 + 1 = d + 2 from by ring]
  step fm  -- R1
  step fm  -- R1
  -- State: (0, 4, d, 2, F+d+1)
  rcases d with _ | d
  · -- d = 0: drain
    apply stepStar_trans (drain_b 4 2 F)
    rw [show F + 4 + 1 = F + 5 from by ring]; finish
  · rcases Nat.even_or_odd (d + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- d+1 even: d+1 = 2k, k >= 1
      rw [show k + k = 2 * k from by ring] at hk
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      -- d+1 = 2(m+1). c = d+1 = 2(m+1). e = F+d+1+1 = F+2(m+1)+1.
      -- Need: (0, 4, 2(m+1), 2, F+2(m+1)+1) →* (0, 0, 0, d+1+2, F+2(d+1)+5)
      -- phase_even needs: (0, 4, 2(m+1), 2, F+m+2+(m+1))
      -- F+2(m+1)+1 = F+2m+3 and F+m+2+(m+1) = F+2m+3. ✓
      rw [show d + 1 = 2 * (m + 1) from hk,
          show F + 2 * (m + 1) + 1 = F + m + 2 + (m + 1) from by ring]
      apply stepStar_trans (phase_even m F)
      -- After: (0, 0, 0, 2m+4, F+4m+9)
      -- Target: (0, 0, 0, d+1+2, F+2(d+1)+5) = (0, 0, 0, 2(m+1)+2, F+2*2(m+1)+5)
      --       = (0, 0, 0, 2m+4, F+4m+9). ✓
      rw [show 2 * m + 4 = 2 * (m + 1) + 2 from by ring,
          show F + 4 * m + 9 = F + 2 * (2 * (m + 1)) + 5 from by ring]
      rw [show 2 * (m + 1) = d + 1 from by omega,
          show 2 * (d + 1) = 2 * (d + 1) from rfl]
      finish
    · -- d+1 odd: d+1 = 2k+1
      -- c = d+1 = 2k+1. e = F+d+1+1 = F+2k+2.
      -- phase_odd needs: F+k+2+k = F+2k+2. ✓
      rw [show d + 1 = 2 * k + 1 from hk,
          show F + (2 * k + 1) + 1 = F + k + 2 + k from by ring]
      apply stepStar_trans (phase_odd k F)
      -- After: (0, 0, 0, 2k+3, F+4k+7)
      -- Target: (0, 0, 0, d+1+2, F+2(d+1)+5) = (0, 0, 0, 2k+3, F+4k+7). ✓
      rw [show 2 * k + 3 = (2 * k + 1) + 2 from by ring,
          show F + 4 * k + 7 = F + 2 * (2 * k + 1) + 5 from by ring]
      rw [show 2 * k + 1 = d + 1 from by omega,
          show 2 * (d + 1) = 2 * (d + 1) from rfl]
      finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ e ≥ d + 1)
  · intro c ⟨d, e, hq, he⟩; subst hq
    rcases d with _ | d
    · obtain ⟨F, rfl⟩ : ∃ F, e = F + 1 := ⟨e - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 1, F + 3⟩, ⟨1, F + 3, rfl, by omega⟩, main_d0 F⟩
    · obtain ⟨F, rfl⟩ : ∃ F, e = F + d + 2 := ⟨e - d - 2, by omega⟩
      refine ⟨⟨0, 0, 0, d + 2, F + 2 * d + 5⟩,
        ⟨d + 2, F + 2 * d + 5, rfl, by omega⟩, ?_⟩
      exact main_transition d F
  · exact ⟨0, 1, rfl, by omega⟩

end Sz22_2003_unofficial_1290
