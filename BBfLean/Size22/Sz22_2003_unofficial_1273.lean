import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1273: [5/6, 99/35, 88/5, 7/11, 5/2]

Vector representation:
```
-1 -1  1  0  0
 0  2 -1 -1  1
 3  0 -1  0  1
 0  0  0  1 -1
-1  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1273

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+3, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 chain: drain c when b=0, d=0
theorem r3_chain : ∀ k, ∀ a e, ⟨a, (0 : ℕ), k, (0 : ℕ), e⟩ [fm]⊢* ⟨a + 3 * k, (0 : ℕ), (0 : ℕ), (0 : ℕ), e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 3) (e + 1))
    ring_nf; finish

-- R4 chain: move e to d
theorem r4_chain : ∀ k, ∀ a d, ⟨a, (0 : ℕ), (0 : ℕ), d, k⟩ [fm]⊢* ⟨a, (0 : ℕ), (0 : ℕ), d + k, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

-- R2 chain: pure R2 with a=0
theorem r2_drain : ∀ k, ∀ b c e, ⟨(0 : ℕ), b, c + k + 1, k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + 2 * k, c + 1, (0 : ℕ), e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · simp; exists 0
  · rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (b + 2) c (e + 1))
    ring_nf; finish

-- After d=0: (A, B, C+1, 0, E) ->* (A + 3*(C+1) + 2*B, 0, 0, 0, E + C + 1 + B)
theorem after_d0 : ∀ B, ∀ A C E,
    ⟨A, B, C + 1, (0 : ℕ), E⟩ [fm]⊢*
    ⟨A + 3 * C + 2 * B + 3, (0 : ℕ), (0 : ℕ), (0 : ℕ), E + C + B + 1⟩ := by
  intro B; induction' B with B ih <;> intro A C E
  · rw [show A + 3 * C + 2 * 0 + 3 = A + 3 * (C + 1) from by ring,
        show E + C + 0 + 1 = E + (C + 1) from by ring]
    exact r3_chain (C + 1) A E
  · rcases A with _ | A
    · step fm; step fm
      apply stepStar_trans (ih 2 C (E + 1))
      ring_nf; finish
    · step fm
      rw [show C + 2 = (C + 1) + 1 from by ring]
      apply stepStar_trans (ih A (C + 1) E)
      ring_nf; finish

-- Main phase: (A, 0, C+1, D, E) ->* (A+D+3C+3, 0, 0, 0, E+2D+C+1) when C+A >= D
theorem phase : ∀ A, ∀ C D E, C + A ≥ D →
    ⟨A, (0 : ℕ), C + 1, D, E⟩ [fm]⊢*
    ⟨A + D + 3 * C + 3, (0 : ℕ), (0 : ℕ), (0 : ℕ), E + 2 * D + C + 1⟩ := by
  intro A; induction' A using Nat.strongRecOn with A ih; intro C D E hCD
  rcases A with _ | _ | A
  · -- A = 0
    rcases D with _ | D
    · -- D = 0
      rw [show 0 + 0 + 3 * C + 3 = 0 + 3 * (C + 1) from by ring,
          show E + 2 * 0 + C + 1 = E + (C + 1) from by ring]
      exact r3_chain (C + 1) 0 E
    · -- D + 1: pure R2 chain then after_d0
      obtain ⟨C', rfl⟩ : ∃ C', C = C' + D + 1 := ⟨C - D - 1, by omega⟩
      rw [show C' + D + 1 + 1 = C' + (D + 1) + 1 from by ring]
      apply stepStar_trans (r2_drain (D + 1) 0 C' E)
      rw [show 0 + 2 * (D + 1) = 2 * (D + 1) from by ring]
      apply stepStar_trans (after_d0 (2 * (D + 1)) 0 C' (E + (D + 1)))
      ring_nf; finish
  · -- A = 1
    rcases D with _ | D
    · -- D = 0
      rw [show 1 + 0 + 3 * C + 3 = 1 + 3 * (C + 1) from by ring,
          show E + 2 * 0 + C + 1 = E + (C + 1) from by ring]
      exact r3_chain (C + 1) 1 E
    · -- D + 1: R2+R1, then R2 chain then after_d0
      rcases D with _ | D
      · -- D = 0, so original d = 1
        step fm; step fm
        apply stepStar_trans (after_d0 1 0 C (E + 1))
        ring_nf; finish
      · -- D + 1 ≥ 1
        obtain ⟨C', rfl⟩ : ∃ C', C = C' + D + 1 := ⟨C - D - 1, by omega⟩
        step fm; step fm
        rw [show C' + D + 1 + 1 = C' + (D + 1) + 1 from by ring]
        apply stepStar_trans (r2_drain (D + 1) 1 C' (E + 1))
        rw [show 1 + 2 * (D + 1) = 2 * D + 3 from by ring]
        apply stepStar_trans (after_d0 (2 * D + 3) 0 C' (E + 1 + (D + 1)))
        ring_nf; finish
  · -- A + 2
    rcases D with _ | D
    · -- D = 0
      rw [show A + 2 + 0 + 3 * C + 3 = (A + 2) + 3 * (C + 1) from by ring,
          show E + 2 * 0 + C + 1 = E + (C + 1) from by ring]
      exact r3_chain (C + 1) (A + 2) E
    · -- D + 1: R2+R1x2 then recurse
      step fm; step fm; step fm
      rw [show C + 2 = (C + 1) + 1 from by ring]
      apply stepStar_trans (ih A (by omega) (C + 1) D (E + 1) (by omega))
      ring_nf; finish

-- Main transition: parameterized to avoid ℕ subtraction
theorem main_transition (n d : ℕ) :
    ⟨d + n + 2, (0 : ℕ), (0 : ℕ), d, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨2 * d + n + 4, (0 : ℕ), (0 : ℕ), 2 * d + 1, (0 : ℕ)⟩ := by
  rw [show d + n + 2 = (d + n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨(d + n + 1) + 1, (0 : ℕ), (0 : ℕ), d, (0 : ℕ)⟩ : Q) [fm]⊢ ⟨d + n + 1, (0 : ℕ), 1, d, (0 : ℕ)⟩)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (phase (d + n + 1) 0 d 0 (by omega))
  rw [show d + n + 1 + d + 3 * 0 + 3 = 2 * d + n + 4 from by ring,
      show 0 + 2 * d + 0 + 1 = 2 * d + 1 from by ring]
  apply stepStar_trans (r4_chain (2 * d + 1) (2 * d + n + 4) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n d, q = ⟨d + n + 2, 0, 0, d, 0⟩ ∧ d ≥ 1)
  · intro c ⟨n, d, hq, hd⟩; subst hq
    exact ⟨_, ⟨n + 1, 2 * d + 1, by ring_nf, by omega⟩, main_transition n d⟩
  · exact ⟨0, 1, rfl, by omega⟩

end Sz22_2003_unofficial_1273
