import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1208: [5/6, 539/2, 4/35, 3/7, 28/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  0
 0  1  0 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1208

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

-- R4 chain: (0, b, 0, d+k, e) →* (0, b+k, 0, d, e)
theorem r4_chain : ∀ k b d, ⟨(0 : ℕ), b, (0 : ℕ), d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    rw [show b + 1 + k = b + (k + 1) from by ring]; exists 0

-- R3+R2+R2 chain: (0, 0, c+k, d+1, e) →* (0, 0, c, d+3*k+1, e+2*k)
theorem r3r2r2_chain : ∀ k c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 3 * k + 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 2))
    rw [show d + 3 + 3 * k + 1 = d + 3 * (k + 1) + 1 from by ring,
        show e + 2 + 2 * k = e + 2 * (k + 1) from by ring]; exists 0

-- Inner loop round: (2, b+4, c, 1, e+1) →* (2, b, c+3, 1, e)
theorem inner_round : ⟨(2 : ℕ), b + 4, c, (1 : ℕ), e + 1⟩ [fm]⊢* ⟨2, b, c + 3, 1, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Inner loop chain: k rounds
theorem inner_chain : ∀ k b c e, ⟨(2 : ℕ), b + 4 * k, c, (1 : ℕ), e + k⟩ [fm]⊢* ⟨2, b, c + 3 * k, 1, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · simp; exists 0
  · rw [show b + 4 * (k + 1) = (b + 4) + 4 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 4) c (e + 1))
    apply stepStar_trans (inner_round (b := b) (c := c + 3 * k) (e := e))
    rw [show c + 3 * k + 3 = c + 3 * (k + 1) from by ring]; exists 0

-- Phase 1+2: R4 chain + R5 → (2, d, 0, 1, e)
-- (0, 0, 0, d, e+1) →* (2, d, 0, 1, e)
theorem phase12 : ∀ d, ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d, e + 1⟩ [fm]⊢* ⟨2, d, 0, 1, e⟩ := by
  intro d
  rw [show (d : ℕ) = 0 + d from by ring]
  apply stepStar_trans (r4_chain d 0 0)
  rw [show (0 : ℕ) + d = d from by ring]
  step fm; finish

-- Combined transition for d%4 = 0: d = 4*(n+1), e_param = E + n + 2
theorem trans_mod0 (n E : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * (n + 1), E + n + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 9 * n + 14, E + 6 * n + 8⟩ := by
  rw [show E + n + 2 = (E + n + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (phase12 (4 * (n + 1)) (e := E + n + 1))
  -- (2, 4*(n+1), 0, 1, E+n+1)
  rw [show (4 : ℕ) * (n + 1) = 0 + 4 * (n + 1) from by ring,
      show E + n + 1 = E + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (inner_chain (n + 1) 0 0 E)
  -- (2, 0, 3*(n+1), 1, E)
  show ⟨2, 0, 0 + 3 * (n + 1), 1, E⟩ [fm]⊢⁺ _
  rw [show (0 : ℕ) + 3 * (n + 1) = 3 * (n + 1) from by ring]
  -- Exit mod 0: R2, R2
  step fm; step fm
  -- (0, 0, 3*(n+1), 5, E+2)
  show ⟨0, 0, 3 * (n + 1), 5, E + 2⟩ [fm]⊢* _
  rw [show (3 : ℕ) * (n + 1) = 0 + 3 * (n + 1) from by ring,
      show (5 : ℕ) = 4 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * (n + 1)) 0 4 (E + 2))
  rw [show 4 + 3 * (3 * (n + 1)) + 1 = 9 * n + 14 from by ring,
      show E + 2 + 2 * (3 * (n + 1)) = E + 6 * n + 8 from by ring]; exists 0

-- Combined transition for d%4 = 1: d = 4*n+1 (n >= 1), e_param = E + n + 1
theorem trans_mod1 (n E : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 1, E + n + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 9 * n + 6, E + 6 * n + 3⟩ := by
  rw [show E + n + 1 = (E + n) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (phase12 (4 * n + 1) (e := E + n))
  rw [show (4 : ℕ) * n + 1 = 1 + 4 * n from by ring,
      show E + n = E + n from rfl]
  apply stepStar_stepPlus_stepPlus (inner_chain n 1 0 E)
  show ⟨2, 1, 0 + 3 * n, 1, E⟩ [fm]⊢⁺ _
  rw [show (0 : ℕ) + 3 * n = 3 * n from by ring]
  -- Exit mod 1: R1, R2
  step fm; step fm
  show ⟨0, 0, 3 * n + 1, 3, E + 1⟩ [fm]⊢* _
  rw [show (3 : ℕ) * n + 1 = 0 + (3 * n + 1) from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * n + 1) 0 2 (E + 1))
  rw [show 2 + 3 * (3 * n + 1) + 1 = 9 * n + 6 from by ring,
      show E + 1 + 2 * (3 * n + 1) = E + 6 * n + 3 from by ring]; exists 0

-- Combined transition for d%4 = 2: d = 4*n+2, e_param = E + n + 1
theorem trans_mod2 (n E : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 2, E + n + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 9 * n + 7, E + 6 * n + 4⟩ := by
  rw [show E + n + 1 = (E + n) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (phase12 (4 * n + 2) (e := E + n))
  rw [show (4 : ℕ) * n + 2 = 2 + 4 * n from by ring,
      show E + n = E + n from rfl]
  apply stepStar_stepPlus_stepPlus (inner_chain n 2 0 E)
  show ⟨2, 2, 0 + 3 * n, 1, E⟩ [fm]⊢⁺ _
  rw [show (0 : ℕ) + 3 * n = 3 * n from by ring]
  -- Exit mod 2: R1, R1, R3, R2, R2
  step fm; step fm; step fm; step fm; step fm
  show ⟨0, 0, 3 * n + 1, 4, E + 2⟩ [fm]⊢* _
  rw [show (3 : ℕ) * n + 1 = 0 + (3 * n + 1) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * n + 1) 0 3 (E + 2))
  rw [show 3 + 3 * (3 * n + 1) + 1 = 9 * n + 7 from by ring,
      show E + 2 + 2 * (3 * n + 1) = E + 6 * n + 4 from by ring]; exists 0

-- Combined transition for d%4 = 3: d = 4*n+3, e_param = E + n + 1
theorem trans_mod3 (n E : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 3, E + n + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 9 * n + 8, E + 6 * n + 5⟩ := by
  rw [show E + n + 1 = (E + n) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (phase12 (4 * n + 3) (e := E + n))
  rw [show (4 : ℕ) * n + 3 = 3 + 4 * n from by ring,
      show E + n = E + n from rfl]
  apply stepStar_stepPlus_stepPlus (inner_chain n 3 0 E)
  show ⟨2, 3, 0 + 3 * n, 1, E⟩ [fm]⊢⁺ _
  rw [show (0 : ℕ) + 3 * n = 3 * n from by ring]
  -- Exit mod 3: R1, R1, R3, R1, R2
  step fm; step fm; step fm; step fm; step fm
  show ⟨0, 0, 3 * n + 2, 2, E + 1⟩ [fm]⊢* _
  rw [show (3 : ℕ) * n + 2 = 0 + (3 * n + 2) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * n + 2) 0 1 (E + 1))
  rw [show 1 + 3 * (3 * n + 2) + 1 = 9 * n + 8 from by ring,
      show E + 1 + 2 * (3 * n + 2) = E + 6 * n + 5 from by ring]; exists 0

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 2 ∧ 2 * e ≥ d)
  · intro c ⟨d, e, hq, hd, he⟩; subst hq
    rcases (show d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 from by omega) with h | h | h | h
    · obtain ⟨n, hn⟩ : ∃ n, d = 4 * n := ⟨d / 4, by omega⟩
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      subst hn
      obtain ⟨E, rfl⟩ : ∃ E, e = E + n' + 2 := ⟨e - n' - 2, by omega⟩
      exact ⟨⟨0, 0, 0, 9 * n' + 14, E + 6 * n' + 8⟩,
        ⟨9 * n' + 14, E + 6 * n' + 8, rfl, by omega, by omega⟩,
        trans_mod0 n' E⟩
    · obtain ⟨n, hn⟩ : ∃ n, d = 4 * n + 1 := ⟨d / 4, by omega⟩
      subst hn
      obtain ⟨E, rfl⟩ : ∃ E, e = E + n + 1 := ⟨e - n - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 9 * n + 6, E + 6 * n + 3⟩,
        ⟨9 * n + 6, E + 6 * n + 3, rfl, by omega, by omega⟩,
        trans_mod1 n E⟩
    · obtain ⟨n, hn⟩ : ∃ n, d = 4 * n + 2 := ⟨d / 4, by omega⟩
      subst hn
      obtain ⟨E, rfl⟩ : ∃ E, e = E + n + 1 := ⟨e - n - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 9 * n + 7, E + 6 * n + 4⟩,
        ⟨9 * n + 7, E + 6 * n + 4, rfl, by omega, by omega⟩,
        trans_mod2 n E⟩
    · obtain ⟨n, hn⟩ : ∃ n, d = 4 * n + 3 := ⟨d / 4, by omega⟩
      subst hn
      obtain ⟨E, rfl⟩ : ∃ E, e = E + n + 1 := ⟨e - n - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 9 * n + 8, E + 6 * n + 5⟩,
        ⟨9 * n + 8, E + 6 * n + 5, rfl, by omega, by omega⟩,
        trans_mod3 n E⟩
  · exact ⟨2, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1208
