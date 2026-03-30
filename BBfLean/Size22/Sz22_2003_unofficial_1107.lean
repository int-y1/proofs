import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1107: [5/6, 4/35, 539/2, 3/11, 66/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  2  1
 0  1  0  0 -1
 1  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1107

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | _ => none

-- R3 chain: drain a into d and e, with b=0 and c=0.
theorem r3_chain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

-- R4 chain: drain e into b, with a=0 and c=0.
theorem r4_chain : ∀ k, ∀ b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- R2 chain with e=1: drain c into a, with b=0.
theorem r2_chain_e1 : ∀ k, ∀ a d, ⟨a, 0, k, d + k, 1⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, 1⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d)
    ring_nf; finish

-- Mixing phase with e=1: general form by strong induction on B.
theorem mix_general : ∀ B, ∀ C d,
    ⟨0, B, C + 1, d + B + C + 1, 1⟩ [fm]⊢* ⟨B + 2 * C + 2, 0, 0, d, 1⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro C d
  rcases B with _ | _ | B
  · -- B = 0: pure R2 chain
    show ⟨0, 0, C + 1, d + 0 + C + 1, 1⟩ [fm]⊢* ⟨0 + 2 * C + 2, 0, 0, d, 1⟩
    rw [show d + 0 + C + 1 = d + (C + 1) from by ring]
    apply stepStar_trans (r2_chain_e1 (C + 1) 0 d)
    ring_nf; finish
  · -- B = 1: R2, R1, then R2 chain
    show ⟨0, 1, C + 1, d + 1 + C + 1, 1⟩ [fm]⊢* ⟨1 + 2 * C + 2, 0, 0, d, 1⟩
    rw [show d + 1 + C + 1 = (d + C + 1) + 1 from by ring]
    step fm
    step fm
    rw [show d + C + 1 = d + (C + 1) from by ring]
    apply stepStar_trans (r2_chain_e1 (C + 1) 1 d)
    ring_nf; finish
  · -- B + 2: R2,R1,R1 then IH with B and C+1
    show ⟨0, B + 2, C + 1, d + (B + 2) + C + 1, 1⟩ [fm]⊢* ⟨(B + 2) + 2 * C + 2, 0, 0, d, 1⟩
    rw [show d + (B + 2) + C + 1 = (d + B + (C + 1) + 1) + 1 from by ring]
    step fm
    step fm
    rw [show d + B + (C + 1) + 1 = (d + B + (C + 1) + 1) from by ring]
    step fm
    show ⟨0, B, C + 2, d + B + (C + 1) + 1, 1⟩ [fm]⊢* ⟨B + 2 + 2 * C + 2, 0, 0, d, 1⟩
    apply stepStar_trans (ih B (by omega) (C + 1) d)
    ring_nf; finish

-- R5+R1: (0, B, 0, D+1, 0) →* (0, B, 1, D, 1).
theorem r5_r1 : ⟨0, B, 0, D + 1, 0⟩ [fm]⊢* ⟨0, B, 1, D, 1⟩ := by
  step fm; step fm; finish

-- R5+R1, then mix_general, then R3 chain.
theorem phase234 : ∀ m E, ⟨0, E + 1, 0, m + E + 3, 0⟩ [fm]⊢* ⟨0, 0, 0, m + 2 * E + 6, E + 4⟩ := by
  intro m E
  -- R5+R1: (0, E+1, 0, (m+E+2)+1, 0) →* (0, E+1, 1, m+E+2, 1)
  rw [show m + E + 3 = (m + E + 2) + 1 from by ring]
  apply stepStar_trans (r5_r1 (B := E + 1) (D := m + E + 2))
  -- Now at (0, E+1, 1, m+E+2, 1)
  rw [show m + E + 2 = m + (E + 1) + 0 + 1 from by ring]
  apply stepStar_trans (mix_general (E + 1) 0 m)
  rw [show E + 1 + 2 * 0 + 2 = E + 3 from by ring]
  -- Now at (E+3, 0, 0, m, 1)
  apply stepStar_trans (r3_chain (E + 3) m 1)
  ring_nf; finish

-- Main transition: from (0, 0, 0, m+E+3, E+1) to (0, 0, 0, m+2*E+6, E+4).
theorem main_transition : ∀ m E,
    ⟨0, 0, 0, m + E + 3, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, m + 2 * E + 6, E + 4⟩ := by
  intro m E
  -- First step (R4): gives ⊢⁺
  step fm
  -- Now at (0, 1, 0, m+E+3, E): remaining R4 chain
  apply stepStar_trans (r4_chain E 1 (m + E + 3))
  -- Now at (0, 1+E, 0, m+E+3, 0)
  show ⟨0, 1 + E, 0, m + E + 3, 0⟩ [fm]⊢* ⟨0, 0, 0, m + 2 * E + 6, E + 4⟩
  rw [show (1 : ℕ) + E = E + 1 from by ring]
  exact phase234 m E

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 11, 7⟩) (by execute fm 31)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m E, q = ⟨0, 0, 0, m + E + 3, E + 1⟩)
  · intro c ⟨m, E, hq⟩; subst hq
    exact ⟨⟨0, 0, 0, m + 2 * E + 6, E + 4⟩,
      ⟨m + E, E + 3, by ring_nf⟩,
      main_transition m E⟩
  · exact ⟨2, 6, by ring_nf⟩

end Sz22_2003_unofficial_1107
