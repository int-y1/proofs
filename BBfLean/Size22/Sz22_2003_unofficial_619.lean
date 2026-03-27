import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #619: [35/6, 121/2, 8/55, 3/7, 6/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 3  0 -1  0 -1
 0  1  0 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_619

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b d e, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R2 repeated: convert a to e (when b=0)
theorem r2_chain : ∀ k a c d e, ⟨a+k, 0, c, d, e⟩ [fm]⊢* ⟨a, 0, c, d, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R1 repeated: drain from both a and b
theorem r1_chain : ∀ k a b c d e, ⟨a+k, b+k, c, d, e⟩ [fm]⊢* ⟨a, b, c+k, d+k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _ _)
  ring_nf; finish

-- R3+R2×3 repeated: drain c (when a=0, b=0)
theorem r3r2_chain : ∀ k c d e, ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+5*k+1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show e + 6 = (e + 5) + 1 from by ring]
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Main drain: (3, B, C, D, E+1) →* (0, 0, 0, D+B, E+3*B+5*C+7)
-- Using E+1 formulation ensures R3 always has e≥1.
-- For B≥3, the R3 step consumes the +1, and we need the recursive call
-- to also have +1 form. This works because E+1 → E after R3,
-- and E = (E-1)+1 when E ≥ 1. We enforce E ≥ B/3 via the precondition.
theorem main_drain : ∀ B, ∀ C D E, B ≤ 3*E+2 →
    ⟨3, B, C, D, E+1⟩ [fm]⊢* ⟨0, 0, 0, D+B, E+3*B+5*C+7⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro C D E hBE
  rcases B with _ | _ | _ | B'
  · -- B=0: R2×3 then r3r2 chain
    rw [show (3 : ℕ) = 0 + 3 from by ring]
    apply stepStar_trans (r2_chain 3 0 C D (E+1))
    rcases C with _ | C
    · ring_nf; finish
    rw [show C + 1 = 0 + (C + 1) from by ring, show E + 1 + 2 * 3 = (E + 6) + 1 from by ring]
    apply stepStar_trans (r3r2_chain (C+1) 0 D (E+6))
    ring_nf; finish
  · -- B=1: R1, R2×2, r3r2 chain
    rw [show (3 : ℕ) = 2 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (r1_chain 1 2 0 C D (E+1))
    rw [show (2 : ℕ) = 0 + 2 from by ring]
    apply stepStar_trans (r2_chain 2 0 (C+1) (D+1) (E+1))
    rcases C with _ | C
    · rw [show E + 1 + 2 * 2 = (E + 4) + 1 from by ring, show (0 : ℕ) + 1 = 0 + 1 from by ring]
      apply stepStar_trans (r3r2_chain 1 0 (D+1) (E+4))
      ring_nf; finish
    rw [show C + 1 + 1 = 0 + (C + 2) from by ring, show E + 1 + 2 * 2 = (E + 4) + 1 from by ring]
    apply stepStar_trans (r3r2_chain (C+2) 0 (D+1) (E+4))
    ring_nf; finish
  · -- B=2: R1×2, R2, r3r2 chain
    rw [show (3 : ℕ) = 1 + 2 from by ring, show (2 : ℕ) = 0 + 2 from by ring]
    apply stepStar_trans (r1_chain 2 1 0 C D (E+1))
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (r2_chain 1 0 (C+2) (D+2) (E+1))
    rcases C with _ | C
    · rw [show E + 1 + 2 * 1 = (E + 2) + 1 from by ring, show (0 : ℕ) + 2 = 0 + 2 from by ring]
      apply stepStar_trans (r3r2_chain 2 0 (D+2) (E+2))
      ring_nf; finish
    rw [show C + 1 + 2 = 0 + (C + 3) from by ring, show E + 1 + 2 * 1 = (E + 2) + 1 from by ring]
    apply stepStar_trans (r3r2_chain (C+3) 0 (D+2) (E+2))
    ring_nf; finish
  · -- B=B'+3: R1×3, R3, then IH on B'
    obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
    rw [show (3 : ℕ) = 0 + 3 from by ring]
    apply stepStar_trans (r1_chain 3 0 B' C D (E'+1+1))
    -- Now at (0, B', C+3, D+3, E'+1+1). R3 fires.
    rw [show C + 3 = (C + 2) + 1 from by ring, show E' + 1 + 1 = (E' + 1) + 1 from by ring]
    step fm
    -- Now at (3, B', C+2, D+3, E'+1).
    apply stepStar_trans (ih B' (by omega) (C+2) (D+3) E' (by omega))
    ring_nf; finish

-- Full transition: (0, 0, 0, n+1, E) →⁺ (0, 0, 0, n+2, E+3*n+7)
theorem full_trans (hE : E ≥ 3*n + 3) :
    ⟨0, 0, 0, n+1, E⟩ [fm]⊢⁺ ⟨0, 0, 0, n+2, E+3*n+7⟩ := by
  obtain ⟨E', rfl⟩ : ∃ E', E = E' + 3 := ⟨E - 3, by omega⟩
  -- Phase 1: d_to_b
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (n+1) 0 0 (E'+3))
  simp only [Nat.zero_add]
  -- Now at (0, n+1, 0, 0, E'+3). R5 fires (e = E'+3 = (E'+2)+1).
  rw [show E' + 3 = (E' + 2) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- Now at (1, n+2, 0, 0, E'+2). R1 fires.
  rw [show (1 : ℕ) = 0 + 1 from by ring, show n + 1 + 1 = (n + 1) + 1 from by ring]
  apply stepStar_trans (r1_chain 1 0 (n+1) 0 0 (E'+2))
  simp only [Nat.zero_add]
  -- Now at (0, n+1, 1, 1, E'+2). R3 fires (c=1=0+1, e=E'+2=(E'+1)+1).
  rw [show (1 : ℕ) = 0 + 1 from by ring, show E' + 2 = (E' + 1) + 1 from by ring]
  step fm
  -- Now at (3, n+1, 0, 1, E'+1). Apply main_drain.
  apply stepStar_trans (main_drain (n+1) 0 1 E' (by omega))
  rw [show 1 + (n + 1) = n + 2 from by ring,
      show E' + 3 * (n + 1) + 5 * 0 + 7 = E' + 3 + 3 * n + 7 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 6⟩)
  · execute fm 7
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n E, q = ⟨0, 0, 0, n+1, E⟩ ∧ E ≥ 3*n + 6)
  · intro c ⟨n, E, hq, hE⟩; subst hq
    exact ⟨⟨0, 0, 0, n+2, E+3*n+7⟩,
      ⟨n+1, E+3*n+7, rfl, by omega⟩,
      full_trans (by omega)⟩
  · exact ⟨0, 6, rfl, by omega⟩

end Sz22_2003_unofficial_619
