import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #250: [135/2, 4/35, 11/5, 7/99, 5/3]

Vector representation:
```
-1  3  1  0  0
 2  0 -1 -1  0
 0  0 -1  0  1
 0 -2  0  1 -1
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_250

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+2, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: (0, b+2*k, 0, d, e+k) →* (0, b, 0, d+k, e)
theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b + 2 * k, 0, d, e + k⟩ [fm]⊢* ⟨0, b, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R2+R1+R1 chain: (0, b, c+1, k+1, 0) →* (0, b+6*(k+1), c+k+2, 0, 0)
theorem r211_chain : ∀ k, ∀ b c, ⟨0, b, c + 1, k + 1, 0⟩ [fm]⊢* ⟨0, b + 6 * (k + 1), c + k + 2, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · step fm; step fm; step fm; ring_nf; finish
  rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3 chain: (0, b, c+k, 0, e) →* (0, b, c, 0, e+k)
theorem r3_chain : ∀ k, ∀ b c e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase B: R5 + R2R1R1 chain + R3 chain
-- (0, b+1, 0, e+1, 0) →⁺ (0, b+6*(e+1), 0, 0, e+2)
theorem phase_b (b e : ℕ) :
    ⟨0, b + 1, 0, e + 1, 0⟩ [fm]⊢⁺ ⟨0, b + 6 * (e + 1), 0, 0, e + 2⟩ := by
  -- R5: (0, b+1, 0, e+1, 0) → (0, b, 1, e+1, 0)
  apply step_stepStar_stepPlus (by (try unfold fm); (try simp only); rfl)
  -- R2+R1+R1 chain: (0, b, 1, e+1, 0) →* (0, b+6*(e+1), e+2, 0, 0)
  apply stepStar_trans (r211_chain e b 0)
  simp only [Nat.zero_add]
  -- R3 chain: (0, b+6*(e+1), e+2, 0, 0) →* (0, b+6*(e+1), 0, 0, e+2)
  rw [show (e + 2 : ℕ) = 0 + (e + 2) from by ring]
  apply stepStar_trans (r3_chain (e + 2) (b + 6 * (e + 1)) 0 0)
  simp only [Nat.zero_add]; finish

-- Main transition: (0, B, 0, 0, E+1) →⁺ (0, B+4*E+3, 0, 0, E+2)
-- when B ≥ 2*E+3
theorem main_trans (b e : ℕ) (hb : b ≥ 2 * e + 3) :
    ⟨0, b, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨0, b + 4 * e + 3, 0, 0, e + 2⟩ := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hb
  subst hr
  -- Phase A: R4 chain (e+1 steps)
  have h1 : ⟨0, 2 * e + 3 + r, 0, 0, e + 1⟩ [fm]⊢*
             ⟨0, r + 1, 0, e + 1, 0⟩ := by
    have h := r4_chain (e + 1) (r + 1) 0 0
    simp only [Nat.zero_add] at h
    rw [show 2 * e + 3 + r = r + 1 + 2 * (e + 1) from by ring]
    exact h
  -- Phase B: (0, r+1, 0, e+1, 0) →⁺ (0, r+6*(e+1), 0, 0, e+2)
  have h2 := phase_b r e
  -- Combine: need r+6*(e+1) = 2*e+3+r+4*e+3
  have h3 : 2 * e + 3 + r + 4 * e + 3 = r + 6 * (e + 1) := by ring
  rw [h3]
  exact stepStar_stepPlus_stepPlus h1 h2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 3, 0, 0, 1⟩)
  · execute fm 2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b e, q = ⟨0, b, 0, 0, e + 1⟩ ∧ b ≥ 2 * e + 3)
  · intro q ⟨b, e, hq, hb⟩
    subst hq
    exact ⟨⟨0, b + 4 * e + 3, 0, 0, e + 2⟩,
           ⟨b + 4 * e + 3, e + 1, by ring_nf, by omega⟩,
           main_trans b e hb⟩
  · exact ⟨3, 0, rfl, by omega⟩

end Sz22_2003_unofficial_250
