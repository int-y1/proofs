import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #138: [1/45, 196/33, 15/7, 1/3, 99/2]

Vector representation:
```
 0 -2 -1  0  0
 2 -1  0  2 -1
 0  1  1 -1  0
 0 -1  0  0  0
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_138

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- R3+R2 chain: k iterations of (R3 then R2)
-- (a, 0, c, d+1, k) →* (a+2*k, 0, c+k, d+k+1, 0)
theorem r3r2_chain : ∀ k a c d,
    ⟨a, 0, c, d+1, k⟩ [fm]⊢* ⟨a+2*k, 0, c+k, d+k+1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih (a + 2) (c + 1) (d + 1))
  ring_nf; finish

-- d-drain generalized: (a, 0, c, d+2*k, 0) →* (a, 0, c+k, d, 0)
theorem d_drain_gen : ∀ k a c d,
    ⟨a, 0, c, d+2*k, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
  apply stepStar_trans (ih a c (d + 2))
  step fm; step fm; step fm; ring_nf; finish

-- d-drain tail: (a, 0, c, 1, 0) →* (a, 0, c+1, 0, 0)
theorem d_drain_one : ∀ a c,
    ⟨a, 0, c, 1, 0⟩ [fm]⊢* ⟨a, 0, c+1, 0, 0⟩ := by
  intro a c; step fm; step fm; finish

-- c-drain: (a+k, 0, k, 0, e) →* (a, 0, 0, 0, e+k)
theorem c_drain : ∀ k a e,
    ⟨a+k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih a (e + 1))
  ring_nf; finish

-- e=0 step: (a+1, 0, 0, 0, 0) →⁺ (a+1, 0, 0, 0, 1)
theorem e0_step : ∀ a,
    ⟨a+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+1, 0, 0, 0, 1⟩ := by
  intro a; execute fm 8

-- Odd E transition: E=2m+1
-- (a+1, 0, 0, 0, 2*m+1) →⁺ (a+m+2, 0, 0, 0, 3*m+2)
theorem odd_e_trans : ∀ m a,
    ⟨a+1, 0, 0, 0, 2*m+1⟩ [fm]⊢⁺ ⟨a+m+2, 0, 0, 0, 3*m+2⟩ := by
  intro m a
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 0, 2 * m + 1⟩ = some ⟨a, 2, 0, 0, 2 * m + 2⟩; rfl
  step fm; step fm
  -- Now at (a+4, 0, 0, 4, 2*m) = (a+4, 0, 0, 3+1, 2*m)
  -- Phase 2: R3+R2 chain with k=2*m
  rw [show (4 : ℕ) = 3 + 1 from rfl]
  apply stepStar_trans (r3r2_chain (2*m) (a+4) 0 3)
  -- Now at (a+4+2*(2*m), 0, 0+2*m, 3+2*m+1, 0)
  -- = (a+4*m+4, 0, 2*m, 2*m+4, 0)
  -- Phase 3: d-drain, d=2*m+4=2*(m+2), using d_drain_gen with d=0
  rw [show 3 + 2 * m + 1 = 0 + 2 * (m + 2) from by ring]
  apply stepStar_trans (d_drain_gen (m+2) (a + 4 + 2 * (2 * m)) (0 + 2 * m) 0)
  simp only [Nat.zero_add]
  -- Now at (a+4+4*m, 0, 2*m+m+2, 0, 0) = (a+4*m+4, 0, 3*m+2, 0, 0)
  -- Phase 4: c-drain
  rw [show a + 4 + 2 * (2 * m) = (a + m + 2) + (3 * m + 2) from by ring,
      show 2 * m + (m + 2) = 3 * m + 2 from by ring]
  apply stepStar_trans (c_drain (3*m+2) (a+m+2) 0)
  ring_nf; finish

-- Even E transition: E=2*m+2
-- (a+1, 0, 0, 0, 2*m+2) →⁺ (a+m+2, 0, 0, 0, 3*m+4)
theorem even_e_trans : ∀ m a,
    ⟨a+1, 0, 0, 0, 2*m+2⟩ [fm]⊢⁺ ⟨a+m+2, 0, 0, 0, 3*m+4⟩ := by
  intro m a
  -- Phase 1: init (3 steps): →* (a+4, 0, 0, 4, 2*m+1)
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 0, (2 * m + 1) + 1⟩ = some ⟨a, 2, 0, 0, (2 * m + 1) + 2⟩; rfl
  step fm; step fm
  -- Now at (a+4, 0, 0, 4, 2*m+1) = (a+4, 0, 0, 3+1, 2*m+1)
  -- Phase 2: R3+R2 chain with k=2*m+1
  rw [show (4 : ℕ) = 3 + 1 from rfl]
  apply stepStar_trans (r3r2_chain (2*m+1) (a+4) 0 3)
  -- Now at (a+4+2*(2*m+1), 0, 0+(2*m+1), 3+(2*m+1)+1, 0)
  -- = (a+4*m+6, 0, 2*m+1, 2*m+5, 0)
  -- Phase 3: d-drain odd, d=2*m+5=2*(m+2)+1
  -- First drain even part via d_drain_gen with d=1: (A, 0, c, 1+2*(m+2), 0) →* (A, 0, c+m+2, 1, 0)
  -- Then d_drain_one
  rw [show 3 + (2 * m + 1) + 1 = 1 + 2 * (m + 2) from by ring]
  apply stepStar_trans (d_drain_gen (m+2) (a + 4 + 2 * (2 * m + 1)) (0 + (2 * m + 1)) 1)
  simp only [Nat.zero_add]
  apply stepStar_trans (d_drain_one (a + 4 + 2 * (2 * m + 1)) (2 * m + 1 + (m + 2)))
  -- Now at (a+4*m+6, 0, 2*m+1+m+2+1, 0, 0) = (a+4*m+6, 0, 3*m+4, 0, 0)
  -- Phase 4: c-drain
  rw [show a + 4 + 2 * (2 * m + 1) = (a + m + 2) + (3 * m + 4) from by ring,
      show 2 * m + 1 + (m + 2) + 1 = 3 * m + 4 from by ring]
  apply stepStar_trans (c_drain (3*m+4) (a+m+2) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fun q ↦ ∃ a e, q = (⟨a+1, 0, 0, 0, e⟩ : Q))
  · intro q ⟨a, e, hq⟩
    subst hq
    rcases e with _ | e
    · -- e = 0
      exact ⟨⟨a+1, 0, 0, 0, 1⟩, ⟨a, 1, rfl⟩, e0_step a⟩
    · -- e = e + 1 ≥ 1
      rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- e even, e = m+m, E = e+1 = 2*m+1 (odd)
        subst hm
        rw [show m + m + 1 = 2 * m + 1 from by ring]
        exact ⟨⟨a+m+2, 0, 0, 0, 3*m+2⟩, ⟨a+m+1, 3*m+2, by ring_nf⟩, odd_e_trans m a⟩
      · -- e odd, e = 2*m+1, E = e+1 = 2*m+2 (even)
        subst hm
        rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring]
        exact ⟨⟨a+m+2, 0, 0, 0, 3*m+4⟩, ⟨a+m+1, 3*m+4, by ring_nf⟩, even_e_trans m a⟩
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_138
