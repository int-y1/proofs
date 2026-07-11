import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #974: [4/15, 33/14, 55/2, 7/121, 6/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  1
 0  0  0  1 -2
 1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_974

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- Phase: R3 chain. a decreases, c and e increase.
theorem r3_chain : ∀ k, ∀ c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 1) (e + 1))
    ring_nf; finish

-- Phase: R4 chain. e decreases by 2, d increases by 1.
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d, e + 2 * k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    rw [show (e + 2 * k) + 2 = e + 2 * k + 2 from by ring]
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    rw [show e + 2 * k + 2 = (e + 2 * k) + 1 + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) e)
    ring_nf; finish

-- Phase: R2+R1 interleaved chain. Eats c and d simultaneously.
-- From (a+1, 0, c+k, d+k, e) to (a+k+1, 0, c, d, e+k)
theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1))
    ring_nf; finish

-- Phase: R2 drain. Drains d into b and e.
theorem r2_drain : ∀ k, ∀ a b e,
    ⟨a + k, b, 0, k, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (b + 1) (e + 1))
    ring_nf; finish

-- Phase: R3+R1 chain. When b>0, R3 then R1 alternate.
theorem r3r1_chain : ∀ k, ∀ a b e,
    ⟨a + 1, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 1) b (e + 1))
    ring_nf; finish

-- Main transition for even n: C(2*m) ⊢⁺ C(2*m+1)
-- C(n) = (n+2, 0, 0, 0, 2*n+2)
-- C(2m) = (2m+2, 0, 0, 0, 4m+2) ⊢⁺ C(2m+1) = (2m+3, 0, 0, 0, 4m+4)
theorem main_trans_even (m : ℕ) :
    ⟨2*m+2, 0, 0, 0, 4*m+2⟩ [fm]⊢⁺ ⟨2*m+3, 0, 0, 0, 4*m+4⟩ := by
  -- Phase 1: R3 chain (2m+2 steps)
  -- (2m+2, 0, 0, 0, 4m+2) →* (0, 0, 2m+2, 0, 6m+4)
  have h1 : ⟨2*m+2, 0, 0, 0, 4*m+2⟩ [fm]⊢* ⟨0, 0, 2*m+2, 0, 6*m+4⟩ := by
    have := r3_chain (2*m+2) 0 (4*m+2)
    rw [show 0 + (2 * m + 2) = 2 * m + 2 from by ring,
        show 4 * m + 2 + (2 * m + 2) = 6 * m + 4 from by ring] at this
    exact this
  -- Phase 2: R4 chain (3m+2 steps). 6m+4 = 2*(3m+2) + 0
  -- (0, 0, 2m+2, 0, 6m+4) →* (0, 0, 2m+2, 3m+2, 0)
  have h2 : ⟨0, 0, 2*m+2, 0, 6*m+4⟩ [fm]⊢* ⟨0, 0, 2*m+2, 3*m+2, 0⟩ := by
    have := r4_chain (3*m+2) (2*m+2) 0 0
    rw [show 0 + 2 * (3 * m + 2) = 6 * m + 4 from by ring,
        show 0 + (3 * m + 2) = 3 * m + 2 from by ring] at this
    exact this
  -- Phase 3: R5 + R1
  -- (0, 0, 2m+2, 3m+2, 0) → (1, 1, 2m+1, 3m+2, 0) → (3, 0, 2m, 3m+2, 0)
  have h3 : ⟨0, 0, 2*m+2, 3*m+2, 0⟩ [fm]⊢⁺ ⟨3, 0, 2*m, 3*m+2, 0⟩ := by
    rw [show 2*m+2 = (2*m+1) + 1 from by ring]
    step fm
    rw [show 2*m+1 = (2*m) + 1 from by ring]
    step fm
    ring_nf; finish
  -- Phase 4: R2+R1 chain (2m rounds)
  -- (3, 0, 2m, 3m+2, 0) →* (2m+3, 0, 0, m+2, 2m)
  have h4 : ⟨3, 0, 2*m, 3*m+2, 0⟩ [fm]⊢* ⟨2*m+3, 0, 0, m+2, 2*m⟩ := by
    have := r2r1_chain (2*m) 2 0 (m+2) 0
    convert this using 2; ring_nf
  -- Phase 5: R2 drain (m+2 steps)
  -- (2m+3, 0, 0, m+2, 2m) →* (m+1, m+2, 0, 0, 3m+2)
  have h5 : ⟨2*m+3, 0, 0, m+2, 2*m⟩ [fm]⊢* ⟨m+1, m+2, 0, 0, 3*m+2⟩ := by
    have := r2_drain (m+2) (m+1) 0 (2*m)
    rw [show m + 1 + (m + 2) = 2 * m + 3 from by ring,
        show 0 + (m + 2) = m + 2 from by ring,
        show 2 * m + (m + 2) = 3 * m + 2 from by ring] at this
    exact this
  -- Phase 6: R3+R1 chain (m+2 rounds)
  -- (m+1, m+2, 0, 0, 3m+2) →* (2m+3, 0, 0, 0, 4m+4)
  have h6 : ⟨m+1, m+2, 0, 0, 3*m+2⟩ [fm]⊢* ⟨2*m+3, 0, 0, 0, 4*m+4⟩ := by
    have := r3r1_chain (m+2) (m) 0 (3*m+2)
    rw [show m + 1 = m + 1 from rfl,
        show 0 + (m + 2) = m + 2 from by ring,
        show m + (m + 2) + 1 = 2 * m + 3 from by ring,
        show 3 * m + 2 + (m + 2) = 4 * m + 4 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus (stepStar_trans h1 h2)
    (stepPlus_stepStar_stepPlus h3
      (stepStar_trans h4 (stepStar_trans h5 h6)))

-- Main transition for odd n: C(2*m+1) ⊢⁺ C(2*m+2)
-- C(2m+1) = (2m+3, 0, 0, 0, 4m+4) ⊢⁺ C(2m+2) = (2m+4, 0, 0, 0, 4m+6)
theorem main_trans_odd (m : ℕ) :
    ⟨2*m+3, 0, 0, 0, 4*m+4⟩ [fm]⊢⁺ ⟨2*m+4, 0, 0, 0, 4*m+6⟩ := by
  -- Phase 1: R3 chain (2m+3 steps)
  -- (2m+3, 0, 0, 0, 4m+4) →* (0, 0, 2m+3, 0, 6m+7)
  have h1 : ⟨2*m+3, 0, 0, 0, 4*m+4⟩ [fm]⊢* ⟨0, 0, 2*m+3, 0, 6*m+7⟩ := by
    have := r3_chain (2*m+3) 0 (4*m+4)
    rw [show 0 + (2 * m + 3) = 2 * m + 3 from by ring,
        show 4 * m + 4 + (2 * m + 3) = 6 * m + 7 from by ring] at this
    exact this
  -- Phase 2: R4 chain (3m+3 steps). 6m+7 = 2*(3m+3) + 1
  -- (0, 0, 2m+3, 0, 6m+7) →* (0, 0, 2m+3, 3m+3, 1)
  have h2 : ⟨0, 0, 2*m+3, 0, 6*m+7⟩ [fm]⊢* ⟨0, 0, 2*m+3, 3*m+3, 1⟩ := by
    have := r4_chain (3*m+3) (2*m+3) 0 1
    rw [show 1 + 2 * (3 * m + 3) = 6 * m + 7 from by ring,
        show 0 + (3 * m + 3) = 3 * m + 3 from by ring] at this
    exact this
  -- Phase 3: R5 + R1
  -- (0, 0, 2m+3, 3m+3, 1) → (1, 1, 2m+2, 3m+3, 1) → (3, 0, 2m+1, 3m+3, 1)
  have h3 : ⟨0, 0, 2*m+3, 3*m+3, 1⟩ [fm]⊢⁺ ⟨3, 0, 2*m+1, 3*m+3, 1⟩ := by
    rw [show 2*m+3 = (2*m+2) + 1 from by ring]
    step fm
    rw [show 2*m+2 = (2*m+1) + 1 from by ring]
    step fm
    ring_nf; finish
  -- Phase 4: R2+R1 chain (2m+1 rounds)
  -- (3, 0, 2m+1, 3m+3, 1) →* (2m+4, 0, 0, m+2, 2m+2)
  have h4 : ⟨3, 0, 2*m+1, 3*m+3, 1⟩ [fm]⊢* ⟨2*m+4, 0, 0, m+2, 2*m+2⟩ := by
    have := r2r1_chain (2*m+1) 2 0 (m+2) 1
    rw [show 2 + 1 = 3 from by ring,
        show 0 + (2 * m + 1) = 2 * m + 1 from by ring,
        show (m + 2) + (2 * m + 1) = 3 * m + 3 from by ring,
        show 2 + (2 * m + 1) + 1 = 2 * m + 4 from by ring,
        show 1 + (2 * m + 1) = 2 * m + 2 from by ring] at this
    exact this
  -- Phase 5: R2 drain (m+2 steps)
  -- (2m+4, 0, 0, m+2, 2m+2) →* (m+2, m+2, 0, 0, 3m+4)
  have h5 : ⟨2*m+4, 0, 0, m+2, 2*m+2⟩ [fm]⊢* ⟨m+2, m+2, 0, 0, 3*m+4⟩ := by
    have := r2_drain (m+2) (m+2) 0 (2*m+2)
    rw [show m + 2 + (m + 2) = 2 * m + 4 from by ring,
        show 0 + (m + 2) = m + 2 from by ring,
        show 2 * m + 2 + (m + 2) = 3 * m + 4 from by ring] at this
    exact this
  -- Phase 6: R3+R1 chain (m+2 rounds)
  -- (m+2, m+2, 0, 0, 3m+4) →* (2m+4, 0, 0, 0, 4m+6)
  have h6 : ⟨m+2, m+2, 0, 0, 3*m+4⟩ [fm]⊢* ⟨2*m+4, 0, 0, 0, 4*m+6⟩ := by
    have := r3r1_chain (m+2) (m+1) 0 (3*m+4)
    rw [show m + 1 + 1 = m + 2 from by ring,
        show 0 + (m + 2) = m + 2 from by ring,
        show m + 1 + (m + 2) + 1 = 2 * m + 4 from by ring,
        show 3 * m + 4 + (m + 2) = 4 * m + 6 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus (stepStar_trans h1 h2)
    (stepPlus_stepStar_stepPlus h3
      (stepStar_trans h4 (stepStar_trans h5 h6)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * n + 2⟩) 0
  intro n
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- even case: n = m + m
    subst hm
    refine ⟨m + m + 1, ?_⟩
    rw [show m + m + 2 = 2 * m + 2 from by ring,
        show 2 * (m + m) + 2 = 4 * m + 2 from by ring,
        show m + m + 1 + 2 = 2 * m + 3 from by ring,
        show 2 * (m + m + 1) + 2 = 4 * m + 4 from by ring]
    exact main_trans_even m
  · -- odd case: n = 2*m + 1
    subst hm
    refine ⟨2 * m + 1 + 1, ?_⟩
    rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 2 * (2 * m + 1) + 2 = 4 * m + 4 from by ring,
        show 2 * m + 1 + 1 + 2 = 2 * m + 4 from by ring,
        show 2 * (2 * m + 1 + 1) + 2 = 4 * m + 6 from by ring]
    exact main_trans_odd m
