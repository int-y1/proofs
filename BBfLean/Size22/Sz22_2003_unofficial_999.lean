import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #999: [4/15, 33/98, 35/2, 7/11, 6/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -2  1
-1  0  1  1  0
 0  0  0  1 -1
 1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_999

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+2, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d + 2 * k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1))
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a b d e,
    ⟨a + k, b, 0, d + 2 * k, e⟩ [fm]⊢* ⟨a, b + k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) d (e + 1))
    ring_nf; finish

theorem cycle_a (a b e : ℕ) :
    ⟨a + 1, b + 2, 0, 0, e⟩ [fm]⊢* ⟨a + 2, b + 1, 0, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem cycle_b (a e : ℕ) :
    ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢* ⟨a + 2, 0, 0, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem ab_drain : ∀ b, ∀ a e,
    ⟨a + 1, b + 1, 0, 0, e⟩ [fm]⊢* ⟨a + b + 2, 0, 0, 0, e + b + 1⟩ := by
  intro b; induction' b with b ih <;> intro a e
  · exact cycle_b a e
  · rw [show b + 1 + 1 = b + 2 from by ring]
    apply stepStar_trans (cycle_a a b e)
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

theorem r3r3r2r1_step (a c e : ℕ) :
    ⟨a + 3, 0, c, 0, e⟩ [fm]⊢* ⟨a + 2, 0, c + 1, 0, e + 1⟩ := by
  rw [show a + 3 = (a + 2) + 1 from by ring]
  step fm
  rw [show a + 2 = (a + 1) + 1 from by ring]
  step fm; step fm; step fm
  ring_nf; finish

theorem r3r3r2r1_chain : ∀ k, ∀ c e,
    ⟨k + 3, 0, c, 0, e⟩ [fm]⊢* ⟨3, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · -- State: (k+1+3, 0, c, 0, e). Apply r3r3r2r1_step to get (k+3, 0, c+1, 0, e+1).
    apply stepStar_trans (r3r3r2r1_step (k + 1) c e)
    apply stepStar_trans (ih (c + 1) (e + 1))
    ring_nf; finish

theorem final_drain (c e : ℕ) :
    ⟨3, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 3, 2, e + 1⟩ := by
  step fm; step fm; step fm; step fm
  step fm; step fm
  ring_nf; finish

theorem odd_fixup (a b e : ℕ) :
    ⟨a + 1, b + 1, 0, 1, e⟩ [fm]⊢* ⟨a + 1, b + 1, 0, 0, e + 1⟩ := by
  step fm; step fm; step fm
  ring_nf; finish

-- Full drain from (k+3, 0, c, 0, e) to (0, 0, c+k+3, 2, e+k+1)
theorem full_drain (k c e : ℕ) :
    ⟨k + 3, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k + 3, 2, e + k + 1⟩ := by
  apply stepStar_trans (r3r3r2r1_chain k c e)
  apply stepStar_trans (final_drain (c + k) (e + k))
  ring_nf; finish

-- Main transition for even n = 2*m:
-- (0, 0, 2m+2, 2, 6m+2) ->+ (0, 0, 2m+3, 2, 6m+5)
theorem main_trans_even (m : ℕ) :
    ⟨0, 0, 2 * m + 2, 2, 6 * m + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * m + 3, 2, 6 * m + 5⟩ := by
  -- Phase 1: R4 drain e into d
  have h1 : ⟨0, 0, 2 * m + 2, 2, 6 * m + 2⟩ [fm]⊢* ⟨0, 0, 2 * m + 2, 6 * m + 4, 0⟩ := by
    have := r4_chain (6 * m + 2) (2 * m + 2) 2
    rw [show 2 + (6 * m + 2) = 6 * m + 4 from by ring] at this; exact this
  -- Phase 2: R5 then R1
  have h2 : ⟨0, 0, 2 * m + 2, 6 * m + 4, 0⟩ [fm]⊢⁺ ⟨3, 0, 2 * m, 6 * m + 4, 0⟩ := by
    rw [show 2 * m + 2 = (2 * m) + 1 + 1 from by ring]
    step fm; step fm; finish
  -- Phase 3: R2R1 chain (2m iterations)
  have h3 : ⟨3, 0, 2 * m, 6 * m + 4, 0⟩ [fm]⊢* ⟨2 * m + 3, 0, 0, 2 * m + 4, 2 * m⟩ := by
    have := r2r1_chain (2 * m) 2 0 (2 * m + 4) 0
    rw [show 2 + 1 = 3 from by ring,
        show 2 * m + 4 + 2 * (2 * m) = 6 * m + 4 from by ring,
        show 2 + 2 * m + 1 = 2 * m + 3 from by ring,
        show 0 + 2 * m = 2 * m from by ring] at this; exact this
  -- Phase 4: R2 chain (m+2 iterations, d even so drains to 0)
  have h4 : ⟨2 * m + 3, 0, 0, 2 * m + 4, 2 * m⟩ [fm]⊢* ⟨m + 1, m + 2, 0, 0, 3 * m + 2⟩ := by
    have := r2_chain (m + 2) (m + 1) 0 0 (2 * m)
    rw [show m + 1 + (m + 2) = 2 * m + 3 from by ring,
        show 0 + 2 * (m + 2) = 2 * m + 4 from by ring,
        show 0 + (m + 2) = m + 2 from by ring,
        show 2 * m + (m + 2) = 3 * m + 2 from by ring] at this; exact this
  -- Phase 5: ab_drain cycle
  have h5 : ⟨m + 1, m + 2, 0, 0, 3 * m + 2⟩ [fm]⊢* ⟨2 * m + 3, 0, 0, 0, 4 * m + 4⟩ := by
    have := ab_drain (m + 1) m (3 * m + 2)
    rw [show m + 1 + 1 = m + 2 from by ring,
        show m + (m + 1) + 2 = 2 * m + 3 from by ring,
        show 3 * m + 2 + (m + 1) + 1 = 4 * m + 4 from by ring] at this; exact this
  -- Phase 6: full_drain
  have h6 : ⟨2 * m + 3, 0, 0, 0, 4 * m + 4⟩ [fm]⊢* ⟨0, 0, 2 * m + 3, 2, 6 * m + 5⟩ := by
    have := full_drain (2 * m) 0 (4 * m + 4)
    rw [show 2 * m + 3 = 2 * m + 3 from rfl,
        show 0 + 2 * m + 3 = 2 * m + 3 from by ring,
        show 4 * m + 4 + 2 * m + 1 = 6 * m + 5 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

-- Main transition for odd n = 2*m+1:
-- (0, 0, 2m+3, 2, 6m+5) ->+ (0, 0, 2m+4, 2, 6m+8)
theorem main_trans_odd (m : ℕ) :
    ⟨0, 0, 2 * m + 3, 2, 6 * m + 5⟩ [fm]⊢⁺ ⟨0, 0, 2 * m + 4, 2, 6 * m + 8⟩ := by
  -- Phase 1: R4 drain
  have h1 : ⟨0, 0, 2 * m + 3, 2, 6 * m + 5⟩ [fm]⊢* ⟨0, 0, 2 * m + 3, 6 * m + 7, 0⟩ := by
    have := r4_chain (6 * m + 5) (2 * m + 3) 2
    rw [show 2 + (6 * m + 5) = 6 * m + 7 from by ring] at this; exact this
  -- Phase 2: R5 then R1
  have h2 : ⟨0, 0, 2 * m + 3, 6 * m + 7, 0⟩ [fm]⊢⁺ ⟨3, 0, 2 * m + 1, 6 * m + 7, 0⟩ := by
    rw [show 2 * m + 3 = (2 * m + 1) + 1 + 1 from by ring]
    step fm; step fm; finish
  -- Phase 3: R2R1 chain (2m+1 iterations)
  have h3 : ⟨3, 0, 2 * m + 1, 6 * m + 7, 0⟩ [fm]⊢*
      ⟨2 * m + 4, 0, 0, 2 * m + 5, 2 * m + 1⟩ := by
    have := r2r1_chain (2 * m + 1) 2 0 (2 * m + 5) 0
    rw [show 2 + 1 = 3 from by ring,
        show 2 * m + 5 + 2 * (2 * m + 1) = 6 * m + 7 from by ring,
        show 2 + (2 * m + 1) + 1 = 2 * m + 4 from by ring,
        show 0 + (2 * m + 1) = 2 * m + 1 from by ring] at this; exact this
  -- Phase 4: R2 chain (m+2 iterations, d odd so leaves d=1)
  have h4 : ⟨2 * m + 4, 0, 0, 2 * m + 5, 2 * m + 1⟩ [fm]⊢*
      ⟨m + 2, m + 2, 0, 1, 3 * m + 3⟩ := by
    have := r2_chain (m + 2) (m + 2) 0 1 (2 * m + 1)
    rw [show m + 2 + (m + 2) = 2 * m + 4 from by ring,
        show 1 + 2 * (m + 2) = 2 * m + 5 from by ring,
        show 0 + (m + 2) = m + 2 from by ring,
        show 2 * m + 1 + (m + 2) = 3 * m + 3 from by ring] at this; exact this
  -- Phase 4b: odd fixup (3 steps: R3, R1, R2)
  have h4b : ⟨m + 2, m + 2, 0, 1, 3 * m + 3⟩ [fm]⊢* ⟨m + 2, m + 2, 0, 0, 3 * m + 4⟩ := by
    have := odd_fixup (m + 1) (m + 1) (3 * m + 3)
    rw [show m + 1 + 1 = m + 2 from by ring,
        show 3 * m + 3 + 1 = 3 * m + 4 from by ring] at this; exact this
  -- Phase 5: ab_drain cycle
  have h5 : ⟨m + 2, m + 2, 0, 0, 3 * m + 4⟩ [fm]⊢* ⟨2 * m + 4, 0, 0, 0, 4 * m + 6⟩ := by
    have := ab_drain (m + 1) (m + 1) (3 * m + 4)
    rw [show m + 1 + 1 = m + 2 from by ring,
        show m + 1 + (m + 1) + 2 = 2 * m + 4 from by ring,
        show 3 * m + 4 + (m + 1) + 1 = 4 * m + 6 from by ring] at this; exact this
  -- Phase 6: full_drain
  have h6 : ⟨2 * m + 4, 0, 0, 0, 4 * m + 6⟩ [fm]⊢* ⟨0, 0, 2 * m + 4, 2, 6 * m + 8⟩ := by
    have := full_drain (2 * m + 1) 0 (4 * m + 6)
    rw [show 2 * m + 1 + 3 = 2 * m + 4 from by ring,
        show 0 + (2 * m + 1) + 3 = 2 * m + 4 from by ring,
        show 4 * m + 6 + (2 * m + 1) + 1 = 6 * m + 8 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans h4 (stepStar_trans h4b (stepStar_trans h5 h6)))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 2, 2⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 2, 3 * n + 2⟩) 0
  intro n
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    refine ⟨m + m + 1, ?_⟩
    rw [show m + m + 2 = 2 * m + 2 from by ring,
        show 3 * (m + m) + 2 = 6 * m + 2 from by ring,
        show m + m + 1 + 2 = 2 * m + 3 from by ring,
        show 3 * (m + m + 1) + 2 = 6 * m + 5 from by ring]
    exact main_trans_even m
  · subst hm
    refine ⟨2 * m + 1 + 1, ?_⟩
    rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 3 * (2 * m + 1) + 2 = 6 * m + 5 from by ring,
        show 2 * m + 1 + 1 + 2 = 2 * m + 4 from by ring,
        show 3 * (2 * m + 1 + 1) + 2 = 6 * m + 8 from by ring]
    exact main_trans_odd m
