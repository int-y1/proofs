import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #759: [35/6, 4/55, 847/2, 3/7, 5/3]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_759

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R2 with a=0 (any b)
theorem fm_r2_a0 (b c d e : ℕ) :
    fm ⟨0, b, c + 1, d, e + 1⟩ = some ⟨0 + 2, b, c, d, e⟩ := by rfl

-- R2 with generic a, b=0
theorem fm_r2_b0 (a c d e : ℕ) :
    fm ⟨a, 0, c + 1, d, e + 1⟩ = some ⟨a + 2, 0, c, d, e⟩ := by
  rcases a with _ | a <;> rfl

-- R3 chain
theorem r3_chain : ∀ k, ∀ a d e,
    ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 2))
    ring_nf; finish

-- R4 chain
theorem r4_chain : ∀ k, ∀ b d e,
    ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R2 drain with b=0
theorem r2_drain : ∀ k, ∀ a c d e,
    ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    exact stepStar_trans ⟨1, fm_r2_b0 a (c + k) d (e + k)⟩ (by
      apply stepStar_trans (ih (a + 2) c d e); ring_nf; finish)

-- R2R1R1 chain: 3-step rounds starting from a=0
-- (0, b+2k, c+1, d, e+k) ⊢* (0, b, c+k+1, d+2k, e)
theorem r2r1r1_chain : ∀ k, ∀ b c d e,
    ⟨0, b + 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, b, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    exact stepStar_trans ⟨1, fm_r2_a0 ((b + 2 * k + 1) + 1) c d (e + k)⟩ (by
      rw [show (0 + 2 : ℕ) = 1 + 1 from by ring,
          show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
      step fm
      rw [show (1 : ℕ) = 0 + 1 from by ring,
          show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
      step fm
      rw [show c + 1 + 1 = (c + 1) + 1 from by ring,
          show d + 1 + 1 = d + 2 from by ring]
      apply stepStar_trans (ih b (c + 1) (d + 2) e)
      ring_nf; finish)

-- Middle phase even: (0, 2k, 1, 0, e+k+2+k) ⊢* (2(k+1), 0, 0, 2k, e+1)
-- using r2r1r1_chain k 0 0 0 (e+k+2) then r2_drain (k+1) 0 0 (2*k) (e+1)
theorem middle_even (k e : ℕ) :
    ⟨0, 2 * k, 1, 0, e + 2 * k + 2⟩ [fm]⊢* ⟨2 * k + 2, 0, 0, 2 * k, e + 1⟩ := by
  -- Use r2r1r1_chain k 0 0 0 (e+k+2):
  -- (0, 0+2k, 0+1, 0, (e+k+2)+k) ⊢* (0, 0, 0+k+1, 0+2k, e+k+2)
  -- We need: (0, 2k, 1, 0, e+2k+2) = (0, 0+2k, 0+1, 0, (e+k+2)+k)
  -- and: (0, 0, k+1, 2k, e+k+2) ⊢* (2k+2, 0, 0, 2k, e+1)
  -- The second part is r2_drain (k+1) 0 0 (2k) (e+1):
  -- (0, 0, 0+(k+1), 2k, (e+1)+(k+1)) ⊢* (0+2(k+1), 0, 0, 2k, e+1)
  -- We need: (0, 0, k+1, 2k, e+k+2) = (0, 0, 0+(k+1), 2k, (e+1)+(k+1))
  -- 0+(k+1) = k+1 ✓, (e+1)+(k+1) = e+k+2 ✓, 0+2(k+1) = 2k+2 ✓
  have step1 : ⟨0, 0 + 2 * k, 0 + 1, 0, (e + k + 2) + k⟩ [fm]⊢*
      ⟨0, 0, 0 + k + 1, 0 + 2 * k, e + k + 2⟩ := r2r1r1_chain k 0 0 0 (e + k + 2)
  have step2 : ⟨0, 0, 0 + (k + 1), 2 * k, (e + 1) + (k + 1)⟩ [fm]⊢*
      ⟨0 + 2 * (k + 1), 0, 0, 2 * k, e + 1⟩ := r2_drain (k + 1) 0 0 (2 * k) (e + 1)
  have h1 : (0 + 2 * k : ℕ) = 2 * k := by ring
  have h2 : (0 + 1 : ℕ) = 1 := by ring
  have h3 : (e + k + 2 + k : ℕ) = e + 2 * k + 2 := by ring
  rw [show (0 + 2 * k : ℕ) = 2 * k from by ring,
      show (0 + 1 : ℕ) = 1 from by ring,
      show (e + k + 2 + k : ℕ) = e + 2 * k + 2 from by ring] at step1
  rw [show (0 + (k + 1) : ℕ) = k + 1 from by ring,
      show ((e + 1) + (k + 1) : ℕ) = e + k + 2 from by ring,
      show (0 + 2 * (k + 1) : ℕ) = 2 * k + 2 from by ring] at step2
  rw [show (0 + k + 1 : ℕ) = k + 1 from by ring] at step1
  exact stepStar_trans step1 step2

-- Middle phase odd: (0, 2k+1, 1, 0, e+2k+3) ⊢* (2k+3, 0, 0, 2k+1, e+1)
theorem middle_odd (k e : ℕ) :
    ⟨0, 2 * k + 1, 1, 0, e + 2 * k + 3⟩ [fm]⊢* ⟨2 * k + 3, 0, 0, 2 * k + 1, e + 1⟩ := by
  -- r2r1r1_chain k 1 0 0 (e+k+3):
  -- (0, 1+2k, 0+1, 0, (e+k+3)+k) ⊢* (0, 1, 0+k+1, 0+2k, e+k+3)
  have step1 : ⟨0, 1 + 2 * k, 0 + 1, 0, (e + k + 3) + k⟩ [fm]⊢*
      ⟨0, 1, 0 + k + 1, 0 + 2 * k, e + k + 3⟩ := r2r1r1_chain k 1 0 0 (e + k + 3)
  rw [show (1 + 2 * k : ℕ) = 2 * k + 1 from by ring,
      show (0 + 1 : ℕ) = 1 from by ring,
      show (e + k + 3 + k : ℕ) = e + 2 * k + 3 from by ring,
      show (0 + k + 1 : ℕ) = k + 1 from by ring,
      show (0 + 2 * k : ℕ) = 2 * k from by ring] at step1
  apply stepStar_trans step1
  -- State: (0, 1, k+1, 2k, e+k+3)
  -- R2 with a=0, b=1
  rw [show k + 1 = (k) + 1 from by ring,
      show e + k + 3 = (e + k + 2) + 1 from by ring]
  exact stepStar_trans ⟨1, fm_r2_a0 1 k (2 * k) (e + k + 2)⟩ (by
    rw [show (0 + 2 : ℕ) = 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    -- R1: (1+1, 0+1, k, 2k, e+k+2) → (1, 0, k+1, 2k+1, e+k+2)
    exact stepStar_trans ⟨1, by
      show fm ⟨1 + 1, 0 + 1, k, 2 * k, e + k + 2⟩ =
        some ⟨1, 0, k + 1, 2 * k + 1, e + k + 2⟩; rfl⟩ (by
      -- State: (1, 0, k+1, 2k+1, e+k+2)
      -- r2_drain (k+1) 1 0 (2k+1) (e+1):
      -- (1, 0, 0+(k+1), 2k+1, (e+1)+(k+1)) ⊢* (1+2(k+1), 0, 0, 2k+1, e+1)
      have step2 : ⟨1, 0, 0 + (k + 1), 2 * k + 1, (e + 1) + (k + 1)⟩ [fm]⊢*
          ⟨1 + 2 * (k + 1), 0, 0, 2 * k + 1, e + 1⟩ := r2_drain (k + 1) 1 0 (2 * k + 1) (e + 1)
      rw [show (0 + (k + 1) : ℕ) = k + 1 from by ring,
          show ((e + 1) + (k + 1) : ℕ) = e + k + 2 from by ring,
          show (1 + 2 * (k + 1) : ℕ) = 2 * k + 3 from by ring] at step2
      exact step2))

-- Full middle phase: (0, d+1, 0, 0, e+d+2) ⊢* (d+2, 0, 0, d, e+1)
theorem middle_phase (d e : ℕ) :
    ⟨0, d + 1, 0, 0, e + d + 2⟩ [fm]⊢* ⟨d + 2, 0, 0, d, e + 1⟩ := by
  -- R5
  exact stepStar_trans ⟨1, by
    show fm ⟨0, (d) + 1, 0, 0, e + d + 2⟩ = some ⟨0, d, 0 + 1, 0, e + d + 2⟩; rfl⟩ (by
    rw [show (0 + 1 : ℕ) = 1 from by ring]
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      rw [show k + k = 2 * k from by ring] at *
      have h := middle_even k e
      rw [show e + 2 * k + 2 = e + 2 * k + 2 from rfl] at h
      exact h
    · subst hk
      have h := middle_odd k e
      rw [show e + (2 * k + 1) + 2 = e + 2 * k + 3 from by ring,
          show 2 * k + 1 + 2 = 2 * k + 3 from by ring]
      exact h)

-- Main transition: (0, 0, 0, d+1, e+d+2) ⊢⁺ (0, 0, 0, 2d+2, 2d+e+5)
theorem main_trans (d e : ℕ) :
    ⟨0, 0, 0, d + 1, e + d + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 2, 2 * d + e + 5⟩ := by
  -- First R4 step (gives ⊢⁺)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, (d) + 1, e + d + 2⟩ = some ⟨0, 0 + 1, 0, d, e + d + 2⟩; rfl
  rw [show (0 + 1 : ℕ) = 1 from by ring]
  -- Remaining R4 steps
  have h1 := r4_chain d 1 0 (e + d + 2)
  rw [show (0 + d : ℕ) = d from by ring] at h1
  apply stepStar_trans h1
  rw [show 1 + d = d + 1 from by ring]
  -- Middle phase
  apply stepStar_trans (middle_phase d e)
  -- R3 chain
  rw [show d + 2 = 0 + (d + 2) from by ring]
  apply stepStar_trans (r3_chain (d + 2) 0 d (e + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 0, p.1 + 1, p.2 + p.1 + 2⟩) ⟨0, 0⟩
  intro ⟨d, e⟩
  refine ⟨⟨2 * d + 1, e + 2⟩, ?_⟩
  show ⟨0, 0, 0, d + 1, e + d + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, (2 * d + 1) + 1, (e + 2) + (2 * d + 1) + 2⟩
  convert main_trans d e using 2
  ring_nf

end Sz22_2003_unofficial_759
