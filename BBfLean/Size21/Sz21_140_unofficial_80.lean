import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #80: [5/6, 44/35, 49/2, 9/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  2  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_80

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 repeated: a → d (each a gives d+2)
theorem a_to_d : ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+2*k, e⟩ := by
  have many_step : ∀ k d, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+2*k, e⟩ := by
    intro k; induction' k with k ih <;> intro d
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih _); ring_nf; finish
  exact many_step k d

-- R4 repeated: e → b (each e gives b+2)
theorem e_to_b : ⟨0, b, 0, d, e+k⟩ [fm]⊢* ⟨0, b+2*k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d, e+k⟩ [fm]⊢* ⟨0, b+2*k, 0, d, e⟩ := by
    intro k; induction' k with k ih <;> intro b
    · exists 0
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih _); ring_nf; finish
  exact many_step k b

-- R1 repeated: a,b → c (each step consumes 1 a, 1 b, produces 1 c)
theorem ab_to_c : ⟨a+k, b+k, c, d, e⟩ [fm]⊢* ⟨a, b, c+k, d, e⟩ := by
  have many_step : ∀ k a b c, ⟨a+k, b+k, c, d, e⟩ [fm]⊢* ⟨a, b, c+k, d, e⟩ := by
    intro k; induction' k with k ih <;> intro a b c
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih _ _ _); ring_nf; finish
  exact many_step k a b c

-- R2 repeated: c,d → a,e (b=0, so R1 never fires before R2)
theorem cd_to_ae : ⟨a, 0, c+k, d+k, e⟩ [fm]⊢* ⟨a+2*k, 0, c, d, e+k⟩ := by
  have many_step : ∀ k a c e, ⟨a, 0, c+k, d+k, e⟩ [fm]⊢* ⟨a+2*k, 0, c, d, e+k⟩ := by
    intro k; induction' k with k ih <;> intro a c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih _ _ _); ring_nf; finish
  exact many_step k a c e

-- R2+R1+R1 loop: each round does b-2, c+1, d-1, e+1
-- From (0, 2*k, c+1, d+k, e) →* (0, 0, c+k+1, d, e+k)
theorem r2r1_loop : ⟨0, 2*k, c+1, d+k, e⟩ [fm]⊢* ⟨0, 0, c+k+1, d, e+k⟩ := by
  have many_step : ∀ k c e, ⟨0, 2*k, c+1, d+k, e⟩ [fm]⊢* ⟨0, 0, c+k+1, d, e+k⟩ := by
    intro k; induction' k with k ih <;> intro c e
    · exists 0
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R2
    rw [show 2 * k + 1 + 1 = (2 * k + 1) + 1 from by ring]
    step fm  -- R1
    step fm  -- R1
    apply stepStar_trans (ih _ _); ring_nf; finish
  exact many_step k c e

-- Main transition: (e+1, 0, 0, 0, e) →⁺ (2e+2, 0, 0, 0, 2e+1)
theorem main_step (e : ℕ) : (⟨e+1, 0, 0, 0, e⟩ : Q) [fm]⊢⁺ ⟨2*e+2, 0, 0, 0, 2*e+1⟩ := by
  -- Phase 1: R3 × (e+1): (e+1, 0, 0, 0, e) →* (0, 0, 0, 2*(e+1), e)
  have h1 : (⟨e+1, 0, 0, 0, e⟩ : Q) [fm]⊢* ⟨0, 0, 0, 2*(e+1), e⟩ := by
    have h := a_to_d (a := 0) (k := e+1) (d := 0) (e := e)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 × e: (0, 0, 0, 2*(e+1), e) →* (0, 2*e, 0, 2*(e+1), 0)
  have h2 : (⟨0, 0, 0, 2*(e+1), e⟩ : Q) [fm]⊢* ⟨0, 2*e, 0, 2*(e+1), 0⟩ := by
    have h := e_to_b (b := 0) (d := 2*(e+1)) (e := 0) (k := e)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5, R2: (0, 2*e, 0, 2*(e+1), 0) →⁺ (2, 2*e, 0, 2*e, 1)
  have h3 : (⟨0, 2*e, 0, 2*(e+1), 0⟩ : Q) [fm]⊢⁺ ⟨2, 2*e, 0, 2*e, 1⟩ := by
    rw [show 2*(e+1) = (2*e+1) + 1 from by ring]
    step fm
    rw [show 2*e+1 = 2*e + 1 from by ring]
    step fm; finish
  -- Combine phases 1-3
  have h123 : (⟨e+1, 0, 0, 0, e⟩ : Q) [fm]⊢⁺ ⟨2, 2*e, 0, 2*e, 1⟩ :=
    stepStar_stepPlus_stepPlus (stepStar_trans h1 h2) h3
  rcases e with _ | e'
  · -- e=0: (2, 0, 0, 0, 1) is the target
    exact h123
  · -- e ≥ 1
    -- Phase 4: R1×2: (2, 2*(e'+1), 0, 2*(e'+1), 1) →* (0, 2*e', 2, 2*(e'+1), 1)
    have h4 : (⟨2, 2*(e'+1), 0, 2*(e'+1), 1⟩ : Q) [fm]⊢* ⟨0, 2*e', 2, 2*(e'+1), 1⟩ := by
      have h := ab_to_c (a := 0) (b := 2*e') (c := 0) (d := 2*(e'+1)) (e := 1) (k := 2)
      simp only [Nat.zero_add] at h
      rw [show 2*e' + 2 = 2*(e'+1) from by ring] at h; exact h
    -- Phase 5: r2r1_loop
    have h5 : (⟨0, 2*e', 2, 2*(e'+1), 1⟩ : Q) [fm]⊢* ⟨0, 0, e'+2, e'+2, e'+1⟩ := by
      have h := r2r1_loop (d := e'+2) (k := e') (c := 1) (e := 1)
      rw [show 1 + 1 = 2 from rfl,
          show (e'+2) + e' = 2*(e'+1) from by ring,
          show 1 + e' + 1 = e'+2 from by ring,
          show 1 + e' = e'+1 from by ring] at h; exact h
    -- Phase 6: cd_to_ae: (0, 0, e'+2, e'+2, e'+1) →* (2*(e'+1)+2, 0, 0, 0, 2*(e'+1)+1)
    have h6 : (⟨0, 0, e'+2, e'+2, e'+1⟩ : Q) [fm]⊢* ⟨2*(e'+1)+2, 0, 0, 0, 2*(e'+1)+1⟩ := by
      have h := cd_to_ae (a := 0) (d := 0) (c := 0) (e := e'+1) (k := e'+2)
      simp only [Nat.zero_add] at h
      rw [show 2*(e'+2) = 2*(e'+1)+2 from by ring,
          show (e'+1)+(e'+2) = 2*(e'+1)+1 from by ring] at h; exact h
    -- Combine all phases
    exact stepPlus_stepStar_stepPlus h123 (stepStar_trans h4 (stepStar_trans h5 h6))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun e ↦ ⟨e+1, 0, 0, 0, e⟩) 1
  intro e
  exact ⟨2*e+1, main_step e⟩
