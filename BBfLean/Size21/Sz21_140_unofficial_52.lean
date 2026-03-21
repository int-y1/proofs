import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #52: [35/6, 4/55, 847/2, 3/7, 5/3]

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

namespace Sz21_140_unofficial_52

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: d → b (when a=0, c=0)
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b d

-- R3 repeated: a → d,e (when b=0, c=0)
theorem a_to_de : ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+k, e+2*k⟩ := by
  have many_step : ∀ k a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+k, e+2*k⟩ := by
    intro k; induction' k with k h <;> intro a d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k a d e

-- R1 one step (manual, to handle cases where step fm can't resolve)
theorem r1_step : fm ⟨a+1, b+1, c, d, e⟩ = some ⟨a, b, c+1, d+1, e⟩ := by simp [fm]

-- R2 one step when a=0 (manual)
theorem r2_step_a0 : fm ⟨0, b, c+1, d, e+1⟩ = some ⟨2, b, c, d, e⟩ := by simp [fm]

-- Combined drain by strong induction on measure = 2*B + c
-- From (a+1, B, c, d, f+c+B) reach (a+1+B+2*c, 0, 0, d+B, f)
-- After R1: a decreases, B decreases, c increases. If a hits 0, R2 fires (c≥1).
-- After R2: a increases by 2, c decreases. a+1 ≥ 1 restored.
-- Using natural addition patterns to avoid subtraction.
theorem gen_drain_r1 :
    ∀ n, ∀ a B c d f, 2*B+c = n →
    ⟨a+1, B, c, d, f+c+B⟩ [fm]⊢* ⟨a+1+B+2*c, 0, 0, d+B, f⟩ := by
  intro n; induction' n using Nat.strongRecOn with n ih; intro a B c d f hn
  rcases B with _ | B
  · -- B = 0: only R2 steps remain (c times, with b=0, a+1≥1 but we need a=0 for R2)
    -- Actually when B=0: state is (a+1, 0, c, d, f+c).
    -- If c=0: done.
    -- If c≥1: a+1≥1, b=0: R1 needs b≥1, fails. R2: c≥1, f+c≥1 (when c≥1). R2 fires.
    -- (a+1, 0, c+1, d, f+c+1) → R2 → (a+3, 0, c, d, f+c) etc.
    -- This is just r2_chain with b=0!
    -- But we already have a+1 ≥ 1, b=0. Use r2_chain_b0 approach.
    simp only [Nat.add_zero] at hn ⊢
    subst hn
    have h : ∀ c a f, ⟨a+1, 0, c, d, f+c⟩ [fm]⊢* ⟨a+1+2*c, 0, 0, d, f⟩ := by
      intro c; induction' c with c hc <;> intro a f
      · exists 0
      rw [show f + (c + 1) = (f + c) + 1 from by ring]
      apply stepStar_trans (c₂ := ⟨a+3, 0, c, d, f+c⟩)
      · rw [show a + 1 = a + 1 from rfl,
            show (c : ℕ) + 1 = c + 1 from rfl]
        -- state: (a+1, 0, c+1, d, (f+c)+1). R2 fires.
        have : fm ⟨a+1, 0, c+1, d, (f+c)+1⟩ = some ⟨(a+1)+2, 0, c, d, f+c⟩ := by simp [fm]
        rw [show (a + 1) + 2 = a + 3 from by ring] at this
        exact step_stepStar this
      apply stepStar_trans (hc _ _)
      ring_nf; finish
    exact h c a f
  · -- B+1 ≥ 1: R1 fires (a+1≥1, B+1≥1)
    -- (a+1, B+1, c, d, f+c+B+1) → R1 → (a, B, c+1, d+1, f+c+B+1)
    -- = (a, B, c+1, d+1, f+(c+1)+B)
    -- New measure: 2*B + (c+1) = 2*(B+1) + c - 1 = n-1
    -- But a could be 0! Need a+1 form. So split:
    rcases a with _ | a
    · -- a=0: (1, B+1, c, d, f+c+B+1)
      -- R1: (0, B, c+1, d+1, f+c+B+1) = (0, B, c+1, d+1, f+(c+1)+B)
      -- Now a=0. If B≥1: need R2 (since a=0, R1 fails). R2: c+1≥1, f+(c+1)+B≥1. ✓
      -- (0, B, (c+1), d+1, f+(c+1)+B) → R2 → (2, B, c, d+1, f+c+B)
      -- = (1+1, B, c, d+1, f+c+B)
      -- Measure: 2*B + c < 2*(B+1) + c = n
      rw [show f + c + (B + 1) = f + c + B + 1 from by ring]
      apply stepStar_trans (c₂ := ⟨0, B, c+1, d+1, f+c+B+1⟩)
      · have : fm ⟨0+1, B+1, c, d, f+c+B+1⟩ = some ⟨0, B, c+1, d+1, f+c+B+1⟩ := by simp [fm]
        exact step_stepStar this
      -- R2 step
      apply stepStar_trans (c₂ := ⟨2, B, c, d+1, f+c+B⟩)
      · rw [show f + c + B + 1 = (f + c + B) + 1 from by ring,
            show (c : ℕ) + 1 = c + 1 from rfl]
        have : fm ⟨0, B, c+1, d+1, (f+c+B)+1⟩ = some ⟨0+2, B, c, d+1, f+c+B⟩ := by simp [fm]
        exact step_stepStar this
      -- Apply IH: (1+1, B, c, d+1, f+c+B)
      have h := ih (2*B+c) (by omega) 1 B c (d+1) f (by ring)
      rw [show (1 : ℕ) + 1 = 2 from by ring] at h
      refine stepStar_trans h ?_
      ring_nf; finish
    · -- a+1 ≥ 1: (a+2, B+1, c, d, f+c+B+1)
      -- R1: (a+1, B, c+1, d+1, f+c+B+1) = ((a+1), B, c+1, d+1, f+(c+1)+B)
      -- Measure: 2*B+(c+1) = 2*(B+1)+c-1 = n-1
      rw [show (a + 1) + 1 = a + 2 from by ring,
          show f + c + (B + 1) = f + c + B + 1 from by ring]
      apply stepStar_trans (c₂ := ⟨a+1, B, c+1, d+1, f+c+B+1⟩)
      · rw [show a + 2 = (a+1) + 1 from by ring,
            show (B : ℕ) + 1 = B + 1 from rfl]
        have : fm ⟨(a+1)+1, B+1, c, d, f+c+B+1⟩ = some ⟨a+1, B, c+1, d+1, f+c+B+1⟩ := by simp [fm]
        exact step_stepStar this
      -- Apply IH
      rw [show f + c + B + 1 = f + (c + 1) + B from by ring]
      have h := ih (2*B+(c+1)) (by omega) a B (c+1) (d+1) f (by ring)
      refine stepStar_trans h ?_
      ring_nf; finish

-- Main transition: (0,0,0,d+1,e+d+2) ⊢⁺ (0,0,0,2*d+2,2*d+e+5)
theorem main_trans : ⟨0, 0, 0, d+1, e+d+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*d+2, 2*d+e+5⟩ := by
  -- Phase 1: d_to_b: (0,0,0,d+1,e+d+2) →* (0,d+1,0,0,e+d+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, d+1, 0, 0, e+d+2⟩)
  · have h := @d_to_b 0 0 (d+1) (e+d+2)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2a: R5: (0, d+1, 0, 0, e+d+2) → (0, d, 1, 0, e+d+2)
  apply step_stepStar_stepPlus (c₂ := ⟨0, d, 1, 0, e+d+2⟩)
  · show fm ⟨0, d+1, 0, 0, e+d+2⟩ = some ⟨0, d, 1, 0, e+d+2⟩; simp [fm]
  -- Phase 2b: R2: (0, d, 1, 0, e+d+2) → (2, d, 0, 0, e+d+1)
  apply stepStar_trans (c₂ := ⟨2, d, 0, 0, e+d+1⟩)
  · rw [show e + d + 2 = (e + d + 1) + 1 from by ring]
    have : fm ⟨0, d, 0+1, 0, (e+d+1)+1⟩ = some ⟨0+2, d, 0, 0, e+d+1⟩ := by simp [fm]
    exact step_stepStar this
  -- Phase 2c: gen_drain: (2, d, 0, 0, e+d+1) = (1+1, d, 0, 0, 0+0+d+...) →* (d+2, 0, 0, d, e+1)
  apply stepStar_trans (c₂ := ⟨d+2, 0, 0, d, e+1⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring,
        show e + d + 1 = (e + 1) + 0 + d from by ring]
    have h := gen_drain_r1 (2*d+0) 1 d 0 0 (e+1) (by ring)
    rw [show 1 + 1 + d + 2 * 0 = d + 2 from by ring,
        show (0 : ℕ) + d = d from by ring] at h
    exact h
  -- Phase 3: a_to_de: (d+2, 0, 0, d, e+1) →* (0, 0, 0, 2*d+2, 2*d+e+5)
  have h := @a_to_de 0 (d+2) d (e+1)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d+1, e+d+2⟩) ⟨0, 0⟩
  intro ⟨d, e⟩
  refine ⟨⟨2*d+1, e+2⟩, ?_⟩
  show ⟨0, 0, 0, d+1, e+d+2⟩ [fm]⊢⁺ ⟨0, 0, 0, (2*d+1)+1, (e+2)+(2*d+1)+2⟩
  have h := @main_trans d e
  rw [show (2*d+1)+1 = 2*d+2 from by ring,
      show (e+2)+(2*d+1)+2 = 2*d+e+5 from by ring]
  exact h
