import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #197: [1/6, 3/35, 125/33, 4/5, 231/2]

Vector representation:
```
-1 -1  0  0  0
 0  1 -1 -1  0
 0 -1  3  0 -1
 2  0 -1  0  0
-1  1  0  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_197

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e+1⟩
  | _ => none

-- R5+R1 chain: drains a (odd) to 0, building d and e.
theorem r5r1_chain : ∀ k d e,
    ⟨2 * k + 1, 0, 0, d, e⟩ [fm]⊢* ⟨0, 1, 0, d + k + 1, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · step fm; ring_nf; finish
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih (d + 1) (e + 1))
  ring_nf; finish

-- R2 partial: applies R2 n times.
theorem r2_partial : ∀ n b c d e,
    ⟨0, b, c + n, d + n, e⟩ [fm]⊢* ⟨0, b + n, c, d, e⟩ := by
  intro n; induction' n with n ih <;> intro b c d e
  · exists 0
  rw [show c + (n + 1) = (c + n) + 1 from by ring,
      show d + (n + 1) = (d + n) + 1 from by ring,
      show b + (n + 1) = (b + n) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R3 repeated: drains e using b, building c.
theorem r3_run : ∀ e b c,
    ⟨0, b + e, c, 0, e⟩ [fm]⊢* ⟨0, b, c + 3 * e, 0, 0⟩ := by
  intro e; induction' e with e ih <;> intro b c
  · simp; exists 0
  rw [show b + (e + 1) = (b + e) + 1 from by ring,
      show c + 3 * (e + 1) = (c + 3) + 3 * e from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R4 repeated: drains c, building a.
theorem c_drain : ∀ c a,
    ⟨a, 0, c, 0, 0⟩ [fm]⊢* ⟨a + 2 * c, 0, 0, 0, 0⟩ := by
  intro c; induction' c with c ih <;> intro a
  · simp; exists 0
  step fm
  apply stepStar_trans (ih (a + 2))
  ring_nf; finish

-- Drain: the key lemma handling the R2/R3 interaction.
theorem drain : ∀ k b,
    ⟨0, b, 3, k + 1, k + b⟩ [fm]⊢* ⟨0, 1, 3 * b + 2 * k + 2, 0, 0⟩ := by
  intro k; induction' k using Nat.strongRecOn with k IH
  rcases k with _ | _ | _ | k
  · -- k = 0
    intro b
    rw [show (0 : ℕ) + 1 = 1 from by ring, show (0 : ℕ) + b = b from by ring,
        show 3 * b + 2 * 0 + 2 = 2 + 3 * b from by ring]
    have h1 := r2_partial 1 b 2 0 b
    rw [show 2 + 1 = 3 from by ring, show (0 : ℕ) + 1 = 1 from by ring] at h1
    apply stepStar_trans h1
    have h2 := r3_run b 1 2
    rw [show 1 + b = b + 1 from by ring] at h2
    exact h2
  · -- k = 1
    intro b
    rw [show (1 : ℕ) + 1 = 2 from by ring, show 1 + b = b + 1 from by ring,
        show 3 * b + 2 * 1 + 2 = 1 + 3 * (b + 1) from by ring]
    have h1 := r2_partial 2 b 1 0 (b + 1)
    rw [show 1 + 2 = 3 from by ring, show (0 : ℕ) + 2 = 2 from by ring] at h1
    apply stepStar_trans h1
    have h2 := r3_run (b + 1) 1 1
    rw [show 1 + (b + 1) = b + 2 from by ring] at h2
    exact h2
  · -- k = 2
    intro b
    rw [show (2 : ℕ) + 1 = 3 from by ring, show 2 + b = b + 2 from by ring,
        show 3 * b + 2 * 2 + 2 = 0 + 3 * (b + 2) from by ring]
    have h1 := r2_partial 3 b 0 0 (b + 2)
    apply stepStar_trans h1
    have h2 := r3_run (b + 2) 1 0
    rw [show 1 + (b + 2) = b + 3 from by ring] at h2
    exact h2
  · -- k + 3: one cycle reduces k by 3
    intro b
    rw [show k + 3 + 1 = k + 4 from by ring,
        show k + 3 + b = k + b + 3 from by ring,
        show 3 * b + 2 * (k + 3) + 2 = 3 * (b + 2) + 2 * k + 2 from by ring]
    -- R2_partial(3): ⟨0, b, 0+3, (k+1)+3, (k+b+3)⟩ →* ⟨0, b+3, 0, k+1, k+b+3⟩
    have h1 := r2_partial 3 b 0 (k + 1) (k + b + 3)
    rw [show 0 + 3 = 3 from by ring, show k + 1 + 3 = k + 4 from by ring] at h1
    apply stepStar_trans h1
    -- R3 step: ⟨0, b+3, 0, k+1, k+b+3⟩ → ⟨0, b+2, 3, k+1, k+b+2⟩
    have hr3 : ⟨0, b + 3, 0, k + 1, k + b + 3⟩ [fm]⊢ ⟨0, b + 2, 3, k + 1, k + b + 2⟩ := by
      show fm ⟨0, b + 3, 0, k + 1, k + b + 3⟩ = some ⟨0, b + 2, 3, k + 1, k + b + 2⟩
      simp [fm]
    apply stepStar_trans (step_stepStar hr3)
    -- IH
    have h2 := IH k (by omega) (b + 2)
    rw [show k + (b + 2) = k + b + 2 from by ring] at h2
    exact h2

-- Full transition: ⟨2k+1, 0, 0, 0, 0⟩ →⁺ ⟨4k+3, 0, 0, 0, 0⟩
theorem main_trans (k : ℕ) :
    ⟨2 * k + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨4 * k + 3, 0, 0, 0, 0⟩ := by
  -- Phase 1: R5/R1 chain
  have h1 := r5r1_chain k 0 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2: R3 step: ⟨0, 1, 0, k+1, k+1⟩ → ⟨0, 0, 3, k+1, k⟩
  apply step_stepStar_stepPlus
  · show fm ⟨0, 1, 0, k + 1, k + 1⟩ = some ⟨0, 0, 3, k + 1, k⟩; simp [fm]
  -- Phase 3: drain
  have h3 := drain k 0
  simp only [Nat.add_zero, show 3 * 0 + 2 * k + 2 = 2 * k + 2 from by ring] at h3
  apply stepStar_trans h3
  -- Phase 4: c_to_a: ⟨0, 1, 2k+2, 0, 0⟩ → R4 → R1 → c_drain
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm; step fm
  have h4 := c_drain (2 * k + 1) 1
  rw [show 1 + 2 * (2 * k + 1) = 4 * k + 3 from by ring] at h4
  exact h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨2 * k + 1, 0, 0, 0, 0⟩) 0
  intro k
  refine ⟨2 * k + 1, ?_⟩
  have h := main_trans k
  rw [show 2 * (2 * k + 1) + 1 = 4 * k + 3 from by ring]
  exact h

end Sz22_2003_unofficial_197
