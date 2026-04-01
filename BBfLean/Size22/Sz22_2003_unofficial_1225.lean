import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1225: [5/6, 539/2, 8/165, 3/7, 5/3]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 3 -1 -1  0 -1
 0  1  0 -1  0
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1225

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b+1, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move d to b
theorem d_to_b : ∀ k b d e, ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [Nat.add_succ d k]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R2 repeated: drain a
theorem r2_drain : ∀ k c d e, ⟨k, (0 : ℕ), c, d, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show k + 1 = (k) + 1 from rfl]
    step fm
    apply stepStar_trans (ih c (d + 2) (e + 1))
    ring_nf; finish

-- Chain: R3 + R1×3 repeated k times
theorem chain : ∀ k, ∀ b c e, ⟨(0 : ℕ), b + 4 * k, c + 1, 0, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 2 * k + 1, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · simp; exists 0
  · rw [show b + 4 * (k + 1) = (b + 4) + 4 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 4) c (e + 1))
    rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show c + 2 * k + 3 = c + 2 * (k + 1) + 1 from by ring]
    finish

-- Cycle: R4 + R3 + R2×3 repeated k times
theorem cycle : ∀ k, ∀ c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, e + 1⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + 5 * k + 1, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) d e)
    rw [show d + 5 * k + 1 = (d + 5 * k) + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm
    rw [show d + 5 * k + 6 = d + 5 * (k + 1) + 1 from by ring,
        show e + 2 * k + 3 = e + 2 * (k + 1) + 1 from by ring]
    finish

-- Odd transition: (0,0,0,4m+2,2m+1) ->+ (0,0,0,10m+6,5m+3)
theorem trans_odd (m : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, 4 * m + 2, 2 * m + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 10 * m + 6, 5 * m + 3⟩ := by
  -- Phase 1: d_to_b
  rw [show 4 * m + 2 = 0 + (4 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (4 * m + 2) 0 0 (2 * m + 1))
  rw [show (0 : ℕ) + (4 * m + 2) = 4 * m + 2 from by ring]
  -- Phase 2: R5
  rw [show 4 * m + 2 = (4 * m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, (4 * m + 1) + 1, 0, 0, 2 * m + 1⟩ : Q) [fm]⊢ ⟨0, 4 * m + 1, 1, 0, 2 * m + 1⟩)
  -- Phase 3: chain with k=m
  rw [show 4 * m + 1 = 1 + 4 * m from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * m + 1 = (m + 1) + m from by ring]
  apply stepStar_trans (chain m 1 0 (m + 1))
  rw [show 0 + 2 * m + 1 = 2 * m + 1 from by ring]
  -- State: (0, 1, 2m+1, 0, m+1)
  -- Phase 4: R3
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * m + 1 = (2 * m) + 1 from by ring,
      show m + 1 = (m) + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, 0 + 1, (2 * m) + 1, 0, m + 1⟩ : Q) [fm]⊢ ⟨3, 0, 2 * m, 0, m⟩))
  -- R2×3
  apply stepStar_trans (r2_drain 3 (2 * m) 0 m)
  rw [show 0 + 2 * 3 = 5 + 1 from by ring,
      show m + 3 = (m + 2) + 1 from by ring]
  -- State: (0, 0, 2m, 5+1, (m+2)+1)
  -- Phase 5: cycle with k=2m
  rw [show 2 * m = 0 + 2 * m from by ring]
  apply stepStar_trans (cycle (2 * m) 0 5 (m + 2))
  rw [show 5 + 5 * (2 * m) + 1 = 10 * m + 6 from by ring,
      show m + 2 + 2 * (2 * m) + 1 = 5 * m + 3 from by ring]
  finish

-- Even transition: (0,0,0,4(m+1),2(m+1)) ->+ (0,0,0,10(m+1)+2,5(m+1)+1)
theorem trans_even (m : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, 4 * (m + 1), 2 * (m + 1)⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 10 * (m + 1) + 2, 5 * (m + 1) + 1⟩ := by
  -- Phase 1: d_to_b
  rw [show 4 * (m + 1) = 0 + (4 * m + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (4 * m + 4) 0 0 (2 * (m + 1)))
  rw [show (0 : ℕ) + (4 * m + 4) = 4 * m + 4 from by ring]
  -- Phase 2: R5
  rw [show 4 * m + 4 = (4 * m + 3) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, (4 * m + 3) + 1, 0, 0, 2 * (m + 1)⟩ : Q) [fm]⊢ ⟨0, 4 * m + 3, 1, 0, 2 * (m + 1)⟩)
  -- Phase 3: chain with k=m
  rw [show 4 * m + 3 = 3 + 4 * m from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * (m + 1) = (m + 2) + m from by ring]
  apply stepStar_trans (chain m 3 0 (m + 2))
  rw [show 0 + 2 * m + 1 = 2 * m + 1 from by ring]
  -- State: (0, 3, 2m+1, 0, m+2)
  -- Phase 4: R3 + R1×2 + R2
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 2 * m + 1 = (2 * m) + 1 from by ring,
      show m + 2 = (m + 1) + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, 2 + 1, (2 * m) + 1, 0, (m + 1) + 1⟩ : Q) [fm]⊢ ⟨3, 2, 2 * m, 0, m + 1⟩))
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨3, 2, 2 * m, 0, m + 1⟩ : Q) [fm]⊢ ⟨2, 1, 2 * m + 1, 0, m + 1⟩))
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨2, 1, 2 * m + 1, 0, m + 1⟩ : Q) [fm]⊢ ⟨1, 0, 2 * m + 2, 0, m + 1⟩))
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, 0, 2 * m + 2, 0, m + 1⟩ : Q) [fm]⊢ ⟨0, 0, 2 * m + 2, 2, m + 2⟩))
  -- State: (0, 0, 2m+2, 2, m+2)
  -- Phase 5: cycle with k=2m+2
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show m + 2 = (m + 1) + 1 from by ring]
  apply stepStar_trans (cycle (2 * m + 2) 0 1 (m + 1))
  rw [show 1 + 5 * (2 * m + 2) + 1 = 10 * (m + 1) + 2 from by ring,
      show m + 1 + 2 * (2 * m + 2) + 1 = 5 * (m + 1) + 1 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ e, q = ⟨0, 0, 0, 2 * e, e⟩ ∧ e ≥ 1)
  · intro q ⟨e, hq, he⟩; subst hq
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- even: e = k + k
      rw [show k + k = 2 * k from by ring] at hk; subst hk
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      refine ⟨_, ⟨5 * (m + 1) + 1, rfl, by omega⟩, ?_⟩
      rw [show 2 * (2 * (m + 1)) = 4 * (m + 1) from by ring,
          show 2 * (5 * (m + 1) + 1) = 10 * (m + 1) + 2 from by ring]
      exact trans_even m
    · -- odd: e = 2*k+1
      subst hk
      refine ⟨_, ⟨5 * k + 3, rfl, by omega⟩, ?_⟩
      rw [show 2 * (2 * k + 1) = 4 * k + 2 from by ring,
          show 2 * (5 * k + 3) = 10 * k + 6 from by ring]
      exact trans_odd k
  · exact ⟨1, rfl, by omega⟩

end Sz22_2003_unofficial_1225
