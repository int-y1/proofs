import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1206: [5/6, 539/2, 4/35, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  0
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1206

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: move d to b. (0, b, 0, d+k, e) →* (0, b+k, 0, d, e)
theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [Nat.add_succ d k]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- Full round: 5 steps. (0, b+3, c, 0, e+1) →* (0, b, c+2, 0, e)
theorem full_round : ⟨0, b + 3, c, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 2, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Full rounds chain: n rounds. (0, b+3*n, c, 0, e+n) →* (0, b, c+2*n, 0, e)
theorem full_rounds_chain : ∀ n, ⟨0, b + 3 * n, c, 0, e + n⟩ [fm]⊢* ⟨0, b, c + 2 * n, 0, e⟩ := by
  intro n; induction' n with n ih generalizing b c e
  · exists 0
  · rw [show b + 3 * (n + 1) = (b + 3) + 3 * n from by ring,
        show e + (n + 1) = (e + 1) + n from by ring]
    apply stepStar_trans (ih (b := b + 3) (c := c) (e := e + 1))
    apply stepStar_trans (full_round (b := b) (c := c + 2 * n) (e := e))
    ring_nf; finish

-- Partial round from b=2: 5 steps. (0, 2, c, 0, e+1) →* (0, 0, c+1, 2, e+1)
theorem partial_round : ⟨0, 2, c, 0, e + 1⟩ [fm]⊢* ⟨0, 0, c + 1, 2, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Drain: R3,R2,R2 repeated. (0, 0, C, d+1, e) →* (0, 0, 0, d+1+3*C, e+2*C)
theorem drain : ∀ C, ⟨0, 0, C, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + 1 + 3 * C, e + 2 * C⟩ := by
  intro C; induction' C with C ih generalizing d e
  · exists 0
  · step fm; step fm; step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 3) (e := e + 2))
    ring_nf; finish

-- Main transition as stepStar
theorem main_star (he : e ≥ n + 1) :
    ⟨0, 0, 0, 3 * n + 2, e⟩ [fm]⊢* ⟨0, 0, 0, 6 * n + 5, e + 3 * n + 2⟩ := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + (n + 1) := ⟨e - (n + 1), by omega⟩
  -- Phase 1: d_to_b
  rw [show (3 * n + 2 : ℕ) = 0 + (3 * n + 2) from by ring]
  apply stepStar_trans (d_to_b (3 * n + 2) (b := 0) (d := 0) (e := e' + (n + 1)))
  -- Now at (0, 3n+2, 0, 0, e'+n+1)
  -- Phase 2: full rounds
  rw [show 0 + (3 * n + 2) = 2 + 3 * n from by ring,
      show e' + (n + 1) = (e' + 1) + n from by ring]
  apply stepStar_trans (full_rounds_chain n (b := 2) (c := 0) (e := e' + 1))
  -- Now at (0, 2, 2n, 0, e'+1)
  -- Phase 3: partial round
  rw [show (0 + 2 * n : ℕ) = 2 * n from by ring]
  apply stepStar_trans (partial_round (c := 2 * n) (e := e'))
  -- Now at (0, 0, 2n+1, 2, e'+1)
  -- Phase 4: drain
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain (2 * n + 1) (d := 1) (e := e' + 1))
  ring_nf; finish

-- Main transition as stepPlus
theorem main_transition (he : e ≥ n + 1) :
    ⟨0, 0, 0, 3 * n + 2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * n + 5, e + 3 * n + 2⟩ := by
  apply stepStar_stepPlus (main_star he)
  intro h
  have h1 := congr_arg (fun q : Q ↦ q.2.2.2.1) h
  simp at h1; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n e, q = ⟨0, 0, 0, 3 * n + 2, e⟩ ∧ e ≥ n + 1 ∧ e ≥ 1)
  · intro c ⟨n, e, hq, he, he1⟩; subst hq
    exact ⟨⟨0, 0, 0, 6 * n + 5, e + 3 * n + 2⟩,
      ⟨2 * n + 1, e + 3 * n + 2, by ring_nf, by omega, by omega⟩, main_transition he⟩
  · exact ⟨0, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1206
