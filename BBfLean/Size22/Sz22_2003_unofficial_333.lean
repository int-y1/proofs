import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #333: [18/35, 65/33, 7/3, 11/13, 99/2]

Vector representation:
```
 1  2 -1 -1  0  0
 0 -1  1  0 -1  1
 0 -1  0  1  0  0
 0  0  0  0  1 -1
-1  2  0  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_333

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | _ => none

theorem r4_loop : ∀ k a d e, ⟨a, 0, 0, d, e, k⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e; step fm
    apply stepStar_trans (ih a d (e + 1))
    ring_nf; finish

theorem r2r1_loop : ∀ k a b d f,
    ⟨a, b + 2, 0, d + k, k, f⟩ [fm]⊢* ⟨a + k, b + k + 2, 0, d, 0, f + k⟩ := by
  intro k; induction k with
  | zero => intro a b d f; exists 0
  | succ k ih =>
    intro a b d f
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 1) d (f + 1))
    ring_nf; finish

theorem r3_loop : ∀ k a d f, ⟨a, k, 0, d, 0, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0, f⟩ := by
  intro k; induction k with
  | zero => intro a d f; exists 0
  | succ k ih =>
    intro a d f; step fm
    apply stepStar_trans (ih a (d + 1) f)
    ring_nf; finish

theorem main_trans (a d n : ℕ) (hd : d ≥ n + 1) :
    ⟨a + 1, 0, 0, d, 0, n⟩ [fm]⊢⁺ ⟨a + n + 1, 0, 0, d + 2, 0, n + 1⟩ := by
  -- Write d = d' + (n+1) where d' = d - (n+1)
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + (n + 1) := ⟨d - (n + 1), by omega⟩
  -- Phase 1: r4 n times: -> (a+1, 0, 0, d'+n+1, n, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := r4_loop n (a + 1) (d' + (n + 1)) 0; simp at h; exact h
  -- Phase 2: r5 once: -> (a, 2, 0, d'+n+1, n+1, 0)
  · apply step_stepStar_stepPlus
    · show fm ⟨a + 1, 0, 0, d' + (n + 1), n, 0⟩ = some ⟨a, 2, 0, d' + (n + 1), n + 1, 0⟩
      simp [fm]
    -- Phase 3: r2/r1 loop (n+1) times
    · apply stepStar_trans (r2r1_loop (n + 1) a 0 d' 0)
      -- State: (a+(n+1), (n+1)+2, 0, d', 0, n+1)
      -- Phase 4: r3 loop (n+3) times
      apply stepStar_trans (r3_loop (0 + (n + 1) + 2) (a + (n + 1)) d' (0 + (n + 1)))
      ring_nf; finish

theorem init_phase : ⟨1, 0, 0, 0, 0, 0⟩ [fm]⊢* (⟨1, 0, 0, 2, 0, 1⟩ : Q) := by
  execute fm 6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨1, 0, 0, 2, 0, 1⟩ : Q))
  · exact init_phase
  · apply progress_nonhalt (fun c : Q ↦ ∃ a d n, c = (⟨a + 1, 0, 0, d, 0, n⟩ : Q) ∧ d ≥ n + 1)
    · intro c ⟨a, d, n, hc, hd⟩
      subst hc
      exact ⟨⟨a + n + 1, 0, 0, d + 2, 0, n + 1⟩,
        ⟨a + n, d + 2, n + 1, rfl, by omega⟩, main_trans a d n hd⟩
    · exact ⟨0, 2, 1, rfl, by omega⟩

end Sz22_2003_unofficial_333
