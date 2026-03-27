import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #368: [2/15, 63/2, 539/3, 5/539, 3/7]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0  1  0
 0 -1  0  2  1
 0  0  1 -2 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_368

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1: Rule 3 drains b, filling d and e
theorem phase1 : ∀ n b d e,
    ⟨0, b + n, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d + 2 * n, e + n⟩ := by
  intro n; induction n with
  | zero => intro b d e; simp; exists 0
  | succ n ih =>
    intro b d e
    rw [show b + (n + 1) = (b + n) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (d + 2) (e + 1))
    rw [show (d + 2) + 2 * n = d + 2 * (n + 1) from by ring,
        show (e + 1) + n = e + (n + 1) from by ring]
    finish

-- Phase 2: Rule 4 drains e, transfers d to c
theorem phase2 : ∀ n c d e,
    ⟨0, 0, c, d + 2 * n, e + n⟩ [fm]⊢* ⟨0, 0, c + n, d, e⟩ := by
  intro n; induction n with
  | zero => intro c d e; simp; exists 0
  | succ n ih =>
    intro c d e
    rw [show d + 2 * (n + 1) = (d + 2 * n) + 2 from by ring,
        show e + (n + 1) = (e + n) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    rw [show (c + 1) + n = c + (n + 1) from by ring]
    finish

-- R2 drain: transfer a to b and d (when c=0, e=0)
theorem r2_drain : ∀ a b d,
    ⟨a, b, 0, d, 0⟩ [fm]⊢* ⟨0, b + 2 * a, 0, d + a, 0⟩ := by
  intro a; induction a with
  | zero => intro b d; simp; exists 0
  | succ a ih =>
    intro b d
    step fm
    apply stepStar_trans (ih (b + 2) (d + 1))
    rw [show (b + 2) + 2 * a = b + 2 * (a + 1) from by ring,
        show (d + 1) + a = d + (a + 1) from by ring]
    finish

-- Inner pair step: consume 2 from c
-- R2: (a+1, 0, c+2, d, 0) -> (a, 2, c+2, d+1, 0)
-- R1: -> (a+1, 1, c+1, d+1, 0)
-- R1: -> (a+2, 0, c, d+1, 0)
theorem inner_pair : ∀ a c d,
    ⟨a + 1, 0, c + 2, d, 0⟩ [fm]⊢* ⟨a + 2, 0, c, d + 1, 0⟩ := by
  intro a c d
  step fm; step fm; step fm
  ring_nf; finish

-- General unwind: (a+1, 0, c, d, 0) ⊢* (0, c + 2*(a+1), 0, d + a + c + 1, 0)
theorem unwind_gen : ∀ c a d,
    ⟨a + 1, 0, c, d, 0⟩ [fm]⊢* ⟨0, c + 2 * (a + 1), 0, d + a + c + 1, 0⟩ := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih => ?_
  intro a d
  match c with
  | 0 =>
    -- r2_drain
    have h := r2_drain (a + 1) 0 d
    rw [show 0 + 2 * (a + 1) = 0 + 2 * (a + 1) from rfl,
        show d + (a + 1) = d + a + 0 + 1 from by ring] at h
    exact h
  | 1 =>
    -- (a+1, 0, 1, d, 0) -> R2 -> (a, 2, 1, d+1, 0) -> R1 -> (a+1, 1, 0, d+1, 0)
    -- -> R2 -> (a, 3, 0, d+2, 0) -> r2_drain -> (0, 3+2*a, 0, d+2+a, 0)
    step fm; step fm; step fm
    apply stepStar_trans (r2_drain a 3 (d + 2))
    rw [show 3 + 2 * a = 1 + 2 * (a + 1) from by ring,
        show (d + 2) + a = d + a + 1 + 1 from by ring]
    ring_nf; finish
  | c + 2 =>
    -- inner_pair then IH
    apply stepStar_trans (inner_pair a c d)
    have h := ih c (by omega) (a + 1) (d + 1)
    apply stepStar_trans h
    rw [show c + 2 * (a + 1 + 1) = c + 2 + 2 * (a + 1) from by ring,
        show (d + 1) + (a + 1) + c + 1 = d + a + (c + 2) + 1 from by ring]
    finish

-- Main transition: one full cycle
theorem main_trans (n d : ℕ) :
    ⟨0, n + 2, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨0, n + 3, 0, d + n + 2, 0⟩ := by
  -- Phase 1: (0, n+2, 0, d+1, 0) ⊢* (0, 0, 0, d+1+2*(n+2), 0+(n+2))
  apply stepStar_stepPlus_stepPlus
  · have h1 := phase1 (n + 2) 0 (d + 1) 0
    simp at h1
    rw [show d + 1 + 2 * (n + 2) = d + 2 * n + 5 from by ring] at h1
    exact h1
  -- Phase 2: (0, 0, 0, d+2*n+5, n+2) ⊢* (0, 0, n+2, d+1, 0)
  apply stepStar_stepPlus_stepPlus
  · have h2 := phase2 (n + 2) 0 (d + 1) 0
    simp at h2
    rw [show (d + 1) + 2 * (n + 2) = d + 2 * n + 5 from by ring] at h2
    exact h2
  -- Phase 3a: R5: (0, 0, n+2, d+1, 0) -> (0, 1, n+2, d, 0)
  -- But wait: with a=0, b=0, c=n+2, d+1, e=0:
  -- R1: needs b>=1. No.
  -- R2: needs a>=1. No.
  -- R3: needs b>=1. No.
  -- R4: needs d>=2 and e>=1. d+1 >= 2 when d >= 1, but e=0. No.
  -- R5: (a, b, c, d+1, e) -> needs d >= 1. d+1 means d >= 0. Yes!
  -- So R5 fires: (0, 0, n+2, d+1, 0) -> (0, 1, n+2, d, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, n + 2, d + 1, 0⟩ = some ⟨0, 1, n + 2, d, 0⟩
    simp [fm]
  -- R1: (0, 1, n+2, d, 0) -> (1, 0, n+1, d, 0) since b=1>=1, c=n+2>=1
  apply stepStar_trans
  · show ⟨0, 1, n + 2, d, 0⟩ [fm]⊢* ⟨1, 0, n + 1, d, 0⟩
    step fm; finish
  -- Phase 3b: unwind_gen
  have h := unwind_gen (n + 1) 0 d
  simp at h
  apply stepStar_trans h
  rw [show (n + 1) + 2 = n + 3 from by ring,
      show d + (n + 1) + 1 = d + n + 2 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0 + 2, 0, 0 + 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm) (fun c ↦ ∃ n d, c = ⟨0, n + 2, 0, d + 1, 0⟩)
  · intro c ⟨n, d, hc⟩
    exact ⟨⟨0, n + 3, 0, d + n + 2, 0⟩, ⟨n + 1, d + n + 1, by ring_nf⟩, hc ▸ main_trans n d⟩
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_368
