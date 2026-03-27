import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #248: [135/2, 4/35, 11/45, 7/11, 5/3]

Vector representation:
```
-1  3  1  0  0
 2  0 -1 -1  0
 0 -2 -1  0  1
 0  0  0  1 -1
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_248

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R2/R1 loop: each round applies R2 (c--, d--, a+=2) then R1×2 (a-=2, b+=6, c+=2).
-- Net per round: b += 6, c += 1, d -= 1.
theorem r2r1_loop : ∀ k b c,
    ⟨0, b, c + 1, k + 1, 0⟩ [fm]⊢* ⟨0, b + 6 * (k + 1), c + k + 2, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro b c; step fm; step fm; step fm; finish
  | succ k ih =>
    intro b c
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 6) (c + 1))
    have : b + 6 + 6 * (k + 1) = b + 6 * (k + 2) := by ring
    have : c + 1 + k + 2 = c + (k + 1) + 2 := by ring
    rw [‹b + 6 + 6 * (k + 1) = b + 6 * (k + 2)›, ‹c + 1 + k + 2 = c + (k + 1) + 2›]
    finish

-- R3 loop: drain c into e. Each step: b -= 2, c -= 1, e += 1.
theorem r3_loop : ∀ c b e,
    ⟨0, b + 2 * (c + 1), c + 1, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e + c + 1⟩ := by
  intro c; induction c with
  | zero => intro b e; step fm; finish
  | succ c ih =>
    intro b e
    step fm
    have h1 : b + 2 * (c + 2) = (b + 2) + 2 * (c + 1) := by ring
    rw [h1] at *
    apply stepStar_trans (ih b (e + 1))
    have : e + 1 + c + 1 = e + (c + 1) + 1 := by ring
    rw [this]; finish

-- R4 loop: drain e into d. Each step: d += 1, e -= 1.
theorem r4_loop : ∀ e b d,
    ⟨0, b, 0, d, e + 1⟩ [fm]⊢* ⟨0, b, 0, d + e + 1, 0⟩ := by
  intro e; induction e with
  | zero => intro b d; step fm; finish
  | succ e ih =>
    intro b d
    step fm
    apply stepStar_trans (ih b (d + 1))
    have : d + 1 + e + 1 = d + (e + 1) + 1 := by ring
    rw [this]; finish

-- Main transition: (0, b+1, 0, n+1, 0) ⊢⁺ (0, b+4*n+2, 0, n+2, 0)
theorem main_step (n b : ℕ) :
    ⟨0, b + 1, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨0, b + 4 * n + 2, 0, n + 2, 0⟩ := by
  -- Phase 1: R5
  apply step_stepStar_stepPlus (by rfl : fm ⟨0, b + 1, 0, n + 1, 0⟩ = some ⟨0, b, 1, n + 1, 0⟩)
  -- Phase 2: R2/R1 loop (n+1 rounds)
  -- r2r1_loop n b 0: (0, b, 0+1, n+1, 0) ->* (0, b+6*(n+1), 0+n+2, 0, 0)
  apply stepStar_trans (r2r1_loop n b 0)
  -- Now at (0, b + 6*(n+1), n+2, 0, 0)
  -- Phase 3: R3 loop (n+2 steps)
  have hr3 : b + 6 * (n + 1) = (b + 4 * n + 2) + 2 * ((n + 1) + 1) := by ring
  have hc : 0 + n + 2 = (n + 1) + 1 := by ring
  rw [hr3, hc]
  apply stepStar_trans (r3_loop (n + 1) (b + 4 * n + 2) 0)
  -- Now at (0, b+4*n+2, 0, 0, 0+(n+1)+1)
  -- Phase 4: R4 loop
  have he : 0 + (n + 1) + 1 = (n + 1) + 1 := by ring
  rw [he]
  apply stepStar_trans (r4_loop (n + 1) (b + 4 * n + 2) 0)
  have : 0 + (n + 1) + 1 = n + 2 := by ring
  rw [this]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0 + 1, 0, 0 + 1, 0⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, p.1 + 1, 0, p.2 + 1, 0⟩) (0, 0)
  intro ⟨b, n⟩
  refine ⟨(b + 4 * n + 1, n + 1), ?_⟩
  show ⟨0, b + 1, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨0, b + 4 * n + 1 + 1, 0, n + 1 + 1, 0⟩
  have h1 : b + 4 * n + 1 + 1 = b + 4 * n + 2 := by ring
  have h2 : n + 1 + 1 = n + 2 := by ring
  rw [h1, h2]
  exact main_step n b

end Sz22_2003_unofficial_248
