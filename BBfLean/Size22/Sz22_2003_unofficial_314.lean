import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #314: [154/15, 1/338, 21/2, 65/7, 2/143]

Vector representation:
```
 1 -1 -1  1  1  0
-1  0  0  0  0 -2
-1  1  0  1  0  0
 0  0  1 -1  0  1
 1  0  0  0 -1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_314

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d+1, e+1, f⟩
  | ⟨a+1, b, c, d, e, f+2⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- R4 chain: (0,0,c,d,e,f) →* (0,0,c+d,0,e,f+d)
theorem r4_chain : ∀ d c e f,
    ⟨0, 0, c, d, e, f⟩ [fm]⊢* ⟨0, 0, c + d, 0, e, f + d⟩ := by
  intro d; induction d with
  | zero => intro c e f; exists 0
  | succ d ih =>
    intro c e f
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R5+R2 chain: (0,0,c,0,e+k+1,3*k+2) →* (0,0,c,0,e+1,2)
theorem r52_chain : ∀ k c e,
    ⟨0, 0, c, 0, e + k + 1, 3 * k + 2⟩ [fm]⊢*
    ⟨0, 0, c, 0, e + 1, 2⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e
    rw [show 3 * (k + 1) + 2 = (3 * k + 2) + 2 + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _)
    finish

-- R1+R3 chain: (0,1,c,d,e,1) →* (0,1,0,d+2*c,e+c,1)
theorem r13_chain : ∀ c d e,
    ⟨0, 1, c, d, e, 1⟩ [fm]⊢* ⟨0, 1, 0, d + 2 * c, e + c, 1⟩ := by
  intro c; induction c with
  | zero => intro d e; exists 0
  | succ c ih =>
    intro d e
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Combined: R5 + R3 + R1/R3 chain + R4 + R1 + R2
-- (0,0,c,0,e+1,2) →* (0,0,0,2*c+1,e+c+1,0)
theorem tail_phase : ∀ c e,
    ⟨0, 0, c, 0, e + 1, 2⟩ [fm]⊢* ⟨0, 0, 0, 2 * c + 1, e + c + 1, 0⟩ := by
  intro c e
  -- R5: (0,0,c,0,e+1,2) → (1,0,c,0,e,1)
  -- R3: (1,0,c,0,e,1) → (0,1,c,1,e,1)
  step fm; step fm
  -- R1+R3 chain: (0,1,c,1,e,1) → (0,1,0,1+2*c,e+c,1)
  apply stepStar_trans (r13_chain c 1 e)
  -- R4: need 1+2*c = (2*c) + 1, so d+1 pattern matches
  rw [show 1 + 2 * c = 2 * c + 1 from by ring]
  -- R4: (0,1,0,2*c+1,e+c,1) → (0,1,1,2*c,e+c,2)
  step fm
  -- R1: (0,1,1,2*c,e+c,2) → (1,0,0,2*c+1,e+c+1,2)
  step fm
  -- R2: (1,0,0,2*c+1,e+c+1,2) → (0,0,0,2*c+1,e+c+1,0)
  step fm
  finish

-- Main transition
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 2 + 3 * (2^n - 1), 2^n + 1 + (2^n - 1), 0⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 + 3 * (2^(n+1) - 1), 2^(n+1) + 1 + (2^(n+1) - 1), 0⟩ := by
  -- Phase 1: R4 chain: D steps
  have phase1 : ⟨0, 0, 0, 2 + 3 * (2^n - 1), 2^n + 1 + (2^n - 1), 0⟩ [fm]⊢*
      ⟨0, 0, 2 + 3 * (2^n - 1), 0, 2^n + 1 + (2^n - 1), 2 + 3 * (2^n - 1)⟩ := by
    have := r4_chain (2 + 3 * (2^n - 1)) 0 (2^n + 1 + (2^n - 1)) 0
    simp only [Nat.zero_add] at this
    exact this
  -- Phase 2: R5+R2 chain
  have phase2 : ⟨0, 0, 2 + 3 * (2^n - 1), 0, 2^n + 1 + (2^n - 1), 2 + 3 * (2^n - 1)⟩ [fm]⊢*
      ⟨0, 0, 2 + 3 * (2^n - 1), 0, 2^n + 1, 2⟩ := by
    rw [show 2^n + 1 + (2^n - 1) = 2^n + (2^n - 1) + 1 from by ring,
        show 2 + 3 * (2 ^ n - 1) = 3 * (2 ^ n - 1) + 2 from by ring]
    exact r52_chain (2^n - 1) (3 * (2^n - 1) + 2) (2^n)
  -- Phase 3: tail_phase
  have phase3 : ⟨0, 0, 2 + 3 * (2^n - 1), 0, 2^n + 1, 2⟩ [fm]⊢*
      ⟨0, 0, 0, 2 * (2 + 3 * (2^n - 1)) + 1, 2^n + (2 + 3 * (2^n - 1)) + 1, 0⟩ := by
    exact tail_phase (2 + 3 * (2^n - 1)) (2^n)
  -- Arithmetic rewrites
  have hpow : 1 ≤ 2^n := Nat.one_le_two_pow
  have h1 : 2 * (2 + 3 * (2^n - 1)) + 1 = 2 + 3 * (2^(n+1) - 1) := by
    simp [Nat.pow_succ]; omega
  have h2 : 2^n + (2 + 3 * (2^n - 1)) + 1 = 2^(n+1) + 1 + (2^(n+1) - 1) := by
    simp [Nat.pow_succ]; omega
  -- Combine all phases
  have combined : ⟨0, 0, 0, 2 + 3 * (2^n - 1), 2^n + 1 + (2^n - 1), 0⟩ [fm]⊢*
      ⟨0, 0, 0, 2 + 3 * (2^(n+1) - 1), 2^(n+1) + 1 + (2^(n+1) - 1), 0⟩ := by
    rw [← h1, ← h2]
    exact stepStar_trans phase1 (stepStar_trans phase2 phase3)
  exact stepStar_stepPlus combined (by intro h; have := congr_arg (fun q : Q ↦ q.2.2.2.1) h; simp at this; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2, 0⟩)
  · execute fm 7
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 0, 0, 2 + 3 * (2^n - 1), 2^n + 1 + (2^n - 1), 0⟩)
  · intro c ⟨n, hq⟩; subst hq
    exact ⟨_, ⟨n + 1, rfl⟩, main_trans n⟩
  · exact ⟨0, by simp⟩
