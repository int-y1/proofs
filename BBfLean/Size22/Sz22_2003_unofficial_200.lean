import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #200: [1/6, 3/385, 125/3, 28/5, 33/2]

Vector representation:
```
-1 -1  0  0  0
 0  1 -1 -1 -1
 0 -1  3  0  0
 2  0 -1  1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_200

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: convert c to a and d
theorem r4_repeat : ∀ k a c d, ⟨a, 0, c + k, d, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c (d + 1))
    ring_nf; finish

-- R5/R1 chain: drain a (odd) to b=1 and e
theorem r5r1_chain : ∀ k d e, ⟨2 * k + 1, 0, 0, d, e⟩ [fm]⊢* ⟨0, 1, 0, d, e + k + 1⟩ := by
  intro k; induction k with
  | zero => intro d e; step fm; ring_nf; finish
  | succ k ih =>
    intro d e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- R2 repeated: drain c, d, e simultaneously, incrementing b
theorem r2_repeat : ∀ m b c d e, ⟨0, b, c + m, d + m, e + m⟩ [fm]⊢* ⟨0, b + m, c, d, e⟩ := by
  intro m; induction m with
  | zero => intro b c d e; simp; exists 0
  | succ m ih =>
    intro b c d e
    rw [show c + (m + 1) = (c + m) + 1 from by ring,
        show d + (m + 1) = (d + m) + 1 from by ring,
        show e + (m + 1) = (e + m) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c d e)
    ring_nf; finish

-- R3 repeated: drain b, adding 3 to c each time (when a=0, d=0)
theorem r3_repeat : ∀ k b c e, ⟨0, b + k, c, 0, e⟩ [fm]⊢* ⟨0, b, c + 3 * k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro b c e; simp; exists 0
  | succ k ih =>
    intro b c e
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 3) e)
    ring_nf; finish

-- Phase 5 round: 4 steps reducing d by 3
theorem phase5_round : ∀ d b, ⟨0, b, 3, d + 4, d + 5⟩ [fm]⊢* ⟨0, b + 2, 3, d + 1, d + 2⟩ := by
  intro d b
  rw [show (3 : ℕ) = 0 + 3 from by ring,
      show d + 4 = (d + 1) + 3 from by ring,
      show d + 5 = (d + 2) + 3 from by ring]
  apply stepStar_trans (r2_repeat 3 b 0 (d + 1) (d + 2))
  rw [show b + 3 = (b + 2) + 1 from by ring]
  step fm; finish

-- Phase 5: from (0, b, 3, d+1, d+2) to (0, 0, 3b+2d+5, 0, 1)
theorem phase5 : ∀ d, ∀ b, ⟨0, b, 3, d + 1, d + 2⟩ [fm]⊢* ⟨0, 0, 3 * b + 2 * d + 5, 0, 1⟩ := by
  intro d; induction' d using Nat.strongRecOn with d ih; intro b
  rcases d with _ | _ | _ | d
  · -- d = 0: (0, b, 3, 1, 2) → R2 → (0, b+1, 2, 0, 1) → R3×(b+1) → (0, 0, 3b+5, 0, 1)
    rw [show (3 : ℕ) = 2 + 1 from by ring,
        show (0 + 1 : ℕ) = 0 + 1 from by ring,
        show (0 + 2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (r2_repeat 1 b 2 0 1)
    rw [show b + 1 = 0 + (b + 1) from by ring]
    apply stepStar_trans (r3_repeat (b + 1) 0 2 1)
    ring_nf; finish
  · -- d = 1: (0, b, 3, 2, 3) → R2×2 → (0, b+2, 1, 0, 1) → R3×(b+2) → (0, 0, 3b+7, 0, 1)
    rw [show (3 : ℕ) = 1 + 2 from by ring,
        show (0 + 1 + 1 : ℕ) = 0 + 2 from by ring,
        show (0 + 1 + 2 : ℕ) = 1 + 2 from by ring]
    apply stepStar_trans (r2_repeat 2 b 1 0 1)
    rw [show b + 2 = 0 + (b + 2) from by ring]
    apply stepStar_trans (r3_repeat (b + 2) 0 1 1)
    ring_nf; finish
  · -- d = 2: (0, b, 3, 3, 4) → R2×3 → (0, b+3, 0, 0, 1) → R3×(b+3) → (0, 0, 3b+9, 0, 1)
    rw [show (3 : ℕ) = 0 + 3 from by ring,
        show (0 + 1 + 1 + 1 : ℕ) = 0 + 3 from by ring,
        show (0 + 1 + 1 + 2 : ℕ) = 1 + 3 from by ring]
    apply stepStar_trans (r2_repeat 3 b 0 0 1)
    rw [show b + 3 = 0 + (b + 3) from by ring]
    apply stepStar_trans (r3_repeat (b + 3) 0 0 1)
    ring_nf; finish
  · -- d + 3: round then IH
    show ⟨0, b, 3, d + 3 + 1, d + 3 + 2⟩ [fm]⊢* ⟨0, 0, 3 * b + 2 * (d + 3) + 5, 0, 1⟩
    rw [show d + 3 + 1 = d + 4 from by ring,
        show d + 3 + 2 = d + 5 from by ring]
    apply stepStar_trans (phase5_round d b)
    apply stepStar_trans (ih d (by omega) (b + 2))
    ring_nf; finish

-- Phase 1: first 3 steps from (0, 0, 2k+3, 0, 1)
theorem phase1 (k : ℕ) : ⟨0, 0, 2 * k + 3, 0, 1⟩ [fm]⊢* ⟨1, 0, 2 * k + 1, 0, 0⟩ := by
  rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring]
  step fm
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  finish

-- Combined phases 2+3: (1, 0, 2k+1, 0, 0) →* (0, 1, 0, 2k+1, 2k+2)
theorem phases23 (k : ℕ) :
    ⟨1, 0, 2 * k + 1, 0, 0⟩ [fm]⊢* ⟨0, 1, 0, 2 * k + 1, 2 * k + 2⟩ := by
  -- Phase 2: R4×(2k+1): → (4k+3, 0, 0, 2k+1, 0)
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_trans (r4_repeat (2 * k + 1) 1 0 0)
  simp only [Nat.zero_add]
  -- Phase 3: R5/R1: (4k+3, 0, 0, 2k+1, 0) → (0, 1, 0, 2k+1, 2k+2)
  rw [show 1 + 2 * (2 * k + 1) = 2 * (2 * k + 1) + 1 from by ring]
  apply stepStar_trans (r5r1_chain (2 * k + 1) (2 * k + 1) 0)
  ring_nf; finish

-- Main transition: (0, 0, 2k+3, 0, 1) →⁺ (0, 0, 4k+5, 0, 1)
theorem main_trans (k : ℕ) :
    ⟨0, 0, 2 * k + 3, 0, 1⟩ [fm]⊢⁺ ⟨0, 0, 4 * k + 5, 0, 1⟩ := by
  -- Phase 1: → (1, 0, 2k+1, 0, 0)
  apply stepStar_stepPlus_stepPlus (phase1 k)
  -- Phases 2+3: → (0, 1, 0, 2k+1, 2k+2)
  apply stepStar_stepPlus_stepPlus (phases23 k)
  -- Phase 4: R3: (0, 1, 0, 2k+1, 2k+2) → (0, 0, 3, 2k+1, 2k+2)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0 + 1, 0, 2 * k + 1, 2 * k + 2⟩ = some ⟨0, 0, 3, 2 * k + 1, 2 * k + 2⟩
    unfold fm; simp
  -- Phase 5: (0, 0, 3, (2k)+1, (2k)+2) →* (0, 0, 4k+5, 0, 1)
  apply stepStar_trans (phase5 (2 * k) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 0, 1⟩) (by unfold c₀; execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 * n + 3, 0, 1⟩) 1
  intro n
  refine ⟨2 * n + 1, ?_⟩
  show ⟨0, 0, 2 * n + 3, 0, 1⟩ [fm]⊢⁺ ⟨0, 0, 2 * (2 * n + 1) + 3, 0, 1⟩
  rw [show 2 * (2 * n + 1) + 3 = 4 * n + 5 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_200
