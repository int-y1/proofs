import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #214: [1/6, 99/35, 5/3, 2/55, 1617/2]

Vector representation:
```
-1 -1  0  0  0
 0  2 -1 -1  1
 0 -1  1  0  0
 1  0 -1  0 -1
-1  1  0  2  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_214

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e+1⟩
  | _ => none

theorem r4_repeat : ∀ k a c e, ⟨a, 0, c + k, 0, e + k⟩ [fm]⊢* ⟨a + k, 0, c, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c e; simp; exists 0
  | succ k ih =>
    intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c e)
    ring_nf; finish

theorem r5r1_chain : ∀ k d e, ⟨2 * k + 1, 0, 0, d, e⟩ [fm]⊢* ⟨0, 1, 0, d + 2 * k + 2, e + k + 1⟩ := by
  intro k; induction k with
  | zero =>
    intro d e
    step fm
    ring_nf; finish
  | succ k ih =>
    intro d e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

theorem r2r3_loop : ∀ k b e, ⟨0, b, 1, k + 1, e⟩ [fm]⊢* ⟨0, b + k + 2, 0, 0, e + k + 1⟩ := by
  intro k; induction k with
  | zero =>
    intro b e
    step fm
    ring_nf; finish
  | succ k ih =>
    intro b e
    rw [show (k + 1) + 1 = (k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) (e + 1))
    ring_nf; finish

theorem r3_drain : ∀ k b c e, ⟨0, b + k, c, 0, e⟩ [fm]⊢* ⟨0, b, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro b c e; simp; exists 0
  | succ k ih =>
    intro b c e
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) e)
    ring_nf; finish

theorem main_trans (n e : ℕ) :
    ⟨0, 0, 2 * n + 3, 0, e + (2 * n + 3)⟩ [fm]⊢⁺
    ⟨0, 0, 2 * n + 5, 0, e + 3 * n + 6⟩ := by
  -- Phase 1: R4 steps
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring,
      show e + ((2 * n + 2) + 1) = (e + (2 * n + 2)) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (2 * n + 2) + 1, 0, (e + (2 * n + 2)) + 1⟩ =
        some ⟨1, 0, 2 * n + 2, 0, e + (2 * n + 2)⟩
    unfold fm; simp
  -- Remaining R4 steps
  have phase1 : ⟨1, 0, 2 * n + 2, 0, e + (2 * n + 2)⟩ [fm]⊢* ⟨2 * n + 3, 0, 0, 0, e⟩ := by
    have := r4_repeat (2 * n + 2) 1 0 e
    simp only [Nat.zero_add] at this
    rw [show 1 + (2 * n + 2) = 2 * n + 3 from by ring] at this
    exact this
  apply stepStar_trans phase1
  -- Phase 2: R5/R1 chain
  have phase2 : ⟨2 * n + 3, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 1, 0, 2 * n + 4, e + n + 2⟩ := by
    rw [show 2 * n + 3 = 2 * (n + 1) + 1 from by ring]
    have := r5r1_chain (n + 1) 0 e
    simp only [Nat.zero_add] at this
    rw [show 2 * (n + 1) + 2 = 2 * n + 4 from by ring,
        show e + (n + 1) + 1 = e + n + 2 from by ring] at this
    exact this
  apply stepStar_trans phase2
  -- Phase 3: R3 step
  have phase3 : ⟨0, 1, 0, 2 * n + 4, e + n + 2⟩ [fm]⊢* ⟨0, 0, 1, 2 * n + 4, e + n + 2⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm; finish
  apply stepStar_trans phase3
  -- Phase 4: R2/R3 loop
  have phase4 : ⟨0, 0, 1, 2 * n + 4, e + n + 2⟩ [fm]⊢* ⟨0, 2 * n + 5, 0, 0, e + 3 * n + 6⟩ := by
    rw [show 2 * n + 4 = (2 * n + 3) + 1 from by ring]
    have := r2r3_loop (2 * n + 3) 0 (e + n + 2)
    rw [show 0 + (2 * n + 3) + 2 = 2 * n + 5 from by ring,
        show (e + n + 2) + (2 * n + 3) + 1 = e + 3 * n + 6 from by ring] at this
    exact this
  apply stepStar_trans phase4
  -- Phase 5: R3 drain
  have := r3_drain (2 * n + 5) 0 0 (e + 3 * n + 6)
  simp only [Nat.zero_add] at this
  exact this

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 3⟩) (by unfold c₀; execute fm 8)
  show ¬halts fm (⟨0, 0, 2 * 0 + 3, 0, 0 + (2 * 0 + 3)⟩ : Q)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨0, 0, 2 * n + 3, 0, e + (2 * n + 3)⟩) ⟨0, 0⟩
  intro ⟨n, e⟩
  refine ⟨⟨n + 1, e + n + 1⟩, ?_⟩
  show ⟨0, 0, 2 * n + 3, 0, e + (2 * n + 3)⟩ [fm]⊢⁺ ⟨0, 0, 2 * (n + 1) + 3, 0, (e + n + 1) + (2 * (n + 1) + 3)⟩
  rw [show 2 * (n + 1) + 3 = 2 * n + 5 from by ring,
      show (e + n + 1) + (2 * n + 5) = e + 3 * n + 6 from by ring]
  exact main_trans n e

end Sz22_2003_unofficial_214
