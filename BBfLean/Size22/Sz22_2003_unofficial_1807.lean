import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1807: [9/10, 55/21, 2/3, 7/11, 1815/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  1  1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1807

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e+2⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1) (e := e))
    ring_nf; finish

theorem b_to_a : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (b := b))
    ring_nf; finish

theorem r2_drain : ∀ k, ⟨0, b + k, c, d + k, e⟩ [fm]⊢* ⟨0, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b) (c := c + 1) (d := d) (e := e + 1))
    ring_nf; finish

theorem r1r2_rounds : ∀ k, ⟨k, b, 1, d + k, e⟩ [fm]⊢* ⟨0, b + k, 1, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b := b + 1) (d := d) (e := e + 1))
    ring_nf; finish

theorem r3r1_loop : ∀ c, ⟨0, b + 1, c, 0, e⟩ [fm]⊢* ⟨0, b + c + 1, 0, 0, e⟩ := by
  intro c; induction' c with c ih generalizing b e
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (b := b + 1) (e := e))
    ring_nf; finish

theorem main_trans (n : ℕ) : ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
  -- Phase 1: e_to_d
  have p1 : ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢* ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ := by
    rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
    apply stepStar_trans (e_to_d (2 * n + 2) (a := n + 2) (d := 0) (e := 0))
    ring_nf; finish
  -- Phase 2: R5
  have p2 : ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢ ⟨n + 1, 1, 1, 2 * n + 2, 2⟩ := by
    show fm ⟨(n + 1) + 1, 0, 0, 2 * n + 2, 0⟩ = some ⟨n + 1, 1, 1, 2 * n + 2, 2⟩
    simp [fm]
  -- Phase 3: R1+R2 rounds
  have p3 : ⟨n + 1, 1, 1, 2 * n + 2, 2⟩ [fm]⊢* ⟨0, n + 2, 1, n + 1, n + 3⟩ := by
    rw [show 2 * n + 2 = (n + 1) + (n + 1) from by ring]
    apply stepStar_trans (r1r2_rounds (n + 1) (b := 1) (d := n + 1) (e := 2))
    ring_nf; finish
  -- Phase 4: R2 drain
  have p4 : ⟨0, n + 2, 1, n + 1, n + 3⟩ [fm]⊢* ⟨0, 1, n + 2, 0, 2 * n + 4⟩ := by
    have h := r2_drain (n + 1) (b := 1) (c := 1) (d := 0) (e := n + 3)
    rw [show 1 + (n + 1) = n + 2 from by ring,
        show 0 + (n + 1) = n + 1 from by ring] at h
    rw [show n + 3 + (n + 1) = 2 * n + 4 from by ring] at h
    exact h
  -- Phase 5: R3 then R1
  have p5 : ⟨0, 1, n + 2, 0, 2 * n + 4⟩ [fm]⊢* ⟨0, 2, n + 1, 0, 2 * n + 4⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]
    step fm
    step fm
    finish
  -- Phase 6: R3+R1 loop
  have p6 : ⟨0, 2, n + 1, 0, 2 * n + 4⟩ [fm]⊢* ⟨0, n + 3, 0, 0, 2 * n + 4⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (r3r1_loop (n + 1) (b := 1) (e := 2 * n + 4))
    ring_nf; finish
  -- Phase 7: b_to_a
  have p7 : ⟨0, n + 3, 0, 0, 2 * n + 4⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
    rw [show n + 3 = 0 + (n + 3) from by ring]
    apply stepStar_trans (b_to_a (n + 3) (a := 0) (b := 0) (e := 2 * n + 4))
    ring_nf; finish
  -- Compose: p1 is ⊢*, p2 is ⊢, so p1+p2 is ⊢⁺. Then p3..p7 are all ⊢*.
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus (step_stepPlus p2)
      (stepStar_trans p3 (stepStar_trans p4 (stepStar_trans p5 (stepStar_trans p6 p7)))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * n + 2⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨n + 1 + 2, 0, 0, 0, 2 * (n + 1) + 2⟩
  rw [show n + 1 + 2 = n + 3 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact main_trans n
