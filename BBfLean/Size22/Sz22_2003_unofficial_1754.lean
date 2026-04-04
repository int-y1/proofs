import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1754: [9/10, 2/21, 3773/2, 5/49, 2/11]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  0
-1  0  0  3  1
 0  0  1 -2  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1754

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+1⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k, e + k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 3) (e := e + 1))
    ring_nf; finish

theorem r4_chain_step : ⟨0, 0, c, d + 2, e⟩ [fm]⊢ ⟨0, 0, c + 1, d, e⟩ := by simp [fm]

theorem r4_chain : ∀ k, ⟨0, 0, c, d + 2 * k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    apply stepStar_trans (step_stepStar (r4_chain_step (c := c) (d := d + 2 * k) (e := e)))
    apply stepStar_trans (ih (c := c + 1) (d := d))
    ring_nf; finish

theorem phase3_init : ⟨0, 0, c + 2, 1, c + 2⟩ [fm]⊢* ⟨0, 3, c, 0, c + 1⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem r5r1_shift_chain : ∀ k, ⟨0, b, k, 0, k + 1⟩ [fm]⊢* ⟨0, b + 2 * k, 0, 0, 1⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · rw [show k + 1 + 1 = (k + 1) + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (b := b + 2))
    ring_nf; finish

theorem processing : ⟨0, 0, c + 2, 1, c + 2⟩ [fm]⊢* ⟨0, 2 * c + 3, 0, 0, 1⟩ := by
  apply stepStar_trans phase3_init
  apply stepStar_trans (r5r1_shift_chain c (b := 3))
  ring_nf; finish

theorem r5_r3 : ⟨0, b, 0, 0, 1⟩ [fm]⊢⁺ ⟨0, b, 0, 3, 1⟩ := by
  step fm; step fm; finish

theorem drain_cycle : ⟨a, b + 3, 0, 3, e⟩ [fm]⊢* ⟨a + 2, b, 0, 3, e + 1⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem drain_gen : ∀ M, ⟨a, 3 * (M + 1), 0, 3, e⟩ [fm]⊢* ⟨a + 2 * M + 3, 0, 0, 0, e + M⟩ := by
  intro M; induction' M with M ih generalizing a e
  · step fm; step fm; step fm; finish
  · rw [show 3 * (M + 1 + 1) = 3 * (M + 1) + 3 from by ring]
    apply stepStar_trans (drain_cycle (a := a) (b := 3 * (M + 1)) (e := e))
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

theorem drain_mod1 : ∀ M, ⟨a, 3 * M + 1, 0, 3, e⟩ [fm]⊢* ⟨a + 2 * M + 1, 0, 0, 2, e + M⟩ := by
  intro M; induction' M with M ih generalizing a e
  · step fm; ring_nf; finish
  · rw [show 3 * (M + 1) + 1 = 3 * M + 1 + 3 from by ring]
    apply stepStar_trans (drain_cycle (a := a) (b := 3 * M + 1) (e := e))
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

theorem process_r5r3_drain_mod1 :
    ⟨0, 0, 3 * n + 4, 1, 3 * n + 4⟩ [fm]⊢⁺ ⟨4 * n + 5, 0, 0, 2, 2 * n + 3⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 3 * n + 4 = (3 * n + 2) + 2 from by ring]
    exact processing (c := 3 * n + 2)
  apply stepPlus_stepStar_stepPlus
  · rw [show 2 * (3 * n + 2) + 3 = 6 * n + 7 from by ring]
    exact r5_r3 (b := 6 * n + 7)
  rw [show 6 * n + 7 = 3 * (2 * n + 2) + 1 from by ring]
  apply stepStar_trans (drain_mod1 (2 * n + 2) (a := 0) (e := 1))
  ring_nf; finish

theorem process_r5r3_drain_gen :
    ⟨0, 0, 6 * n + 2, 1, 6 * n + 2⟩ [fm]⊢⁺ ⟨8 * n + 3, 0, 0, 0, 4 * n + 1⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 6 * n + 2 = (6 * n) + 2 from by ring]
    exact processing (c := 6 * n)
  apply stepPlus_stepStar_stepPlus
  · rw [show 2 * (6 * n) + 3 = 12 * n + 3 from by ring]
    exact r5_r3 (b := 12 * n + 3)
  rw [show 12 * n + 3 = 3 * (4 * n + 0 + 1) from by ring]
  apply stepStar_trans (drain_gen (4 * n) (a := 0) (e := 1))
  ring_nf; finish

theorem half1 : ∀ n, ⟨2 * n + 3, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨4 * n + 5, 0, 0, 2, 2 * n + 3⟩ := by
  intro n
  apply stepStar_stepPlus_stepPlus
  · exact r3_chain (2 * n + 3) (d := 0) (e := n + 1)
  apply stepStar_stepPlus_stepPlus
  · rw [show 0 + 3 * (2 * n + 3) = 1 + 2 * (3 * n + 4) from by ring]
    exact r4_chain (3 * n + 4) (c := 0) (d := 1) (e := n + 1 + (2 * n + 3))
  rw [show (0 : ℕ) + (3 * n + 4) = 3 * n + 4 from by ring,
      show n + 1 + (2 * n + 3) = 3 * n + 4 from by ring]
  exact process_r5r3_drain_mod1

theorem half2 : ∀ n, ⟨4 * n + 1, 0, 0, 2, 2 * n + 1⟩ [fm]⊢⁺ ⟨8 * n + 3, 0, 0, 0, 4 * n + 1⟩ := by
  intro n
  apply stepStar_stepPlus_stepPlus
  · rw [show (2 : ℕ) = 2 from rfl]
    exact r3_chain (4 * n + 1) (d := 2) (e := 2 * n + 1)
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 + 3 * (4 * n + 1) = 1 + 2 * (6 * n + 2) from by ring]
    exact r4_chain (6 * n + 2) (c := 0) (d := 1) (e := 2 * n + 1 + (4 * n + 1))
  rw [show (0 : ℕ) + (6 * n + 2) = 6 * n + 2 from by ring,
      show 2 * n + 1 + (4 * n + 1) = 6 * n + 2 from by ring]
  exact process_r5r3_drain_gen

theorem main_trans : ∀ n, ⟨2 * n + 3, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨8 * n + 11, 0, 0, 0, 4 * n + 5⟩ := by
  intro n
  apply stepPlus_trans (half1 n)
  exact half2 (n + 1)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩) (by execute fm 19)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, 0, 0, n + 1⟩) 0
  intro n; refine ⟨4 * n + 4, ?_⟩
  show ⟨2 * n + 3, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨2 * (4 * n + 4) + 3, 0, 0, 0, (4 * n + 4) + 1⟩
  rw [show 2 * (4 * n + 4) + 3 = 8 * n + 11 from by ring,
      show (4 * n + 4) + 1 = 4 * n + 5 from by ring]
  exact main_trans n
