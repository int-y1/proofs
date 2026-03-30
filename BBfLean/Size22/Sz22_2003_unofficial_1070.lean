import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1070: [5/6, 16/15, 343/2, 3/7, 5/3]

Vector representation:
```
-1 -1  1  0
 0  1 -1  0
 0  0 -1  3
 0  0  0 -1
 0 -1  0  1
```

This Fractran program halts.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1070

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+4, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+3⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | _ => none

private theorem d_to_b : ∀ k, ∀ b d,
    ⟨(0 : ℕ), b, 0, d + k⟩ [fm]⊢* ⟨0, b + k, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) d

private theorem c_drain_step : ∀ c d,
    ⟨(0 : ℕ), 0, c + 1, d + 1⟩ [fm]⊢* ⟨0, 0, c, d + 12⟩ := by
  intro c d
  step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

private theorem chain_round : ∀ b c,
    ⟨(4 : ℕ), b + 5, c, 0⟩ [fm]⊢* ⟨4, b, c + 3, 0⟩ := by
  intro b c
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

private theorem chain_multi : ∀ k, ∀ b c,
    ⟨(4 : ℕ), b + 5 * k, c, 0⟩ [fm]⊢* ⟨4, b, c + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · ring_nf; finish
  · rw [show b + 5 * (k + 1) = (b + 5 * k) + 5 from by ring,
        show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring]
    apply stepStar_trans (chain_round (b + 5 * k) c)
    exact ih b (c + 3)

private theorem tail_0 : ∀ c,
    ⟨(4 : ℕ), 0, c, 0⟩ [fm]⊢* ⟨0, 0, c, 12⟩ := by
  intro c; step fm; step fm; step fm; step fm; ring_nf; finish

private theorem tail_1 : ∀ c,
    ⟨(4 : ℕ), 1, c, 0⟩ [fm]⊢* ⟨0, 0, c + 1, 9⟩ := by
  intro c; step fm; step fm; step fm; step fm; ring_nf; finish

private theorem tail_2 : ∀ c,
    ⟨(4 : ℕ), 2, c, 0⟩ [fm]⊢* ⟨0, 0, c + 2, 6⟩ := by
  intro c; step fm; step fm; step fm; step fm; ring_nf; finish

private theorem tail_3 : ∀ c,
    ⟨(4 : ℕ), 3, c, 0⟩ [fm]⊢* ⟨0, 0, c + 3, 3⟩ := by
  intro c; step fm; step fm; step fm; step fm; ring_nf; finish

private theorem c_drain_all : ∀ k, ∀ d,
    ⟨(0 : ℕ), 0, k, d + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 1 + 11 * k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · ring_nf; finish
  · rw [show d + 1 + 11 * (k + 1) = (d + 11) + 1 + 11 * k from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    apply stepStar_trans (c_drain_step k d)
    exact ih (d + 11)

private theorem opening : ∀ b,
    ⟨(0 : ℕ), b + 2, 0, 0⟩ [fm]⊢* ⟨4, b, 0, 0⟩ := by
  intro b; step fm; step fm; ring_nf; finish

private theorem r1_four : ∀ c,
    ⟨(4 : ℕ), 4, c, 0⟩ [fm]⊢* ⟨0, 0, c + 4, 0⟩ := by
  intro c
  apply stepStar_trans (step_stepStar (show fm ⟨4, 4, c, 0⟩ = some ⟨3, 3, c + 1, 0⟩ from by unfold fm; simp))
  apply stepStar_trans (step_stepStar (show fm ⟨3, 3, c + 1, 0⟩ = some ⟨2, 2, c + 2, 0⟩ from by unfold fm; simp))
  apply stepStar_trans (step_stepStar (show fm ⟨2, 2, c + 2, 0⟩ = some ⟨1, 1, c + 3, 0⟩ from by unfold fm; simp))
  exact step_stepStar (show fm ⟨1, 1, c + 3, 0⟩ = some ⟨0, 0, c + 4, 0⟩ from by unfold fm; simp)

private theorem chain_to_halt : ∀ k, ∀ c,
    ⟨(4 : ℕ), 4 + 5 * k, c, 0⟩ [fm]⊢* ⟨0, 0, c + 4 + 3 * k, 0⟩ := by
  intro k c
  apply stepStar_trans (chain_multi k 4 c)
  rw [show c + 4 + 3 * k = (c + 3 * k) + 4 from by ring]
  exact r1_four (c + 3 * k)

private theorem halted_at : ∀ c, halted fm ⟨(0 : ℕ), 0, c, 0⟩ := by
  intro c; rfl

private theorem cycle_r0 (q : ℕ) :
    ⟨(0 : ℕ), 0, 0, 5 * q + 2⟩ [fm]⊢* ⟨0, 0, 0, 33 * q + 12⟩ := by
  rw [show 5 * q + 2 = 0 + (5 * q + 2) from by ring]
  apply stepStar_trans (d_to_b (5 * q + 2) 0 0)
  rw [show 0 + (5 * q + 2) = (5 * q) + 2 from by ring]
  apply stepStar_trans (opening (5 * q))
  rw [show 5 * q = 0 + 5 * q from by ring]
  apply stepStar_trans (chain_multi q 0 0)
  rw [show 0 + 3 * q = 3 * q from by ring]
  apply stepStar_trans (tail_0 (3 * q))
  rw [show (12 : ℕ) = 11 + 1 from by ring,
      show 33 * q + 12 = 11 + 1 + 11 * (3 * q) from by ring]
  exact c_drain_all (3 * q) 11

private theorem cycle_r1 (q : ℕ) :
    ⟨(0 : ℕ), 0, 0, 5 * q + 3⟩ [fm]⊢* ⟨0, 0, 0, 33 * q + 20⟩ := by
  rw [show 5 * q + 3 = 0 + (5 * q + 3) from by ring]
  apply stepStar_trans (d_to_b (5 * q + 3) 0 0)
  rw [show 0 + (5 * q + 3) = (5 * q + 1) + 2 from by ring]
  apply stepStar_trans (opening (5 * q + 1))
  rw [show 5 * q + 1 = 1 + 5 * q from by ring]
  apply stepStar_trans (chain_multi q 1 0)
  rw [show 0 + 3 * q = 3 * q from by ring]
  apply stepStar_trans (tail_1 (3 * q))
  rw [show (9 : ℕ) = 8 + 1 from by ring]
  rw [show 33 * q + 20 = 8 + 1 + 11 * (3 * q + 1) from by ring]
  exact c_drain_all (3 * q + 1) 8

private theorem cycle_r2 (q : ℕ) :
    ⟨(0 : ℕ), 0, 0, 5 * q + 4⟩ [fm]⊢* ⟨0, 0, 0, 33 * q + 28⟩ := by
  rw [show 5 * q + 4 = 0 + (5 * q + 4) from by ring]
  apply stepStar_trans (d_to_b (5 * q + 4) 0 0)
  rw [show 0 + (5 * q + 4) = (5 * q + 2) + 2 from by ring]
  apply stepStar_trans (opening (5 * q + 2))
  rw [show 5 * q + 2 = 2 + 5 * q from by ring]
  apply stepStar_trans (chain_multi q 2 0)
  rw [show 0 + 3 * q = 3 * q from by ring]
  apply stepStar_trans (tail_2 (3 * q))
  rw [show (6 : ℕ) = 5 + 1 from by ring]
  rw [show 33 * q + 28 = 5 + 1 + 11 * (3 * q + 2) from by ring]
  exact c_drain_all (3 * q + 2) 5

private theorem cycle_r3 (q : ℕ) :
    ⟨(0 : ℕ), 0, 0, 5 * q + 5⟩ [fm]⊢* ⟨0, 0, 0, 33 * q + 36⟩ := by
  rw [show 5 * q + 5 = 0 + (5 * q + 5) from by ring]
  apply stepStar_trans (d_to_b (5 * q + 5) 0 0)
  rw [show 0 + (5 * q + 5) = (5 * q + 3) + 2 from by ring]
  apply stepStar_trans (opening (5 * q + 3))
  rw [show 5 * q + 3 = 3 + 5 * q from by ring]
  apply stepStar_trans (chain_multi q 3 0)
  rw [show 0 + 3 * q = 3 * q from by ring]
  apply stepStar_trans (tail_3 (3 * q))
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  rw [show 33 * q + 36 = 2 + 1 + 11 * (3 * q + 3) from by ring]
  exact c_drain_all (3 * q + 3) 2

private theorem cycle_to_halt (q : ℕ) :
    ⟨(0 : ℕ), 0, 0, 5 * q + 6⟩ [fm]⊢* ⟨0, 0, 3 * q + 4, 0⟩ := by
  rw [show 5 * q + 6 = 0 + (5 * q + 6) from by ring]
  apply stepStar_trans (d_to_b (5 * q + 6) 0 0)
  rw [show 0 + (5 * q + 6) = (5 * q + 4) + 2 from by ring]
  apply stepStar_trans (opening (5 * q + 4))
  rw [show 5 * q + 4 = 4 + 5 * q from by ring,
      show 3 * q + 4 = 0 + 4 + 3 * q from by ring]
  exact chain_to_halt q 0

theorem halts_thm : halts fm c₀ := by
  apply stepStar_halts (c₂ := ⟨0, 0, 0, 20⟩) (by execute fm 16)
  apply stepStar_halts (c₂ := ⟨0, 0, 0, 135⟩)
  · rw [show (20 : ℕ) = 5 * 3 + 5 from by ring,
        show (135 : ℕ) = 33 * 3 + 36 from by ring]
    exact cycle_r3 3
  apply stepStar_halts (c₂ := ⟨0, 0, 0, 894⟩)
  · rw [show (135 : ℕ) = 5 * 26 + 5 from by ring,
        show (894 : ℕ) = 33 * 26 + 36 from by ring]
    exact cycle_r3 26
  apply stepStar_halts (c₂ := ⟨0, 0, 0, 5902⟩)
  · rw [show (894 : ℕ) = 5 * 178 + 4 from by ring,
        show (5902 : ℕ) = 33 * 178 + 28 from by ring]
    exact cycle_r2 178
  apply stepStar_halts (c₂ := ⟨0, 0, 0, 38952⟩)
  · rw [show (5902 : ℕ) = 5 * 1180 + 2 from by ring,
        show (38952 : ℕ) = 33 * 1180 + 12 from by ring]
    exact cycle_r0 1180
  apply stepStar_halts (c₂ := ⟨0, 0, 0, 257082⟩)
  · rw [show (38952 : ℕ) = 5 * 7790 + 2 from by ring,
        show (257082 : ℕ) = 33 * 7790 + 12 from by ring]
    exact cycle_r0 7790
  apply stepStar_halts (c₂ := ⟨0, 0, 0, 1696740⟩)
  · rw [show (257082 : ℕ) = 5 * 51416 + 2 from by ring,
        show (1696740 : ℕ) = 33 * 51416 + 12 from by ring]
    exact cycle_r0 51416
  apply stepStar_halts (c₂ := ⟨0, 0, 0, 11198487⟩)
  · rw [show (1696740 : ℕ) = 5 * 339347 + 5 from by ring,
        show (11198487 : ℕ) = 33 * 339347 + 36 from by ring]
    exact cycle_r3 339347
  apply stepStar_halts (c₂ := ⟨0, 0, 0, 73910013⟩)
  · rw [show (11198487 : ℕ) = 5 * 2239697 + 2 from by ring,
        show (73910013 : ℕ) = 33 * 2239697 + 12 from by ring]
    exact cycle_r0 2239697
  apply stepStar_halts (c₂ := ⟨0, 0, 0, 487806086⟩)
  · rw [show (73910013 : ℕ) = 5 * 14782002 + 3 from by ring,
        show (487806086 : ℕ) = 33 * 14782002 + 20 from by ring]
    exact cycle_r1 14782002
  apply stepStar_halts (c₂ := ⟨0, 0, 292683652, 0⟩)
  · rw [show (487806086 : ℕ) = 5 * 97561216 + 6 from by ring,
        show (292683652 : ℕ) = 3 * 97561216 + 4 from by ring]
    exact cycle_to_halt 97561216
  exact halted_halts (halted_at 292683652)

end Sz22_2003_unofficial_1070
