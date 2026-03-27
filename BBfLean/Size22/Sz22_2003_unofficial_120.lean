import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #120: [1/405, 14/15, 9/7, 25/2, 3/5]

Vector representation:
```
 0 -4 -1  0
 1 -1 -1  1
 0  2  0 -1
-1  0  2  0
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_120

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+4, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R4 repeated: a → c
theorem a_to_c : ∀ k, ∀ a c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3 repeated: d → b
theorem d_to_b : ∀ k, ∀ a b, ⟨a, b, 0, k⟩ [fm]⊢* ⟨a, b+2*k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  rw [show (k + 1) = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Inner loop: (a, 0, c+2, d+1) -> (a+2, 0, c, d+2) in 3 steps
-- Iterated k times: (a, 0, c+2k, d+1) -> (a+2k, 0, c, d+k+1)
theorem inner_loop : ∀ k, ∀ a c d, ⟨a, 0, c+2*k, d+1⟩ [fm]⊢* ⟨a+2*k, 0, c, d+k+1⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ (d+1))
  ring_nf; finish

-- b-8 drain round: uses R1, R1, R4 to reduce b by 8 and a by 1
-- (a+1, b+8, 2, 0) -> (a+1, b+4, 1, 0) -> (a+1, b, 0, 0) -> (a, b, 2, 0)
theorem b8_drain : ∀ k, ∀ a b, ⟨a+k, b+8*k, 2, 0⟩ [fm]⊢* ⟨a, b, 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + 8 * (k + 1) = (b + 8 * k) + 4 + 4 from by ring]
  step fm
  rw [show b + 8 * k + 4 = (b + 8 * k) + 4 from by ring]
  step fm
  -- R4: ((a+k)+1, b+8*k, 0, 0) -> (a+k, b+8*k, 2, 0)
  apply stepStar_trans (c₂ := ⟨a+k, b+8*k, 2, 0⟩)
  · apply step_stepStar
    show fm ⟨(a+k)+1, b+8*k, 0, 0⟩ = some ⟨a+k, b+8*k, 2, 0⟩
    simp [fm]
  exact ih _ _

-- Terminal drain b=4: 1 step
theorem drain_b4 : ∀ a, ⟨a, 4, 2, 0⟩ [fm]⊢* ⟨a, 0, 1, 0⟩ := by
  intro a; step fm; finish

-- Terminal drain b=7: 4 steps -> (a, 0, 1, 0)
theorem drain_b7 : ∀ a, ⟨a, 7, 2, 0⟩ [fm]⊢* ⟨a, 0, 1, 0⟩ := by
  intro a; step fm; step fm; step fm; step fm
  exact drain_b4 a

-- Terminal drain b=5 -> b=2: 4 steps
theorem drain_b5_to_b2 : ∀ a, ⟨a, 5, 2, 0⟩ [fm]⊢* ⟨a, 2, 2, 0⟩ := by
  intro a; step fm; step fm; step fm; step fm; finish

-- Terminal drain b=2 -> a+1,b=4: 5 steps
theorem drain_b2_to_b4 : ∀ a, ⟨a, 2, 2, 0⟩ [fm]⊢* ⟨a+1, 4, 2, 0⟩ := by
  intro a; step fm; step fm; step fm; step fm; step fm; finish

-- Terminal drain b=5: gain +1
theorem drain_b5 : ∀ a, ⟨a, 5, 2, 0⟩ [fm]⊢* ⟨a+1, 0, 1, 0⟩ := by
  intro a
  apply stepStar_trans (drain_b5_to_b2 a)
  apply stepStar_trans (drain_b2_to_b4 a)
  exact drain_b4 (a+1)

-- Terminal drain b=3 -> a+1,b=5: 5 steps
theorem drain_b3_to_b5 : ∀ a, ⟨a, 3, 2, 0⟩ [fm]⊢* ⟨a+1, 5, 2, 0⟩ := by
  intro a; step fm; step fm; step fm; step fm; step fm; finish

-- Terminal drain b=3: gain +2
theorem drain_b3 : ∀ a, ⟨a, 3, 2, 0⟩ [fm]⊢* ⟨a+2, 0, 1, 0⟩ := by
  intro a
  apply stepStar_trans (drain_b3_to_b5 a)
  apply stepStar_trans (drain_b5_to_b2 (a+1))
  apply stepStar_trans (drain_b2_to_b4 (a+1))
  exact drain_b4 (a+2)

-- Terminal drain b=1 -> a+1,b=3: 5 steps
theorem drain_b1_to_b3 : ∀ a, ⟨a, 1, 2, 0⟩ [fm]⊢* ⟨a+1, 3, 2, 0⟩ := by
  intro a; step fm; step fm; step fm; step fm; step fm; finish

-- Terminal drain b=1: gain +3
theorem drain_b1 : ∀ a, ⟨a, 1, 2, 0⟩ [fm]⊢* ⟨a+3, 0, 1, 0⟩ := by
  intro a
  apply stepStar_trans (drain_b1_to_b3 a)
  apply stepStar_trans (drain_b3_to_b5 (a+1))
  apply stepStar_trans (drain_b5_to_b2 (a+2))
  apply stepStar_trans (drain_b2_to_b4 (a+2))
  exact drain_b4 (a+3)

-- Drain start: (a+1, 0, 1, d+1) -> (a+1, 2d+3, 2, 0)
-- R3: -> (a+1, 2, 1, d). R2: -> (a+2, 1, 0, d+1). d_to_b: -> (a+2, 2d+3, 0, 0). R4: -> (a+1, 2d+3, 2, 0).
theorem drain_start (d a : ℕ) : ⟨a+1, 0, 1, d+1⟩ [fm]⊢* ⟨a+1, 2*d+3, 2, 0⟩ := by
  step fm; step fm
  apply stepStar_trans (c₂ := ⟨a+2, 2*d+3, 0, 0⟩)
  · have h := d_to_b (d+1) (a+2) 1
    convert h using 2; ring_nf
  -- R4: (a+2, 2*d+3, 0, 0) -> (a+1, 2*d+3, 2, 0)
  apply step_stepStar
  show fm ⟨(a+1)+1, 2*d+3, 0, 0⟩ = some ⟨a+1, 2*d+3, 2, 0⟩
  simp [fm]

-- Main transition for n = 4k+1 (n' = 7k+3)
theorem trans_mod1 (k : ℕ) : ⟨4*k+1, 0, 1, 0⟩ [fm]⊢⁺ ⟨7*k+3, 0, 1, 0⟩ := by
  rw [show 4 * k + 1 = (4 * k) + 1 from by ring]
  -- First R4 step provides stepPlus
  step fm
  -- Now goal is ⊢* (7k+3, 0, 1, 0) at (4k, 0, 3, 0)
  apply stepStar_trans (c₂ := ⟨0, 0, 8*k+3, 0⟩)
  · have h := a_to_c (4*k) 0 3
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- R5 + R2
  rw [show 8 * k + 3 = (8 * k + 2) + 1 from by ring]
  step fm
  rw [show 8 * k + 2 = (8 * k + 1) + 1 from by ring]
  step fm
  -- Now at (1, 0, 8k+1, 1). Inner loop.
  apply stepStar_trans (c₂ := ⟨8*k+1, 0, 1, 4*k+1⟩)
  · have h := inner_loop (4*k) 1 1 0
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨8*k+1, 8*k+3, 2, 0⟩)
  · have h := drain_start (4*k) (8*k)
    convert h using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨7*k+1, 3, 2, 0⟩)
  · have h := b8_drain k (7*k+1) 3
    convert h using 2; ring_nf
  exact drain_b3 (7*k+1)

-- Main transition for n = 4k+2 (n' = 7k+4)
theorem trans_mod2 (k : ℕ) : ⟨4*k+2, 0, 1, 0⟩ [fm]⊢⁺ ⟨7*k+4, 0, 1, 0⟩ := by
  rw [show 4 * k + 2 = (4 * k + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨0, 0, 8*k+5, 0⟩)
  · have h := a_to_c (4*k+1) 0 3
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  rw [show 8 * k + 5 = (8 * k + 4) + 1 from by ring]
  step fm
  rw [show 8 * k + 4 = (8 * k + 3) + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨8*k+3, 0, 1, 4*k+2⟩)
  · have h := inner_loop (4*k+1) 1 1 0
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨8*k+3, 8*k+5, 2, 0⟩)
  · have h := drain_start (4*k+1) (8*k+2)
    convert h using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨7*k+3, 5, 2, 0⟩)
  · have h := b8_drain k (7*k+3) 5
    convert h using 2; ring_nf
  exact drain_b5 (7*k+3)

-- Main transition for n = 4k+3 (n' = 7k+5)
theorem trans_mod3 (k : ℕ) : ⟨4*k+3, 0, 1, 0⟩ [fm]⊢⁺ ⟨7*k+5, 0, 1, 0⟩ := by
  rw [show 4 * k + 3 = (4 * k + 2) + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨0, 0, 8*k+7, 0⟩)
  · have h := a_to_c (4*k+2) 0 3
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  rw [show 8 * k + 7 = (8 * k + 6) + 1 from by ring]
  step fm
  rw [show 8 * k + 6 = (8 * k + 5) + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨8*k+5, 0, 1, 4*k+3⟩)
  · have h := inner_loop (4*k+2) 1 1 0
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨8*k+5, 8*k+7, 2, 0⟩)
  · have h := drain_start (4*k+2) (8*k+4)
    convert h using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨7*k+5, 7, 2, 0⟩)
  · have h := b8_drain k (7*k+5) 7
    convert h using 2; ring_nf
  exact drain_b7 (7*k+5)

-- Main transition for n = 4(k+1) = 4k+4 (n' = 7k+9)
theorem trans_mod0 (k : ℕ) : ⟨4*k+4, 0, 1, 0⟩ [fm]⊢⁺ ⟨7*k+9, 0, 1, 0⟩ := by
  rw [show 4 * k + 4 = (4 * k + 3) + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨0, 0, 8*k+9, 0⟩)
  · have h := a_to_c (4*k+3) 0 3
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  rw [show 8 * k + 9 = (8 * k + 8) + 1 from by ring]
  step fm
  rw [show 8 * k + 8 = (8 * k + 7) + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨8*k+7, 0, 1, 4*k+4⟩)
  · have h := inner_loop (4*k+3) 1 1 0
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨8*k+7, 8*k+9, 2, 0⟩)
  · have h := drain_start (4*k+3) (8*k+6)
    convert h using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨7*k+6, 1, 2, 0⟩)
  · have h := b8_drain (k+1) (7*k+6) 1
    convert h using 2; ring_nf
  exact drain_b1 (7*k+6)

-- Combined main transition
theorem main_trans (n : ℕ) (hn : n ≥ 1) :
    ∃ n', n' ≥ 1 ∧ (⟨n, 0, 1, 0⟩ [fm]⊢⁺ ⟨n', 0, 1, 0⟩) := by
  have hmod := Nat.div_add_mod n 4
  set q := n / 4
  set r := n % 4
  have hr : r < 4 := Nat.mod_lt n (by omega)
  interval_cases r
  · rcases q with _ | k
    · omega
    rw [show n = 4 * k + 4 from by omega]
    exact ⟨7*k+9, by omega, trans_mod0 k⟩
  · rw [show n = 4 * q + 1 from by omega]
    exact ⟨7*q+3, by omega, trans_mod1 q⟩
  · rw [show n = 4 * q + 2 from by omega]
    exact ⟨7*q+4, by omega, trans_mod2 q⟩
  · rw [show n = 4 * q + 3 from by omega]
    exact ⟨7*q+5, by omega, trans_mod3 q⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 1, 0⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, n ≥ 1 ∧ q = ⟨n, 0, 1, 0⟩)
  · intro c ⟨n, hn, hq⟩
    subst hq
    obtain ⟨n', hn', hstep⟩ := main_trans n hn
    exact ⟨⟨n', 0, 1, 0⟩, ⟨n', hn', rfl⟩, hstep⟩
  · exact ⟨1, by omega, rfl⟩

end Sz22_2003_unofficial_120
