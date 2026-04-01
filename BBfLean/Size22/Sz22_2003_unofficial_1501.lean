import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1501: [7/15, 9/77, 242/3, 5/11, 847/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 1 -1  0  0  2
 0  0  1  0 -1
-1  0  0  1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1501

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | _ => none

-- R4 chain: move e to c
theorem r4_chain : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

-- R3 chain: drain b into a and e
theorem r3_chain : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 2))
    ring_nf; finish

-- Drain loop: one iteration (7 steps)
theorem drain_step : ⟨a + 1, 0, c + 4, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Drain loop iterated k times
theorem drain_loop : ∀ k, ⟨a + k, 0, c + 4 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih generalizing a c d
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show c + 4 * (k + 1) = (c + 4) + 4 * k from by ring]
    apply stepStar_trans (ih (a := a + 1) (c := c + 4))
    apply stepStar_trans drain_step
    ring_nf; finish

-- Chain: R2/R3 interleaving converts (A, B, 0, D, 2) to canonical form
-- Formula: (A, B, 0, D, 2) →* (A+B+2D, 0, 0, 0, 2B+3D+2)
theorem chain : ∀ D, ∀ A B,
    ⟨A, B, 0, D, 2⟩ [fm]⊢* ⟨A + B + 2 * D, 0, 0, 0, 2 * B + 3 * D + 2⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro A B
  rcases D with _ | _ | D
  · -- D = 0: just R3 chain
    rw [show B = 0 + B from by ring]
    apply stepStar_trans (r3_chain B (a := A) (b := 0) (e := 2))
    ring_nf; finish
  · -- D = 1: R2, R3, then R3 chain
    step fm; step fm
    rw [show B + 1 = 0 + (B + 1) from by ring]
    apply stepStar_trans (r3_chain (B + 1) (a := A + 1) (b := 0) (e := 3))
    ring_nf; finish
  · -- D + 2: R2, R2, R3, then IH
    step fm; step fm; step fm
    apply stepStar_trans (ih D (by omega) (A + 1) (B + 3))
    ring_nf; finish

-- Tail c'=0 with chain: (a+1, 0, 0, d, 0) →⁺ (a+2d+2, 0, 0, 0, 3d+5)
theorem tail_c0 : ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 2, 0, 0, 0, 3 * d + 5⟩ := by
  step fm
  apply stepStar_trans (chain (d + 1) a 0)
  ring_nf; finish

-- Tail c'=1 with chain: (a+1, 0, 1, d+1, 0) →⁺ (a+2d+5, 0, 0, 0, 3d+9)
theorem tail_c1 : ⟨a + 1, 0, 1, d + 1, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 5, 0, 0, 0, 3 * d + 9⟩ := by
  step fm  -- R5: (a, 0, 1, d+2, 2)
  step fm  -- R2: (a, 2, 1, d+1, 1)
  step fm  -- R1: (a, 1, 0, d+2, 1)
  step fm  -- R2: (a, 3, 0, d+1, 0)
  step fm  -- R3: (a+1, 2, 0, d+1, 2)
  apply stepStar_trans (chain (d + 1) (a + 1) 2)
  ring_nf; finish

-- Tail c'=2 with chain: (a+1, 0, 2, d+1, 0) →⁺ (a+2d+6, 0, 0, 0, 3d+10)
theorem tail_c2 : ⟨a + 1, 0, 2, d + 1, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 6, 0, 0, 0, 3 * d + 10⟩ := by
  step fm  -- R5: (a, 0, 2, d+2, 2)
  step fm  -- R2: (a, 2, 2, d+1, 1)
  step fm  -- R1: (a, 1, 1, d+2, 1)
  step fm  -- R1: (a, 0, 0, d+3, 1)
  step fm  -- R2: (a, 2, 0, d+2, 0)
  step fm  -- R3: (a+1, 1, 0, d+2, 2)
  apply stepStar_trans (chain (d + 2) (a + 1) 1)
  ring_nf; finish

-- Tail c'=3 with chain: (a+1, 0, 3, d+1, 0) →⁺ (a+2d+7, 0, 0, 0, 3d+11)
theorem tail_c3 : ⟨a + 1, 0, 3, d + 1, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 7, 0, 0, 0, 3 * d + 11⟩ := by
  step fm  -- R5: (a, 0, 3, d+2, 2)
  step fm  -- R2: (a, 2, 3, d+1, 1)
  step fm  -- R1: (a, 1, 2, d+2, 1)
  step fm  -- R1: (a, 0, 1, d+3, 1)
  step fm  -- R2: (a, 2, 1, d+2, 0)
  step fm  -- R1: (a, 1, 0, d+3, 0)
  step fm  -- R3: (a+1, 0, 0, d+3, 2)
  apply stepStar_trans (chain (d + 3) (a + 1) 0)
  ring_nf; finish

-- Full transition for e = 4*(n+1) (e mod 4 = 0, e >= 4)
-- (a+n+2, 0, 0, 0, 4n+4) →⁺ (a+6n+8, 0, 0, 0, 9n+14)
theorem full_r0 :
    ⟨a + n + 2, 0, 0, 0, 4 * n + 4⟩ [fm]⊢⁺ ⟨a + 6 * n + 8, 0, 0, 0, 9 * n + 14⟩ := by
  -- R4 chain: e → c
  rw [show (4 * n + 4 : ℕ) = 0 + (4 * n + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (4 * n + 4) (a := a + n + 2) (c := 0) (e := 0))
  -- Now at (a+n+2, 0, 4n+4, 0, 0)
  -- Drain loop: n+1 iterations
  rw [show a + n + 2 = (a + 1) + (n + 1) from by ring,
      show (0 : ℕ) + (4 * n + 4) = 0 + 4 * (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop (n + 1) (a := a + 1) (c := 0) (d := 0))
  -- Now at (a+1, 0, 0, 3*(n+1), 0) = (a+1, 0, 0, 3n+3, 0)
  rw [show (0 : ℕ) + 3 * (n + 1) = 3 * n + 3 from by ring]
  apply stepPlus_stepStar_stepPlus (tail_c0 (a := a) (d := 3 * n + 3))
  ring_nf; finish

-- Full transition for e = 4*(n+1)+1 (e mod 4 = 1, e >= 5)
-- (a+n+2, 0, 0, 0, 4n+5) →⁺ (a+6n+9, 0, 0, 0, 9n+15)
theorem full_r1 :
    ⟨a + n + 2, 0, 0, 0, 4 * n + 5⟩ [fm]⊢⁺ ⟨a + 6 * n + 9, 0, 0, 0, 9 * n + 15⟩ := by
  rw [show (4 * n + 5 : ℕ) = 0 + (4 * n + 5) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (4 * n + 5) (a := a + n + 2) (c := 0) (e := 0))
  rw [show a + n + 2 = (a + 1) + (n + 1) from by ring,
      show (0 : ℕ) + (4 * n + 5) = 1 + 4 * (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop (n + 1) (a := a + 1) (c := 1) (d := 0))
  rw [show (0 : ℕ) + 3 * (n + 1) = (3 * n + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (tail_c1 (a := a) (d := 3 * n + 2))
  ring_nf; finish

-- Full transition for e = 4*(n+1)+2 (e mod 4 = 2, e >= 6)
-- (a+n+2, 0, 0, 0, 4n+6) →⁺ (a+6n+10, 0, 0, 0, 9n+16)
theorem full_r2 :
    ⟨a + n + 2, 0, 0, 0, 4 * n + 6⟩ [fm]⊢⁺ ⟨a + 6 * n + 10, 0, 0, 0, 9 * n + 16⟩ := by
  rw [show (4 * n + 6 : ℕ) = 0 + (4 * n + 6) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (4 * n + 6) (a := a + n + 2) (c := 0) (e := 0))
  rw [show a + n + 2 = (a + 1) + (n + 1) from by ring,
      show (0 : ℕ) + (4 * n + 6) = 2 + 4 * (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop (n + 1) (a := a + 1) (c := 2) (d := 0))
  rw [show (0 : ℕ) + 3 * (n + 1) = (3 * n + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (tail_c2 (a := a) (d := 3 * n + 2))
  ring_nf; finish

-- Full transition for e = 4*(n+1)+3 (e mod 4 = 3, e >= 7)
-- (a+n+2, 0, 0, 0, 4n+7) →⁺ (a+6n+11, 0, 0, 0, 9n+17)
theorem full_r3 :
    ⟨a + n + 2, 0, 0, 0, 4 * n + 7⟩ [fm]⊢⁺ ⟨a + 6 * n + 11, 0, 0, 0, 9 * n + 17⟩ := by
  rw [show (4 * n + 7 : ℕ) = 0 + (4 * n + 7) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (4 * n + 7) (a := a + n + 2) (c := 0) (e := 0))
  rw [show a + n + 2 = (a + 1) + (n + 1) from by ring,
      show (0 : ℕ) + (4 * n + 7) = 3 + 4 * (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop (n + 1) (a := a + 1) (c := 3) (d := 0))
  rw [show (0 : ℕ) + 3 * (n + 1) = (3 * n + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (tail_c3 (a := a) (d := 3 * n + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: (1, 0, 0, 0, 0) →* (9, 0, 0, 0, 15)
  apply stepStar_not_halts_not_halts (c₂ := ⟨9, 0, 0, 0, 15⟩)
  · execute fm 32
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ 4 * a ≥ e + 8 ∧ e ≥ 4)
  · intro c ⟨a, e, hq, ha, he⟩; subst hq
    obtain ⟨n, rfl | rfl | rfl | rfl⟩ :
        ∃ n, e = 4 * n ∨ e = 4 * n + 1 ∨ e = 4 * n + 2 ∨ e = 4 * n + 3 :=
      ⟨e / 4, by omega⟩
    · -- e = 4*n, n >= 1
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, a = F + m + 2 := ⟨a - m - 2, by omega⟩
      refine ⟨⟨F + 6 * m + 8, 0, 0, 0, 9 * m + 14⟩,
        ⟨F + 6 * m + 8, 9 * m + 14, rfl, by omega, by omega⟩, ?_⟩
      show ⟨F + m + 2, 0, 0, 0, 4 * (m + 1)⟩ [fm]⊢⁺ _
      rw [show 4 * (m + 1) = 4 * m + 4 from by ring]
      exact full_r0
    · -- e = 4*n+1, n >= 1
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, a = F + m + 2 := ⟨a - m - 2, by omega⟩
      refine ⟨⟨F + 6 * m + 9, 0, 0, 0, 9 * m + 15⟩,
        ⟨F + 6 * m + 9, 9 * m + 15, rfl, by omega, by omega⟩, ?_⟩
      show ⟨F + m + 2, 0, 0, 0, 4 * (m + 1) + 1⟩ [fm]⊢⁺ _
      rw [show 4 * (m + 1) + 1 = 4 * m + 5 from by ring]
      exact full_r1
    · -- e = 4*n+2, n >= 1
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, a = F + m + 2 := ⟨a - m - 2, by omega⟩
      refine ⟨⟨F + 6 * m + 10, 0, 0, 0, 9 * m + 16⟩,
        ⟨F + 6 * m + 10, 9 * m + 16, rfl, by omega, by omega⟩, ?_⟩
      show ⟨F + m + 2, 0, 0, 0, 4 * (m + 1) + 2⟩ [fm]⊢⁺ _
      rw [show 4 * (m + 1) + 2 = 4 * m + 6 from by ring]
      exact full_r2
    · -- e = 4*n+3, n >= 1
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, a = F + m + 2 := ⟨a - m - 2, by omega⟩
      refine ⟨⟨F + 6 * m + 11, 0, 0, 0, 9 * m + 17⟩,
        ⟨F + 6 * m + 11, 9 * m + 17, rfl, by omega, by omega⟩, ?_⟩
      show ⟨F + m + 2, 0, 0, 0, 4 * (m + 1) + 3⟩ [fm]⊢⁺ _
      rw [show 4 * (m + 1) + 3 = 4 * m + 7 from by ring]
      exact full_r3
  · exact ⟨9, 15, rfl, by omega, by omega⟩
