import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #431: [27/35, 1/33, 50/3, 11/25, 21/2]

Vector representation:
```
 0  3 -1 -1  0
 0 -1  0  0 -1
 1 -1  2  0  0
 0  0 -2  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_431

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 repeated: (a, 0, c + 2*k, 0, e) ->* (a, 0, c, 0, e + k)
theorem r4_chain : ∀ k c e, ⟨a, 0, c + 2 * k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro c e
    rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (c + 2) e)
    step fm; ring_nf; finish

-- R3 chain: (a, b + k, c, 0, 0) ->* (a + k, b, c + 2*k, 0, 0)
theorem r3_chain : ∀ k a c, ⟨a, b + k, c, 0, 0⟩ [fm]⊢* ⟨a + k, b, c + 2 * k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro a c
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Generalized drain: (A + 1 + m, 0, 0, d, m) ->⁺ (A + 1, 0, 2, d + m + 1, 0)
theorem drain_gen : ∀ m d, ⟨A + 1 + m, 0, 0, d, m⟩ [fm]⊢⁺ ⟨A + 1, 0, 2, d + m + 1, 0⟩ := by
  intro m; induction m with
  | zero => intro d; step fm; step fm; ring_nf; finish
  | succ m ih =>
    intro d
    rw [show A + 1 + (m + 1) = (A + 1 + m) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (stepPlus_stepStar (ih (d + 1)))
    ring_nf; finish

-- Process D: (A, B, 2, D+1, 0) ->* (A + B + 3*(D+1), 0, 2*B + 5*(D+1) + 2, 0, 0)
theorem process_d_gen :
    ∀ D A B, ⟨A, B, 2, D + 1, 0⟩ [fm]⊢* ⟨A + B + 3 * (D + 1), 0, 2 * B + 5 * (D + 1) + 2, 0, 0⟩ := by
  intro D; induction D using Nat.strongRecOn with
  | ind D ih =>
    intro A B
    rcases D with _ | _ | D'
    · -- D+1 = 1: R1 then R3 chain
      step fm
      have h := @r3_chain 0 (B + 3) A 1; rw [Nat.zero_add] at h
      apply stepStar_trans h
      ring_nf; finish
    · -- D+1 = 2: R1, R1 then R3 chain
      step fm; step fm
      have h := @r3_chain 0 (B + 3 + 3) A 0; rw [Nat.zero_add] at h
      apply stepStar_trans h
      ring_nf; finish
    · -- D+1 = D'+3: R1, R1, R3 then recurse on D'
      step fm; step fm; step fm
      apply stepStar_trans (ih D' (by omega) _ _)
      ring_nf; finish

-- Even transition: (n+k+1, 0, 2*k, 0, 0) ->+ (n+3*k+4, 0, 5*k+7, 0, 0)
theorem even_trans :
    ⟨n + k + 1, 0, 2 * k, 0, 0⟩ [fm]⊢⁺ ⟨n + 3 * k + 4, 0, 5 * k + 7, 0, 0⟩ := by
  -- Phase 1: R4 chain k times
  rw [show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain k 0 0)
  simp only [Nat.zero_add]
  -- Phase 2: drain_gen (stepPlus)
  rw [show n + k + 1 = n + 1 + k from by ring]
  apply stepPlus_stepStar_stepPlus (drain_gen k 0)
  simp only [Nat.zero_add]
  -- Phase 3: process_d_gen
  apply stepStar_trans (process_d_gen k (n + 1) 0)
  ring_nf; finish

-- Odd k=0: (a+2, 0, 1, 0, 0) -> (a+5, 0, 8, 0, 0)
theorem odd0_trans : ⟨a + 2, 0, 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 5, 0, 8, 0, 0⟩ := by
  execute fm 6

-- Odd k=1: (a+2, 0, 3, 0, 0) -> (a+4, 0, 6, 0, 0)
theorem odd1_trans : ⟨a + 2, 0, 3, 0, 0⟩ [fm]⊢⁺ ⟨a + 4, 0, 6, 0, 0⟩ := by
  execute fm 7

-- Odd k=2: (a+2, 0, 5, 0, 0) -> (a+3, 0, 4, 0, 0)
theorem odd2_trans : ⟨a + 2, 0, 5, 0, 0⟩ [fm]⊢⁺ ⟨a + 3, 0, 4, 0, 0⟩ := by
  execute fm 8

-- Odd k=3: (a+2, 0, 7, 0, 0) -> (a+2, 0, 2, 0, 0)
theorem odd3_trans : ⟨a + 2, 0, 7, 0, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 2, 0, 0⟩ := by
  execute fm 9

-- Odd k=4: (a+5, 0, 9, 0, 0) -> (a+4, 0, 0, 0, 0)
theorem odd4_trans : ⟨a + 5, 0, 9, 0, 0⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 0, 0⟩ := by
  execute fm 10

-- Odd k>=5: k = j+5, (m+j+6, 0, 2*j+11, 0, 0) -> (m+3*j+10, 0, 5*j+12, 0, 0)
theorem odd_big_trans :
    ⟨m + j + 6, 0, 2 * j + 11, 0, 0⟩ [fm]⊢⁺ ⟨m + 3 * j + 10, 0, 5 * j + 12, 0, 0⟩ := by
  -- Phase 1: R4 (j+5) times
  rw [show 2 * j + 11 = 1 + 2 * (j + 5) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (j + 5) 1 0)
  simp only [Nat.zero_add]
  -- Phase 2: 6 fixed steps: R5, R1, R2x4 -> (m+j+5, 0, 0, 0, j+1)
  step fm; step fm; step fm; step fm; step fm; step fm
  -- Phase 3: drain_gen with A = m+3, m' = j+1
  rw [show m + j + 5 = (m + 3) + 1 + (j + 1) from by ring]
  apply stepStar_trans (stepPlus_stepStar (drain_gen (j + 1) 0))
  simp only [Nat.zero_add]
  -- Phase 4: process_d_gen with D = j+1, A = m+4
  rw [show m + 3 + 1 = m + 4 from by ring]
  apply stepStar_trans (process_d_gen (j + 1) (m + 4) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 7, 0, 0⟩)
  · execute fm 6
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a, 0, c, 0, 0⟩ ∧ a ≥ 2 ∧ 2 * a > c)
  · intro q ⟨a, c, hq, ha, hac⟩; subst hq
    rcases Nat.even_or_odd c with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- c even: c = k + k
      subst hk
      obtain ⟨n, rfl⟩ : ∃ n, a = n + k + 1 := ⟨a - k - 1, by omega⟩
      refine ⟨⟨n + 3 * k + 4, 0, 5 * k + 7, 0, 0⟩,
        ⟨n + 3 * k + 4, 5 * k + 7, rfl, by omega, by omega⟩, ?_⟩
      rw [show k + k = 2 * k from by ring]
      exact even_trans
    · -- c odd: c = 2*k + 1
      subst hk
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k ≥ 5 from by omega) with
        rfl | rfl | rfl | rfl | rfl | hk5
      · -- k=0, c=1
        obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
        exact ⟨⟨m + 5, 0, 8, 0, 0⟩, ⟨m + 5, 8, rfl, by omega, by omega⟩, odd0_trans⟩
      · -- k=1, c=3
        obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
        exact ⟨⟨m + 4, 0, 6, 0, 0⟩, ⟨m + 4, 6, rfl, by omega, by omega⟩, odd1_trans⟩
      · -- k=2, c=5
        obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
        exact ⟨⟨m + 3, 0, 4, 0, 0⟩, ⟨m + 3, 4, rfl, by omega, by omega⟩, odd2_trans⟩
      · -- k=3, c=7
        obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
        exact ⟨⟨m + 2, 0, 2, 0, 0⟩, ⟨m + 2, 2, rfl, by omega, by omega⟩, odd3_trans⟩
      · -- k=4, c=9
        obtain ⟨m, rfl⟩ : ∃ m, a = m + 5 := ⟨a - 5, by omega⟩
        exact ⟨⟨m + 4, 0, 0, 0, 0⟩, ⟨m + 4, 0, rfl, by omega, by omega⟩, odd4_trans⟩
      · -- k >= 5
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
        obtain ⟨m, rfl⟩ : ∃ m, a = m + j + 6 := ⟨a - j - 6, by omega⟩
        refine ⟨⟨m + 3 * j + 10, 0, 5 * j + 12, 0, 0⟩,
          ⟨m + 3 * j + 10, 5 * j + 12, rfl, by omega, by omega⟩, ?_⟩
        rw [show 2 * (j + 5) + 1 = 2 * j + 11 from by ring]
        exact odd_big_trans
  · exact ⟨4, 7, rfl, by omega, by omega⟩
