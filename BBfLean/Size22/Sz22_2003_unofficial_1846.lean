import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1846: [9/35, 1/33, 50/3, 11/5, 245/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  0  0 -1
 1 -1  2  0  0
 0  0 -1  0  1
-1  0  1  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1846

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+2, e⟩
  | _ => none

theorem c_to_e : ∀ k, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c) (e := e + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a, b + k, c, 0, 0⟩ [fm]⊢* ⟨a + k, b, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (b := b) (c := c + 2))
    ring_nf; finish

theorem expand_bd : ∀ D, ∀ a b, ⟨a, b + 1, 0, D, 0⟩ [fm]⊢* ⟨a + b + 2 * D + 1, 0, 2 * b + 3 * D + 2, 0, 0⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro a b
  rcases D with _ | _ | D
  · -- D = 0: R3 chain
    show ⟨a, b + 1, 0, 0, 0⟩ [fm]⊢* ⟨a + b + 1, 0, 2 * b + 2, 0, 0⟩
    rw [show b + 1 = 0 + (b + 1) from by ring,
        show a + b + 1 = a + (b + 1) from by ring,
        show 2 * b + 2 = 0 + 2 * (b + 1) from by ring]
    exact r3_chain (b + 1) (a := a) (b := 0) (c := 0)
  · -- D = 1: R3, R1, R3, then R3 chain
    step fm -- R3: (a+1, b, 2, 1, 0)
    step fm -- R1: (a+1, b+2, 1, 0, 0)
    step fm -- R3: (a+2, b+1, 3, 0, 0)
    rw [show b + 1 = 0 + (b + 1) from by ring]
    apply stepStar_trans (r3_chain (b + 1) (a := a + 2) (b := 0) (c := 3))
    ring_nf; finish
  · -- D + 2: R3, R1, R1, then recurse on D
    step fm -- R3: (a+1, b, 2, D+2, 0)
    step fm -- R1: (a+1, b+2, 1, D+1, 0)
    step fm -- R1: (a+1, b+4, 0, D, 0)
    rw [show b + 4 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih D (by omega) (a + 1) (b + 3))
    ring_nf; finish

theorem staircase : ∀ k, ⟨a + k, 0, 0, d, e + 2 * k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
    step fm -- R5: (a+k, 0, 1, d+2, e+2*k+1)
    step fm -- R1: (a+k, 2, 0, d+1, e+2*k+1)
    step fm -- R2: (a+k, 1, 0, d+1, e+2*k)
    step fm -- R2: (a+k, 0, 0, d+1, e+2*k-1)
    show ⟨a + k, 0, 0, d + 1, e + 2 * k⟩ [fm]⊢* ⟨a, 0, 0, d + (k + 1), e⟩
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    exact ih (a := a) (d := d + 1) (e := e)

theorem expansion_e0 : ⟨a + 1, 0, 0, D, 0⟩ [fm]⊢⁺ ⟨a + 2 * D + 4, 0, 0, 0, 3 * D + 7⟩ := by
  step fm -- R5: (a, 0, 1, D+2, 0)
  step fm -- R1: (a, 2, 0, D+1, 0)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (expand_bd (D + 1) a 1)
  rw [show a + 1 + 2 * (D + 1) + 1 = a + 2 * D + 4 from by ring,
      show 2 * 1 + 3 * (D + 1) + 2 = 3 * D + 7 from by ring]
  rw [show 3 * D + 7 = 0 + (3 * D + 7) from by ring]
  apply stepStar_trans (c_to_e (3 * D + 7) (a := a + 2 * D + 4) (c := 0) (e := 0))
  ring_nf; finish

theorem expansion_e1_d0 : ⟨a + 1, 0, 0, 0, 1⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 0, 5⟩ := by
  execute fm 12

theorem expansion_e1 : ∀ D, ⟨a + 1, 0, 0, D, 1⟩ [fm]⊢⁺ ⟨a + 2 * D + 3, 0, 0, 0, 3 * D + 5⟩ := by
  intro D
  rcases D with _ | D
  · exact expansion_e1_d0
  · -- D + 1 >= 1
    step fm -- R5: (a, 0, 1, D+3, 1)
    step fm -- R1: (a, 2, 0, D+2, 1)
    step fm -- R2: (a, 1, 0, D+2, 0)
    step fm -- R3: (a+1, 0, 2, D+2, 0)
    step fm -- R1: (a+1, 2, 1, D+1, 0)
    step fm -- R1: (a+1, 4, 0, D, 0)
    rw [show (4 : ℕ) = 3 + 1 from by ring]
    apply stepStar_trans (expand_bd D (a + 1) 3)
    rw [show a + 1 + 3 + 2 * D + 1 = a + 2 * (D + 1) + 3 from by ring,
        show 2 * 3 + 3 * D + 2 = 3 * (D + 1) + 5 from by ring]
    rw [show 3 * (D + 1) + 5 = 0 + (3 * (D + 1) + 5) from by ring]
    apply stepStar_trans (c_to_e (3 * (D + 1) + 5) (a := a + 2 * (D + 1) + 3) (c := 0) (e := 0))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 7⟩) (by execute fm 14)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ 2 * a ≥ e + 1 ∧ a ≥ 1)
  · intro c ⟨a, e, hq, ha, ha1⟩; subst hq
    rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- e even: e = K + K
      subst hK
      obtain ⟨m, rfl⟩ : ∃ m, a = m + K + 1 := ⟨a - K - 1, by omega⟩
      refine ⟨⟨m + 2 * K + 4, 0, 0, 0, 3 * K + 7⟩,
              ⟨m + 2 * K + 4, 3 * K + 7, rfl, by omega, by omega⟩, ?_⟩
      rw [show m + K + 1 = (m + 1) + K from by ring,
          show K + K = 0 + 2 * K from by ring]
      apply stepStar_stepPlus_stepPlus (staircase K (a := m + 1) (d := 0) (e := 0))
      rw [show (0 : ℕ) + K = K from by ring]
      exact expansion_e0 (a := m) (D := K)
    · -- e odd: e = 2K + 1
      subst hK
      obtain ⟨m, rfl⟩ : ∃ m, a = m + K + 1 := ⟨a - K - 1, by omega⟩
      refine ⟨⟨m + 2 * K + 3, 0, 0, 0, 3 * K + 5⟩,
              ⟨m + 2 * K + 3, 3 * K + 5, rfl, by omega, by omega⟩, ?_⟩
      rw [show m + K + 1 = (m + 1) + K from by ring,
          show 2 * K + 1 = 1 + 2 * K from by ring]
      apply stepStar_stepPlus_stepPlus (staircase K (a := m + 1) (d := 0) (e := 1))
      rw [show (0 : ℕ) + K = K from by ring]
      exact expansion_e1 K (a := m)
  · exact ⟨4, 7, rfl, by omega, by omega⟩
