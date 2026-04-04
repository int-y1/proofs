import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1881: [9/35, 5/33, 242/5, 7/121, 15/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 1  0 -1  0  2
 0  0  0  1 -2
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1881

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r5r1_drain : ∀ k, ∀ a b d, ⟨a + k, b, 0, d + k, 0⟩ [fm]⊢* ⟨a, b + 3 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (b + 3) d)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a c e, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 0, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c (e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ a d e, ⟨a, 0, 0, d, e + 2 * k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    apply stepStar_trans (ih a d (e + 2))
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; finish

theorem interleaved : ∀ k, ∀ a b c, ⟨a, b + 2 * k, c + 1, 0, 1⟩ [fm]⊢*
    ⟨a + k, b, c + k + 1, 0, 1⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]
    apply stepStar_trans (ih a (b + 2) c)
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring]
    step fm; step fm; step fm; finish

-- Full Phase 2: (a+1, B, 0, 0, 0) ->⁺ (a+B+2, 0, 0, 0, B+3)
-- Proof: R5, R3, R2 opening, then interleaved drain, then R3 chain.
-- We use strong induction on B to handle the R2 step at the end.
-- Alternative: split even/odd and handle b=0 and b=1 tails.
-- Actually simplest: prove the whole thing directly for each parity.

theorem phase2_full (B : ℕ) : ⟨a + 1, B, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + B + 2, 0, 0, 0, B + 3⟩ := by
  -- Opening: 3 steps (a+1, B, 0, 0, 0) -> (a+1, B, 1, 0, 1)
  step fm  -- R5: a+1 >= 1
  rw [show B + 1 = B + 1 from rfl]
  step fm  -- R3: c=1 >= 1
  step fm  -- R2: b=B+1 >= 1, e=2 >= 1
  -- Goal: (a+1, B, 1, 0, 1) ⊢* (a+B+2, 0, 0, 0, B+3)
  -- Now: b=B, c=1, e=1. Use interleaved drain for B/2 rounds.
  rcases Nat.even_or_odd B with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- B = 2m
    rw [show m + m = 2 * m from by ring] at hm; subst hm
    have il := interleaved m (a + 1) 0 0
    simp only [Nat.zero_add] at il
    apply stepStar_trans il
    have rc := r3_chain (m + 1) (a + 1 + m) 0 1
    simp only [Nat.zero_add] at rc
    apply stepStar_trans rc
    ring_nf; finish
  · -- B = 2m+1
    subst hm
    have il := interleaved m (a + 1) 1 0
    simp only [Nat.zero_add] at il
    rw [show 1 + 2 * m = 2 * m + 1 from by ring] at il
    apply stepStar_trans il
    have r2_step : ⟨a + 1 + m, 1, m + 1, 0, 1⟩ [fm]⊢ ⟨a + 1 + m, 0, m + 2, 0, 0⟩ := by
      rw [show a + 1 + m = (a + m) + 1 from by ring]; simp [fm]
    apply stepStar_trans (step_stepStar r2_step)
    have rc := r3_chain (m + 2) (a + 1 + m) 0 0
    simp only [Nat.zero_add] at rc
    apply stepStar_trans rc
    ring_nf; finish

theorem d0e0 : ⟨a + 2, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 1, 1⟩ := by
  execute fm 5

theorem d1e1 : ⟨a + 3, 0, 0, 1, 1⟩ [fm]⊢⁺ ⟨a + 5, 0, 0, 2, 0⟩ := by
  execute fm 10

theorem e1_open : ⟨a + 1, 0, 0, d + 2, 1⟩ [fm]⊢* ⟨a, 4, 0, d, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Main transition for D >= 1, E = 0:
-- (a+D+2, 0, 0, D, 0) -> drain -> (a+2, 3D, 0, 0, 0) -> Phase 2 -> (a+3D+3, 0, 0, 0, 3D+3) -> R4 drain
theorem main_e0 (D : ℕ) (_hD : D ≥ 1) :
    ⟨a + D + 2, 0, 0, D, 0⟩ [fm]⊢⁺ ⟨a + 3 * D + 3, 0, 0, (3 * D + 3) / 2, (3 * D + 3) % 2⟩ := by
  have drain := r5r1_drain D (a + 2) 0 0
  simp only [Nat.zero_add] at drain
  rw [show a + 2 + D = a + D + 2 from by ring] at drain
  apply stepStar_stepPlus_stepPlus drain
  apply stepPlus_stepStar_stepPlus
  · rw [show a + 2 = (a + 1) + 1 from by ring]
    exact phase2_full (3 * D) (a := a + 1)
  rw [show a + 1 + 3 * D + 2 = a + 3 * D + 3 from by ring]
  have r4 := r4_chain ((3 * D + 3) / 2) (a + 3 * D + 3) 0 ((3 * D + 3) % 2)
  simp only [Nat.zero_add] at r4
  rw [show (3 * D + 3) % 2 + 2 * ((3 * D + 3) / 2) = 3 * D + 3 from by omega] at r4
  exact r4

-- Main transition for D >= 2, E = 1:
-- (a+D+2, 0, 0, D, 1) -> e1_open -> (a+D+1, 4, 0, D-2, 0) -> drain -> (a+3, 3D-2, 0, 0, 0) -> Phase 2 -> R4
theorem main_e1 (D : ℕ) (hD : D ≥ 2) :
    ⟨a + D + 2, 0, 0, D, 1⟩ [fm]⊢⁺ ⟨a + 3 * D + 2, 0, 0, (3 * D + 1) / 2, (3 * D + 1) % 2⟩ := by
  have open_step := e1_open (a := a + D + 1) (d := D - 2)
  rw [show (D - 2) + 2 = D from by omega, show a + D + 1 + 1 = a + D + 2 from by ring] at open_step
  apply stepStar_stepPlus_stepPlus open_step
  have drain := r5r1_drain (D - 2) (a + 3) 4 0
  simp only [Nat.zero_add] at drain
  rw [show a + 3 + (D - 2) = a + D + 1 from by omega] at drain
  apply stepStar_stepPlus_stepPlus drain
  rw [show 4 + 3 * (D - 2) = 3 * D - 2 from by omega]
  apply stepPlus_stepStar_stepPlus
  · rw [show a + 3 = (a + 2) + 1 from by ring]
    exact phase2_full (3 * D - 2) (a := a + 2)
  have hD3 : 3 * D - 2 + 2 = 3 * D := Nat.sub_add_cancel (by omega)
  have hDrw : a + 2 + (3 * D - 2) + 2 = a + 3 * D + 2 := by
    rw [show a + 2 + (3 * D - 2) + 2 = a + (3 * D - 2 + 2) + 2 from by ring, hD3]
  rw [hDrw]
  have r4 := r4_chain ((3 * D + 1) / 2) (a + 3 * D + 2) 0 ((3 * D + 1) % 2)
  simp only [Nat.zero_add] at r4
  have hD4 : 3 * D - 2 + 3 = 3 * D + 1 := by omega
  rw [hD4]
  rw [show (3 * D + 1) % 2 + 2 * ((3 * D + 1) / 2) = 3 * D + 1 from by omega] at r4
  exact r4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 2, 0⟩) (by execute fm 15)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a D E, q = ⟨a, 0, 0, D, E⟩ ∧ a ≥ D + 2 ∧ E ≤ 1 ∧ (E = 1 → D ≥ 1))
  · intro c ⟨a, D, E, hq, ha, hE, hED⟩; subst hq
    rcases E with _ | _ | _
    · -- E = 0
      rcases D with _ | D
      · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
        exact ⟨_, ⟨a' + 3, 1, 1, rfl, by omega, by omega, fun _ => by omega⟩, d0e0⟩
      · obtain ⟨a', rfl⟩ : ∃ a', a = a' + (D + 1) + 2 := ⟨a - D - 3, by omega⟩
        refine ⟨_, ⟨a' + 3 * (D + 1) + 3, (3 * (D + 1) + 3) / 2, (3 * (D + 1) + 3) % 2,
          rfl, by omega, by omega, fun h => by omega⟩, main_e0 (D + 1) (by omega)⟩
    · -- E = 1
      have hD1 : D ≥ 1 := hED rfl
      rcases D with _ | D
      · omega
      · rcases D with _ | D
        · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
          exact ⟨_, ⟨a' + 5, 2, 0, rfl, by omega, by omega,
            fun h => absurd h (by omega)⟩, d1e1⟩
        · obtain ⟨a', rfl⟩ : ∃ a', a = a' + (D + 2) + 2 := ⟨a - D - 4, by omega⟩
          refine ⟨_, ⟨a' + 3 * (D + 2) + 2, (3 * (D + 2) + 1) / 2, (3 * (D + 2) + 1) % 2,
            rfl, by omega, by omega, fun h => by omega⟩, main_e1 (D + 2) (by omega)⟩
    · omega
  · exact ⟨4, 2, 0, rfl, by omega, by omega, fun h => absurd h (by omega)⟩
