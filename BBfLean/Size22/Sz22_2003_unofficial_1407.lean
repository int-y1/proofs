import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1407: [7/15, 1089/14, 44/3, 5/11, 3/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  2
 2 -1  0  0  1
 0  0  1  0 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1407

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 transfer: e to c
theorem e_to_c : ∀ k c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- R3 chain: drain b with c=0, d=0
theorem r3_chain : ∀ k a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm; apply stepStar_trans (ih (a + 2) (e + 1)); ring_nf; finish

-- Inner loop (even c): k rounds of R1,R1,R2
theorem inner_even : ∀ k A D E, ⟨A + k, 2, 2 * k, D, E⟩ [fm]⊢* ⟨A, 2, 0, D + k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show 2 * (k + 1) = (2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih A (D + 1) (E + 2)); ring_nf; finish

-- Inner loop (odd c): k rounds of R1,R1,R2 then final R1
theorem inner_odd : ∀ k A D E, ⟨A + k, 2, 2 * k + 1, D, E⟩ [fm]⊢* ⟨A, 1, 0, D + k + 1, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · step fm; finish
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih A (D + 1) (E + 2)); ring_nf; finish

-- Drain: (A, B, 0, D, E) →* (A+2B+3D, 0, 0, 0, E+B+4D)
-- by strong induction on D. Requires A+B >= 1 when D >= 1.
theorem drain : ∀ D, ∀ A B E, A + B ≥ 1 ∨ D = 0 →
    ⟨A, B, 0, D, E⟩ [fm]⊢* ⟨A + 2 * B + 3 * D, 0, 0, 0, E + B + 4 * D⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih
  intro A B E hpre
  rcases D with _ | D'
  · -- D=0: R3 chain or done
    rcases B with _ | B'
    · -- B=0: 0 steps
      exists 0
    · -- B>=1: R3 chain
      rw [show A + 2 * (B' + 1) + 3 * 0 = A + 2 * (B' + 1) from by ring,
          show E + (B' + 1) + 4 * 0 = E + (B' + 1) from by ring]
      exact r3_chain (B' + 1) A E
  · -- D'+1: split on A
    rcases A with _ | A'
    · -- A=0: need B >= 1. R3 fires.
      have hB : B ≥ 1 := by omega
      obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
      step fm
      -- at (2, B', 0, D'+1, E+1). R2 fires.
      step fm
      -- at (1, B'+2, 0, D', E+3). Apply IH at D' < D'+1.
      apply stepStar_trans (ih D' (by omega) 1 (B' + 2) (E + 3) (by omega))
      ring_nf; finish
    · -- A'+1 >= 1: R2 fires.
      step fm
      -- at (A', B+2, 0, D', E+2). Apply IH at D' < D'+1.
      apply stepStar_trans (ih D' (by omega) A' (B + 2) (E + 2) (by omega))
      ring_nf; finish

-- Main phase c=0
theorem phase_c0 (a : ℕ) : ⟨a + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 0, 1⟩ := by
  step fm; step fm; finish

-- Main phase odd c = 2k+1
theorem phase_odd (k a' : ℕ) :
    ⟨a' + k + 2, 0, 2 * k + 1, 0, 0⟩ [fm]⊢⁺ ⟨a' + 3 * k + 4, 0, 0, 0, 6 * k + 4⟩ := by
  rw [show a' + k + 2 = (a' + k) + 2 from by ring]
  step fm; step fm; step fm
  -- at (a'+k, 2, 2k, 0, 2)
  apply stepStar_trans (inner_even k a' 0 2)
  -- at (a', 2, 0, k, 2k+2)
  rw [show (0 + k : ℕ) = k from by ring, show 2 + 2 * k = 2 * k + 2 from by ring]
  apply stepStar_trans (drain k a' 2 (2 * k + 2) (by omega))
  ring_nf; finish

-- Main phase even c = 2k+2
theorem phase_even (k a' : ℕ) :
    ⟨a' + k + 3, 0, 2 * k + 2, 0, 0⟩ [fm]⊢⁺ ⟨a' + 3 * k + 6, 0, 0, 0, 6 * k + 7⟩ := by
  rw [show a' + k + 3 = (a' + k + 1) + 2 from by ring]
  step fm; step fm; step fm
  -- at (a'+k+1, 2, 2k+1, 0, 2)
  rw [show (a' + k + 1 : ℕ) = (a' + 1) + k from by ring]
  apply stepStar_trans (inner_odd k (a' + 1) 0 2)
  -- at (a'+1, 1, 0, k+1, 2k+2)
  rw [show (0 + k + 1 : ℕ) = k + 1 from by ring, show 2 + 2 * k = 2 * k + 2 from by ring]
  -- R2: a'+1 >= 1 and k+1 >= 1
  step fm
  -- at (a', 3, 0, k, 2k+4)
  apply stepStar_trans (drain k a' 3 (2 * k + 4) (by omega))
  ring_nf; finish

-- Unified main transition
theorem main_trans (a e : ℕ) (h : 2 * a ≥ e + 3) :
    ⟨a, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a + e + 1, 0, 0, 0, 3 * e + 1⟩ := by
  rw [show (e : ℕ) = 0 + e from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c e 0 0 (a := a))
  rw [show (0 + e : ℕ) = e from by ring]
  rcases e with _ | e
  · -- e = 0
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    exact phase_c0 a'
  · rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- e even = k+k, c = e+1 = 2k+1 (odd)
      subst hk
      rw [show k + k + 1 = 2 * k + 1 from by ring]
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + k + 2 := ⟨a - k - 2, by omega⟩
      apply stepPlus_stepStar_stepPlus (phase_odd k a')
      ring_nf; finish
    · -- e odd = 2k+1, c = e+1 = 2k+2 (even)
      subst hk
      rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring]
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + k + 3 := ⟨a - k - 3, by omega⟩
      apply stepPlus_stepStar_stepPlus (phase_even k a')
      ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩)
  · execute fm 2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ 2 * a ≥ e + 3)
  · intro c ⟨a, e, hq, h⟩; subst hq
    exact ⟨⟨a + e + 1, 0, 0, 0, 3 * e + 1⟩,
      ⟨a + e + 1, 3 * e + 1, rfl, by omega⟩,
      main_trans a e h⟩
  · exact ⟨2, 1, rfl, by omega⟩

end Sz22_2003_unofficial_1407
