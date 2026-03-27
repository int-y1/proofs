import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #164: [1/45, 49/5, 10/77, 3/7, 6655/2]

Vector representation:
```
 0 -2 -1  0  0
 0  0 -1  2  0
 1  0  1 -1 -1
 0  1  0 -1  0
-1  0  1  0  3
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_164

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+3⟩
  | _ => none

-- Phase 1: R3+R2 chain (b=0)
theorem r3r2_b0 : ∀ k a d, ⟨a, 0, 0, d+1, k+1⟩ [fm]⊢* ⟨a+k+1, 0, 0, d+k+2, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; step fm; ring_nf; finish
  · rw [show (k + 1 : ℕ) + 1 = (k + 1) + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (d + 1))
    ring_nf; finish

-- Phase 1: R3+R2 chain (b=1)
theorem r3r2_b1 : ∀ k a d, ⟨a, 1, 0, d+1, k+1⟩ [fm]⊢* ⟨a+k+1, 1, 0, d+k+2, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; step fm; ring_nf; finish
  · rw [show (k + 1 : ℕ) + 1 = (k + 1) + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (d + 1))
    ring_nf; finish

-- Phase 2: R4 chain
theorem r4_chain : ∀ k a b, ⟨a, b, 0, k, 0⟩ [fm]⊢* ⟨a, b+k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · step fm
    apply stepStar_trans (ih a (b + 1))
    ring_nf; finish

-- Phase 3: R5+R1 chain
theorem r5r1_chain : ∀ k a b e, ⟨a+k, b+2*k, 0, 0, e⟩ [fm]⊢* ⟨a, b, 0, 0, e+3*k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a b (e + 3))
    ring_nf; finish

-- Phase 4a: R5+R2 step (b=0)
theorem r5r2_b0 : ⟨a+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a, 0, 0, 2, e+3⟩ := by
  step fm; step fm; finish

-- Phase 4b: R5+R2 step (b=1)
theorem r5r2_b1 : ⟨a+1, 1, 0, 0, e⟩ [fm]⊢⁺ ⟨a, 1, 0, 2, e+3⟩ := by
  step fm; step fm; finish

-- Cycle for b=0, B=d+e+5 even: d+e+5 = 2*K
theorem cycle_b0_Beven (hB : d + e + 5 = 2 * K) (hae : a + e + 3 ≥ K + 1) :
    ⟨a, 0, 0, d+2, e+3⟩ [fm]⊢⁺ ⟨a+e+2-K, 0, 0, 2, 3*K+3⟩ := by
  rw [show d + 2 = (d + 1) + 1 from by ring, show e + 3 = (e + 2) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r3r2_b0 (e + 2) a (d + 1))
  rw [show a + (e + 2) + 1 = a + e + 3 from by ring,
      show d + 1 + (e + 2) + 2 = d + e + 5 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (d+e+5) (a+e+3) 0)
  rw [show 0 + (d + e + 5) = 0 + 2 * K from by omega,
      show a + e + 3 = (a + e + 3 - K) + K from by omega,
      show (0 : ℕ) + 2 * K = 0 + 2 * K from rfl]
  apply stepStar_stepPlus_stepPlus (r5r1_chain K (a+e+3-K) 0 0)
  rw [Nat.zero_add, show a + e + 3 - K = (a + e + 2 - K) + 1 from by omega]
  exact r5r2_b0

-- Cycle for b=0, B=d+e+5 odd: d+e+5 = 2*K+1
theorem cycle_b0_Bodd (hB : d + e + 5 = 2 * K + 1) (hae : a + e + 3 ≥ K + 1) :
    ⟨a, 0, 0, d+2, e+3⟩ [fm]⊢⁺ ⟨a+e+2-K, 1, 0, 2, 3*K+3⟩ := by
  rw [show d + 2 = (d + 1) + 1 from by ring, show e + 3 = (e + 2) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r3r2_b0 (e + 2) a (d + 1))
  rw [show a + (e + 2) + 1 = a + e + 3 from by ring,
      show d + 1 + (e + 2) + 2 = d + e + 5 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (d+e+5) (a+e+3) 0)
  rw [show 0 + (d + e + 5) = 1 + 2 * K from by omega,
      show a + e + 3 = (a + e + 3 - K) + K from by omega]
  apply stepStar_stepPlus_stepPlus (r5r1_chain K (a+e+3-K) 1 0)
  rw [Nat.zero_add,
      show a + e + 3 - K = (a + e + 2 - K) + 1 from by omega]
  exact r5r2_b1

-- Cycle for b=1, B=1+d+e+5 even: d+e+6 = 2*K
theorem cycle_b1_Beven (hB : d + e + 6 = 2 * K) (hae : a + e + 3 ≥ K + 1) :
    ⟨a, 1, 0, d+2, e+3⟩ [fm]⊢⁺ ⟨a+e+2-K, 0, 0, 2, 3*K+3⟩ := by
  rw [show d + 2 = (d + 1) + 1 from by ring, show e + 3 = (e + 2) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r3r2_b1 (e + 2) a (d + 1))
  rw [show a + (e + 2) + 1 = a + e + 3 from by ring,
      show d + 1 + (e + 2) + 2 = d + e + 5 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (d+e+5) (a+e+3) 1)
  rw [show 1 + (d + e + 5) = 0 + 2 * K from by omega,
      show a + e + 3 = (a + e + 3 - K) + K from by omega,
      show (0 : ℕ) + 2 * K = 0 + 2 * K from rfl]
  apply stepStar_stepPlus_stepPlus (r5r1_chain K (a+e+3-K) 0 0)
  rw [Nat.zero_add, show a + e + 3 - K = (a + e + 2 - K) + 1 from by omega]
  exact r5r2_b0

-- Cycle for b=1, B=1+d+e+5 odd: d+e+6 = 2*K+1
theorem cycle_b1_Bodd (hB : d + e + 6 = 2 * K + 1) (hae : a + e + 3 ≥ K + 1) :
    ⟨a, 1, 0, d+2, e+3⟩ [fm]⊢⁺ ⟨a+e+2-K, 1, 0, 2, 3*K+3⟩ := by
  rw [show d + 2 = (d + 1) + 1 from by ring, show e + 3 = (e + 2) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r3r2_b1 (e + 2) a (d + 1))
  rw [show a + (e + 2) + 1 = a + e + 3 from by ring,
      show d + 1 + (e + 2) + 2 = d + e + 5 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (d+e+5) (a+e+3) 1)
  rw [show 1 + (d + e + 5) = 1 + 2 * K from by omega,
      show a + e + 3 = (a + e + 3 - K) + K from by omega]
  apply stepStar_stepPlus_stepPlus (r5r1_chain K (a+e+3-K) 1 0)
  rw [Nat.zero_add,
      show a + e + 3 - K = (a + e + 2 - K) + 1 from by omega]
  exact r5r2_b1

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 3⟩)
  · execute fm 2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a b d e, q = ⟨a, b, 0, d + 2, e + 3⟩ ∧ b ≤ 1 ∧ 2 * a + e ≥ b + d)
  · intro c ⟨a, b, d, e, hq, hb, hae⟩; subst hq
    rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl
    · -- b = 0
      rcases Nat.even_or_odd (d + e + 5) with ⟨K, hK⟩ | ⟨K, hK⟩
      · -- B even: d+e+5 = K+K
        have hK2 : d + e + 5 = 2 * K := by omega
        exact ⟨_, ⟨a + e + 2 - K, 0, 0, 3 * K, rfl, by omega, by omega⟩,
          cycle_b0_Beven hK2 (by omega)⟩
      · -- B odd: d+e+5 = 2*K+1
        exact ⟨_, ⟨a + e + 2 - K, 1, 0, 3 * K, rfl, by omega, by omega⟩,
          cycle_b0_Bodd hK (by omega)⟩
    · -- b = 1
      rcases Nat.even_or_odd (d + e + 6) with ⟨K, hK⟩ | ⟨K, hK⟩
      · -- B even: d+e+6 = K+K
        have hK2 : d + e + 6 = 2 * K := by omega
        exact ⟨_, ⟨a + e + 2 - K, 0, 0, 3 * K, rfl, by omega, by omega⟩,
          cycle_b1_Beven hK2 (by omega)⟩
      · -- B odd: d+e+6 = 2*K+1
        exact ⟨_, ⟨a + e + 2 - K, 1, 0, 3 * K, rfl, by omega, by omega⟩,
          cycle_b1_Bodd hK (by omega)⟩
  · exact ⟨0, 0, 0, 0, rfl, by omega, by omega⟩
