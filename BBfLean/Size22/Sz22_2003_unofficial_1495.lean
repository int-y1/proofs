import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1495: [7/15, 9/77, 100/7, 11/5, 35/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 2  0  2 -1  0
 0  0 -1  0  1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1495

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 chain: transfer c to e.
theorem c_to_e : ∀ k a e, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih a (e + 1)); ring_nf; finish

-- R3 chain: transfer d to a and c.
theorem r3_chain : ∀ k a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 2) (c + 2)); ring_nf; finish

-- Drain first round (b=0): R5-R2-R1-R2.
theorem drain_first (A E : ℕ) :
    ⟨A + 1, 0, 0, 0, E + 2⟩ [fm]⊢* ⟨A, 3, 0, 0, E⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Drain subsequent round (b>=1): R5-R1-R2-R2.
theorem drain_round (A B E : ℕ) :
    ⟨A + 1, B + 1, 0, 0, E + 2⟩ [fm]⊢* ⟨A, B + 4, 0, 0, E⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Chain of k drain rounds (b>=1).
theorem drain_b1 : ∀ k A B E, ⟨A + k, B + 1, 0, 0, E + 2 * k⟩ [fm]⊢* ⟨A, B + 3 * k + 1, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A B E
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show E + 2 * (k + 1) = (E + 2 * k) + 2 from by ring]
    apply stepStar_trans (drain_round (A + k) B (E + 2 * k))
    rw [show B + 4 = (B + 3) + 1 from by ring]
    apply stepStar_trans (ih A (B + 3) E)
    rw [show B + 3 + 3 * k + 1 = B + 3 * (k + 1) + 1 from by ring]; finish

-- Full drain for even e: first round + m subsequent rounds.
theorem drain_even (m A : ℕ) :
    ⟨A + m + 1, 0, 0, 0, 2 * m + 2⟩ [fm]⊢* ⟨A, 3 * m + 3, 0, 0, 0⟩ := by
  rw [show A + m + 1 = (A + m) + 1 from by ring,
      show 2 * m + 2 = (2 * m) + 2 from by ring]
  apply stepStar_trans (drain_first (A + m) (2 * m))
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 2 * m = 0 + 2 * m from by ring]
  apply stepStar_trans (drain_b1 m A 2 0)
  rw [show 2 + 3 * m + 1 = 3 * m + 3 from by ring]; finish

-- Full drain for odd e: leaves remainder e=1.
theorem drain_odd (m A : ℕ) :
    ⟨A + m + 1, 0, 0, 0, 2 * m + 3⟩ [fm]⊢* ⟨A, 3 * m + 3, 0, 0, 1⟩ := by
  rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show A + m + 1 = (A + m) + 1 from by ring,
      show 2 * m + 2 + 1 = (2 * m + 1) + 2 from by ring]
  apply stepStar_trans (drain_first (A + m) (2 * m + 1))
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (drain_b1 m A 2 1)
  rw [show 2 + 3 * m + 1 = 3 * m + 3 from by ring,
      show 0 + 1 = 1 from by ring]; finish

-- R3-R1-R1 single step.
theorem r3r1r1_step (a b d : ℕ) :
    ⟨a, b + 2, 0, d + 1, 0⟩ [fm]⊢* ⟨a + 2, b, 0, d + 2, 0⟩ := by
  step fm; step fm; step fm; finish

-- R3-R1-R1 chain: k cycles (b=0).
theorem r3r1r1_chain : ∀ k a d, ⟨a, 2 * k, 0, d + 1, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    apply stepStar_trans (r3r1r1_step a (2 * k) d)
    apply stepStar_trans (ih (a + 2) (d + 1))
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring,
        show d + 1 + k + 1 = d + (k + 1) + 1 from by ring]; finish

-- R3-R1-R1 chain: k cycles (general b).
theorem r3r1r1_chain_gen : ∀ k a b d, ⟨a, b + 2 * k, 0, d + 1, 0⟩ [fm]⊢* ⟨a + 2 * k, b, 0, d + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    apply stepStar_trans (r3r1r1_step a (b + 2 * k) d)
    apply stepStar_trans (ih (a + 2) b (d + 1))
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring,
        show d + 1 + k + 1 = d + (k + 1) + 1 from by ring]; finish

-- Phase 3 even B: R3-R1-R1 chain then R3 chain.
theorem phase3_Beven (A K : ℕ) :
    ⟨A, 2 * K, 0, 2, 0⟩ [fm]⊢* ⟨A + 4 * K + 4, 0, 2 * K + 4, 0, 0⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain K A 1)
  rw [show 1 + K + 1 = K + 2 from by ring]
  apply stepStar_trans (r3_chain (K + 2) (A + 2 * K) 0)
  ring_nf; finish

-- Phase 3 odd B: R3-R1-R1 chain, then R3-R1-R3, then R3 chain.
theorem phase3_Bodd (A K : ℕ) :
    ⟨A, 2 * K + 1, 0, 2, 0⟩ [fm]⊢* ⟨A + 4 * K + 6, 0, 2 * K + 5, 0, 0⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * K + 1 = 1 + 2 * K from by ring]
  apply stepStar_trans (r3r1r1_chain_gen K A 1 1)
  rw [show 1 + K + 1 = (K + 1) + 1 from by ring]
  step fm; step fm
  rw [show K + 2 = (K + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (r3_chain (K + 1) (A + 2 * K + 4) 3)
  ring_nf; finish

-- Phase 3 (e=0): R5-R1, then parity dispatch.
theorem phase3_e0 (A B : ℕ) :
    ⟨A + 1, B + 1, 0, 0, 0⟩ [fm]⊢⁺ ⟨A + 2 * B + 4, 0, B + 4, 0, 0⟩ := by
  step fm; step fm
  rcases Nat.even_or_odd B with ⟨K, hK⟩ | ⟨K, hK⟩
  · subst hK
    rw [show K + K = 2 * K from by ring]
    apply stepStar_trans (phase3_Beven A K)
    rw [show A + 2 * (2 * K) + 4 = A + 4 * K + 4 from by ring,
        show 2 * K + 4 = 2 * K + 4 from rfl]; finish
  · subst hK
    apply stepStar_trans (phase3_Bodd A K)
    rw [show A + 2 * (2 * K + 1) + 4 = A + 4 * K + 6 from by ring,
        show 2 * K + 1 + 4 = 2 * K + 5 from by ring]; finish

-- Phase 3 (e=1): R5-R1-R2-R3-R1-R1, then same as e=0 with A+2.
theorem phase3_e1 (A B : ℕ) :
    ⟨A + 1, B + 1, 0, 0, 1⟩ [fm]⊢⁺ ⟨A + 2 * B + 6, 0, B + 4, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm
  rcases Nat.even_or_odd B with ⟨K, hK⟩ | ⟨K, hK⟩
  · subst hK
    rw [show K + K = 2 * K from by ring]
    apply stepStar_trans (phase3_Beven (A + 2) K)
    rw [show A + 2 * (2 * K) + 6 = A + 2 + 4 * K + 4 from by ring,
        show 2 * K + 4 = 2 * K + 4 from rfl]; finish
  · subst hK
    apply stepStar_trans (phase3_Bodd (A + 2) K)
    rw [show A + 2 * (2 * K + 1) + 6 = A + 2 + 4 * K + 6 from by ring,
        show 2 * K + 1 + 4 = 2 * K + 5 from by ring]; finish

-- Even c transition: c_to_e, drain_even, phase3_e0.
theorem main_even (F m : ℕ) :
    ⟨F + m + 2, 0, 2 * m + 2, 0, 0⟩ [fm]⊢⁺ ⟨F + 6 * m + 8, 0, 3 * m + 6, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c_to_e (2 * m + 2) (F + m + 2) 0)
  rw [show 0 + (2 * m + 2) = 2 * m + 2 from by ring,
      show F + m + 2 = (F + 1) + m + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (drain_even m (F + 1))
  rw [show 3 * m + 3 = (3 * m + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phase3_e0 F (3 * m + 2))
  ring_nf; finish

-- Odd c transition: c_to_e, drain_odd, phase3_e1.
theorem main_odd (F m : ℕ) :
    ⟨F + m + 2, 0, 2 * m + 3, 0, 0⟩ [fm]⊢⁺ ⟨F + 6 * m + 10, 0, 3 * m + 6, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c_to_e (2 * m + 3) (F + m + 2) 0)
  rw [show 0 + (2 * m + 3) = 2 * m + 3 from by ring,
      show F + m + 2 = (F + 1) + m + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (drain_odd m (F + 1))
  rw [show 3 * m + 3 = (3 * m + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phase3_e1 F (3 * m + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 3, 0, 0⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ F c, q = ⟨F + c / 2 + 1, 0, c, 0, 0⟩ ∧ c ≥ 2)
  · intro q ⟨F, c, hq, hc⟩
    subst hq
    rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hm1 : m ≥ 1 := by omega
      obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm1
      subst hm
      have hd : (1 + m' + (1 + m')) / 2 = m' + 1 := by omega
      rw [hd]
      refine ⟨⟨F + 6 * m' + 8, 0, 3 * m' + 6, 0, 0⟩, ?_, ?_⟩
      · refine ⟨F + 6 * m' + 8 - (3 * m' + 6) / 2 - 1, 3 * m' + 6, ?_, by omega⟩
        congr 1; omega
      · rw [show F + (m' + 1) + 1 = F + m' + 2 from by ring,
            show 1 + m' + (1 + m') = 2 * m' + 2 from by ring]
        exact main_even F m'
    · have hm1 : m ≥ 1 := by omega
      obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm1
      subst hm
      have hd : (2 * (1 + m') + 1) / 2 = m' + 1 := by omega
      rw [hd]
      refine ⟨⟨F + 6 * m' + 10, 0, 3 * m' + 6, 0, 0⟩, ?_, ?_⟩
      · refine ⟨F + 6 * m' + 10 - (3 * m' + 6) / 2 - 1, 3 * m' + 6, ?_, by omega⟩
        congr 1; omega
      · rw [show F + (m' + 1) + 1 = F + m' + 2 from by ring,
            show 2 * (1 + m') + 1 = 2 * m' + 3 from by ring]
        exact main_odd F m'
  · exact ⟨0, 3, rfl, by omega⟩

end Sz22_2003_unofficial_1495
