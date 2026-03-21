import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #136: [9/35, 1/363, 50/3, 11/5, 21/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  0  0 -2
 1 -1  2  0  0
 0  0 -1  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_136

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+2⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- Phase 1 even: (a+k, 0, 0, d, 2k) →* (a, 0, 0, d+k, 0)
theorem r5r2_even : ∀ k, ∀ a d, ⟨a+k, 0, 0, d, 2*k⟩ [fm]⊢* ⟨a, 0, 0, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih a (d + 1))
  ring_nf; finish

-- Phase 1 odd: (a+k, 0, 0, d, 2k+1) →* (a, 0, 0, d+k, 1)
theorem r5r2_odd : ∀ k, ∀ a d, ⟨a+k, 0, 0, d, 2*k+1⟩ [fm]⊢* ⟨a, 0, 0, d+k, 1⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih a (d + 1))
  ring_nf; finish

-- R1R1R3 rounds with e=0
theorem r1r1r3_e0 : ∀ k, ∀ a b d, ⟨a, b, 2, d+2*k, 0⟩ [fm]⊢* ⟨a+k, b+3*k, 2, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 1 + 1 from by ring]
  step fm; rw [show (d + 2 * k) + 1 = d + 2 * k + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (ih (a + 1) (b + 3) d)
  ring_nf; finish

-- R1R1R3 rounds with e=1
theorem r1r1r3_e1 : ∀ k, ∀ a b d, ⟨a, b, 2, d+2*k, 1⟩ [fm]⊢* ⟨a+k, b+3*k, 2, d, 1⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 1 + 1 from by ring]
  step fm; rw [show (d + 2 * k) + 1 = d + 2 * k + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (ih (a + 1) (b + 3) d)
  ring_nf; finish

-- R3 chain with e=0
theorem r3_chain_e0 : ∀ k, ∀ a c, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a+k, 0, c+2*k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  step fm
  apply stepStar_trans (ih (a + 1) (c + 2))
  ring_nf; finish

-- R3 chain with e=1
theorem r3_chain_e1 : ∀ k, ∀ a c, ⟨a, k, c, 0, 1⟩ [fm]⊢* ⟨a+k, 0, c+2*k, 0, 1⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  step fm
  apply stepStar_trans (ih (a + 1) (c + 2))
  ring_nf; finish

-- R4 chain: c → e
theorem r4_chain : ∀ k, ∀ a e, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  step fm
  apply stepStar_trans (ih a (e + 1))
  ring_nf; finish

-- D even, e=0
theorem phase234_e0_even (K : ℕ) : ∀ a, ⟨a+1, 0, 0, 2*K, 0⟩ [fm]⊢⁺ ⟨a+4*K+3, 0, 0, 0, 6*K+5⟩ := by
  intro a
  step fm; step fm
  rw [show 2 * K + 1 = 1 + 2 * K from by ring]
  refine stepStar_trans (r1r1r3_e0 K (a + 1) 0 1) ?_
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm
  refine stepStar_trans (r3_chain_e0 (0 + 3 * K + 1) (a + 1 + K + 1) 3) ?_
  refine stepStar_trans (r4_chain (3 + 2 * (0 + 3 * K + 1)) (a + 1 + K + 1 + (0 + 3 * K + 1)) 0) ?_
  ring_nf; finish

-- D odd, e=0
theorem phase234_e0_odd (K : ℕ) : ∀ a, ⟨a+1, 0, 0, 2*K+1, 0⟩ [fm]⊢⁺ ⟨a+4*K+5, 0, 0, 0, 6*K+8⟩ := by
  intro a
  step fm; step fm
  rw [show 2 * K + 1 + 1 = 0 + 2 * (K + 1) from by ring]
  refine stepStar_trans (r1r1r3_e0 (K + 1) (a + 1) 0 0) ?_
  refine stepStar_trans (r3_chain_e0 (0 + 3 * (K + 1)) (a + 1 + (K + 1)) 2) ?_
  refine stepStar_trans (r4_chain (2 + 2 * (0 + 3 * (K + 1))) (a + 1 + (K + 1) + (0 + 3 * (K + 1))) 0) ?_
  ring_nf; finish

-- D even, e=1
theorem phase234_e1_even (K : ℕ) : ∀ a, ⟨a+1, 0, 0, 2*K, 1⟩ [fm]⊢⁺ ⟨a+4*K+3, 0, 0, 0, 6*K+6⟩ := by
  intro a
  step fm; step fm
  rw [show 2 * K + 1 = 1 + 2 * K from by ring]
  refine stepStar_trans (r1r1r3_e1 K (a + 1) 0 1) ?_
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm
  refine stepStar_trans (r3_chain_e1 (0 + 3 * K + 1) (a + 1 + K + 1) 3) ?_
  refine stepStar_trans (r4_chain (3 + 2 * (0 + 3 * K + 1)) (a + 1 + K + 1 + (0 + 3 * K + 1)) 1) ?_
  ring_nf; finish

-- D odd, e=1
theorem phase234_e1_odd (K : ℕ) : ∀ a, ⟨a+1, 0, 0, 2*K+1, 1⟩ [fm]⊢⁺ ⟨a+4*K+5, 0, 0, 0, 6*K+9⟩ := by
  intro a
  step fm; step fm
  rw [show 2 * K + 1 + 1 = 0 + 2 * (K + 1) from by ring]
  refine stepStar_trans (r1r1r3_e1 (K + 1) (a + 1) 0 0) ?_
  refine stepStar_trans (r3_chain_e1 (0 + 3 * (K + 1)) (a + 1 + (K + 1)) 2) ?_
  refine stepStar_trans (r4_chain (2 + 2 * (0 + 3 * (K + 1))) (a + 1 + (K + 1) + (0 + 3 * (K + 1))) 1) ?_
  ring_nf; finish

-- Main even: e=2E
theorem main_even (E : ℕ) (hE : E ≥ 1) (a : ℕ) (ha : a ≥ E + 1) :
    ⟨a, 0, 0, 0, 2*E⟩ [fm]⊢⁺ ⟨a+E+2, 0, 0, 0, 3*E+5⟩ := by
  obtain ⟨A, rfl⟩ : ∃ A, a = A + (E + 1) := ⟨a - (E + 1), by omega⟩
  rw [show A + (E + 1) = (A + 1) + E from by ring]
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨A + 1, 0, 0, E, 0⟩)
  · refine stepStar_trans (r5r2_even E (A + 1) 0) ?_; ring_nf; finish
  rcases Nat.even_or_odd E with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK; subst hK
    rw [show A + 1 + 2 * K + (2 * K) + 2 = A + 4 * K + 3 from by ring,
        show 3 * (2 * K) + 5 = 6 * K + 5 from by ring]
    exact phase234_e0_even K A
  · subst hK
    rw [show A + 1 + (2 * K + 1) + (2 * K + 1) + 2 = A + 4 * K + 5 from by ring,
        show 3 * (2 * K + 1) + 5 = 6 * K + 8 from by ring]
    exact phase234_e0_odd K A

-- Main odd: e=2E+1
theorem main_odd (E : ℕ) (hE : E ≥ 1) (a : ℕ) (ha : a ≥ E + 1) :
    ⟨a, 0, 0, 0, 2*E+1⟩ [fm]⊢⁺ ⟨a+E+2, 0, 0, 0, 3*E+6⟩ := by
  obtain ⟨A, rfl⟩ : ∃ A, a = A + (E + 1) := ⟨a - (E + 1), by omega⟩
  rw [show A + (E + 1) = (A + 1) + E from by ring]
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨A + 1, 0, 0, E, 1⟩)
  · refine stepStar_trans (r5r2_odd E (A + 1) 0) ?_; ring_nf; finish
  rcases Nat.even_or_odd E with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK; subst hK
    rw [show A + 1 + 2 * K + (2 * K) + 2 = A + 4 * K + 3 from by ring,
        show 3 * (2 * K) + 6 = 6 * K + 6 from by ring]
    exact phase234_e1_even K A
  · subst hK
    rw [show A + 1 + (2 * K + 1) + (2 * K + 1) + 2 = A + 4 * K + 5 from by ring,
        show 3 * (2 * K + 1) + 6 = 6 * K + 9 from by ring]
    exact phase234_e1_odd K A

theorem main_trans (a e : ℕ) (h1 : 2 * a ≥ e + 1) (h2 : e ≥ 2) :
    ∃ a' e', (⟨a, 0, 0, 0, e⟩ : Q) [fm]⊢⁺ ⟨a', 0, 0, 0, e'⟩ ∧ 2 * a' ≥ e' + 1 ∧ e' ≥ 2 := by
  rcases Nat.even_or_odd e with ⟨E, hE⟩ | ⟨E, hE⟩
  · rw [show E + E = 2 * E from by ring] at hE; subst hE
    have hE1 : E ≥ 1 := by omega
    have ha : a ≥ E + 1 := by omega
    exact ⟨a + E + 2, 3 * E + 5, main_even E hE1 a ha, by omega, by omega⟩
  · subst hE
    have hE1 : E ≥ 1 := by omega
    have ha : a ≥ E + 1 := by omega
    exact ⟨a + E + 2, 3 * E + 6, main_odd E hE1 a ha, by omega, by omega⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 5⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ 2 * a ≥ e + 1 ∧ e ≥ 2)
  · intro c ⟨a, e, hq, h1, h2⟩
    subst hq
    obtain ⟨a', e', htrans, h1', h2'⟩ := main_trans a e h1 h2
    exact ⟨⟨a', 0, 0, 0, e'⟩, ⟨a', e', rfl, h1', h2'⟩, htrans⟩
  · exact ⟨3, 5, rfl, by omega, by omega⟩
