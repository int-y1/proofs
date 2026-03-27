import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #169: [1/45, 686/5, 10/77, 3/7, 55/2]

Vector representation:
```
 0 -2 -1  0  0
 1  0 -1  3  0
 1  0  1 -1 -1
 0  1  0 -1  0
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_169

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+3, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- Phase 1: R5+R1 chain (even b).
theorem r5r1_chain_even : ∀ K a e,
    ⟨a + K, 2 * K, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + K⟩ := by
  intro K; induction' K with K ih <;> intro a e
  · exists 0
  · rw [show a + (K + 1) = (a + K) + 1 from by ring,
        show 2 * (K + 1) = 2 * K + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

-- Phase 1: R5+R1 chain (odd b).
theorem r5r1_chain_odd : ∀ K a e,
    ⟨a + K, 2 * K + 1, 0, 0, e⟩ [fm]⊢* ⟨a, 1, 0, 0, e + K⟩ := by
  intro K; induction' K with K ih <;> intro a e
  · exists 0
  · rw [show a + (K + 1) = (a + K) + 1 from by ring,
        show 2 * (K + 1) + 1 = 2 * K + 1 + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

-- Phase 2: R3+R2 chain (b=0).
theorem r3r2_chain_even : ∀ K a d e,
    ⟨a, 0, 0, d + 1, e + K⟩ [fm]⊢* ⟨a + 2 * K, 0, 0, d + 2 * K + 1, e⟩ := by
  intro K; induction' K with K ih <;> intro a d e
  · simp; exists 0
  · rw [show e + (K + 1) = (e + K) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 2) (d + 2) e)
    ring_nf; finish

-- Phase 2: R3+R2 chain (b=1).
theorem r3r2_chain_odd : ∀ K a d e,
    ⟨a, 1, 0, d + 1, e + K⟩ [fm]⊢* ⟨a + 2 * K, 1, 0, d + 2 * K + 1, e⟩ := by
  intro K; induction' K with K ih <;> intro a d e
  · simp; exists 0
  · rw [show e + (K + 1) = (e + K) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 2) (d + 2) e)
    ring_nf; finish

-- Phase 3: R4 chain.
theorem r4_chain : ∀ D a b,
    ⟨a, b, 0, D, 0⟩ [fm]⊢* ⟨a, b + D, 0, 0, 0⟩ := by
  intro D; induction' D with D ih <;> intro a b
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih a (b + 1))
    ring_nf; finish

-- Main transition (even b):
-- (a+K+1, 2*K, 0, 0, 0) ⊢⁺ (a+2*K+3, 2*K+5, 0, 0, 0)
theorem main_trans_even (a K : ℕ) :
    ⟨a + K + 1, 2 * K, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 2 * K + 3, 2 * K + 5, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a + 1, 0, 0, 0, K⟩)
  · have h := r5r1_chain_even K (a + 1) 0
    rw [show a + 1 + K = a + K + 1 from by ring, show 0 + K = K from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a + 1, 0, 0, 3, K + 1⟩)
  · step fm; step fm; ring_nf; finish
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a + 2 * K + 3, 0, 0, 2 * K + 5, 0⟩)
  · have h := r3r2_chain_even (K + 1) (a + 1) 2 0
    rw [show a + 1 + 2 * (K + 1) = a + 2 * K + 3 from by ring,
        show 2 + 2 * (K + 1) + 1 = 2 * K + 5 from by ring,
        show 0 + (K + 1) = K + 1 from by ring] at h; exact h
  have h := r4_chain (2 * K + 5) (a + 2 * K + 3) 0
  rw [show 0 + (2 * K + 5) = 2 * K + 5 from by ring] at h
  exact stepStar_stepPlus h (by simp [Q])

-- Main transition (odd b):
-- (a+K+1, 2*K+1, 0, 0, 0) ⊢⁺ (a+2*K+3, 2*K+6, 0, 0, 0)
theorem main_trans_odd (a K : ℕ) :
    ⟨a + K + 1, 2 * K + 1, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 2 * K + 3, 2 * K + 6, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a + 1, 1, 0, 0, K⟩)
  · have h := r5r1_chain_odd K (a + 1) 0
    rw [show a + 1 + K = a + K + 1 from by ring, show 0 + K = K from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a + 1, 1, 0, 3, K + 1⟩)
  · step fm; step fm; ring_nf; finish
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a + 2 * K + 3, 1, 0, 2 * K + 5, 0⟩)
  · have h := r3r2_chain_odd (K + 1) (a + 1) 2 0
    rw [show a + 1 + 2 * (K + 1) = a + 2 * K + 3 from by ring,
        show 2 + 2 * (K + 1) + 1 = 2 * K + 5 from by ring,
        show 0 + (K + 1) = K + 1 from by ring] at h; exact h
  have h := r4_chain (2 * K + 5) (a + 2 * K + 3) 1
  rw [show 1 + (2 * K + 5) = 2 * K + 6 from by ring] at h
  exact stepStar_stepPlus h (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 5, 0, 0, 0⟩)
  · execute fm 9
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a K, q = ⟨a + K + 1, 2 * K, 0, 0, 0⟩ ∨
                          (q = ⟨a + K + 1, 2 * K + 1, 0, 0, 0⟩ ∧ a + K ≥ 1))
  · intro q ⟨a, K, hq⟩
    rcases hq with hq | ⟨hq, hak⟩
    · exact ⟨⟨a + 2 * K + 3, 2 * K + 5, 0, 0, 0⟩,
             ⟨a + K, K + 2, Or.inr ⟨by ring_nf, by omega⟩⟩,
             hq ▸ main_trans_even a K⟩
    · have ⟨m, hm⟩ : ∃ m, a + K = m + 1 := ⟨a + K - 1, by omega⟩
      exact ⟨⟨a + 2 * K + 3, 2 * K + 6, 0, 0, 0⟩,
             ⟨m, K + 3, Or.inl (by rw [show m + (K + 3) + 1 = a + 2 * K + 3 from by omega,
                                        show 2 * (K + 3) = 2 * K + 6 from by ring])⟩,
             hq ▸ main_trans_odd a K⟩
  · exact ⟨0, 2, Or.inr ⟨by ring_nf, by omega⟩⟩

end Sz22_2003_unofficial_169
