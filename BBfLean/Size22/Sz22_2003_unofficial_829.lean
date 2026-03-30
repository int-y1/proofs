import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #829: [35/6, 8/55, 77/2, 3/7, 5/3]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  0 -1
-1  0  0  1  1
 0  1  0 -1  0
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_829

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: (0, b, 0, d+k, e) →* (0, b+k, 0, d, e)
theorem r4_chain : ∀ k, ∀ b d, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = d + k + 1 from by ring]; step fm
    apply stepStar_trans (ih (b + 1) d); ring_nf; finish

-- R3 chain: (a+k, 0, 0, d, e) →* (a, 0, 0, d+k, e+k)
theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]; step fm
    apply stepStar_trans (ih a (d + 1) (e + 1)); ring_nf; finish

-- R2+R3 drain: (a+1, 0, C, d, e) →* (0, 0, 0, d+a+1+3*C, a+1+2*C+e)
theorem r2_r3_drain : ∀ C, ∀ a d e,
    ⟨a + 1, 0, C, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + a + 1 + 3 * C, a + 1 + 2 * C + e⟩ := by
  intro C; induction' C with C ih <;> intro a d e
  · rw [show a + 1 = 0 + (a + 1) from by ring]
    apply stepStar_trans (r3_chain (a + 1) 0 d e); ring_nf; finish
  · rcases e with _ | e'
    · step fm; step fm
      rw [show a + 3 = (a + 2) + 1 from by ring]
      apply stepStar_trans (ih (a + 2) (d + 1) 0); ring_nf; finish
    · step fm
      rw [show a + 1 + 3 = (a + 3) + 1 from by ring]
      apply stepStar_trans (ih (a + 3) d e'); ring_nf; finish

-- Interleaved R1x3 + R2 loop
theorem interleaved_loop : ∀ k, ∀ b E,
    ⟨3, b + 3 * k, 0, 0, E + k⟩ [fm]⊢* ⟨3, b, 2 * k, 3 * k, E⟩ := by
  intro k; induction' k with k ih <;> intro b E
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    apply stepStar_trans (ih (b + 3) (E + 1))
    step fm; step fm; step fm; step fm
    ring_nf; finish

-- r=0 tail: ⟨3, 0, 2*K, 3*K, E⟩ →* ⟨0, 0, 0, 9*K+3, 4*K+E+3⟩
theorem tail_r0 (K E : ℕ) :
    ⟨3, 0, 2 * K, 3 * K, E⟩ [fm]⊢* ⟨0, 0, 0, 9 * K + 3, 4 * K + E + 3⟩ := by
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r2_r3_drain (2 * K) 2 (3 * K) E)
  ring_nf; finish

-- r=1 tail: ⟨3, 1, 2*K, 3*K, E⟩ →* ⟨0, 0, 0, 9*K+6, 4*K+E+4⟩
theorem tail_r1 (K E : ℕ) :
    ⟨3, 1, 2 * K, 3 * K, E⟩ [fm]⊢* ⟨0, 0, 0, 9 * K + 6, 4 * K + E + 4⟩ := by
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r2_r3_drain (2 * K + 1) 1 (3 * K + 1) E)
  ring_nf; finish

-- r=2 tail: ⟨3, 2, 2*K, 3*K, E⟩ →* ⟨0, 0, 0, 9*K+9, 4*K+E+5⟩
theorem tail_r2 (K E : ℕ) :
    ⟨3, 2, 2 * K, 3 * K, E⟩ [fm]⊢* ⟨0, 0, 0, 9 * K + 9, 4 * K + E + 5⟩ := by
  step fm; step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r2_r3_drain (2 * K + 2) 0 (3 * K + 2) E)
  ring_nf; finish

-- Full inner phase: ⟨3, r + 3*K, 0, 0, E + K⟩ →* ⟨0, 0, 0, 9*K+3*r+3, 4*K+r+E+3⟩
theorem inner_phase_aux (K r E : ℕ) (hr : r ≤ 2) :
    ⟨3, r + 3 * K, 0, 0, E + K⟩ [fm]⊢* ⟨0, 0, 0, 9 * K + 3 * r + 3, 4 * K + r + E + 3⟩ := by
  apply stepStar_trans (interleaved_loop K r E)
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 from by omega) with rfl | rfl | rfl
  · apply stepStar_trans (tail_r0 K E); ring_nf; finish
  · apply stepStar_trans (tail_r1 K E); ring_nf; finish
  · apply stepStar_trans (tail_r2 K E); ring_nf; finish

-- R5+R2 start: (0, b+1, 0, 0, e+1) →⁺ (3, b, 0, 0, e)
theorem r5_r2 (b e : ℕ) : ⟨0, b + 1, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨3, b, 0, 0, e⟩ := by
  step fm; step fm; finish

-- Full transition (parametrized by K, r, E directly)
theorem main_transition_aux (K r E : ℕ) (hr : r ≤ 2) :
    ⟨0, 0, 0, r + 3 * K + 1, E + K + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 9 * K + 3 * r + 3, 4 * K + r + E + 3⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show r + 3 * K + 1 = 0 + (r + 3 * K + 1) from by ring]
    exact r4_chain (r + 3 * K + 1) 0 0
  apply stepPlus_stepStar_stepPlus
  · rw [show (0 : ℕ) + (r + 3 * K + 1) = (r + 3 * K) + 1 from by ring]
    exact r5_r2 (r + 3 * K) (E + K)
  exact inner_phase_aux K r E hr

-- Main transition in terms of d and e
theorem main_transition (d e : ℕ) (h : d / 3 ≤ e) :
    ⟨0, 0, 0, d + 1, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * d + 3, d + e + 3⟩ := by
  have hK : d / 3 ≤ e := h
  have hr : d % 3 ≤ 2 := by omega
  rw [show d + 1 = d % 3 + 3 * (d / 3) + 1 from by omega,
      show e + 1 = (e - d / 3) + (d / 3) + 1 from by omega,
      show 3 * d + 3 = 9 * (d / 3) + 3 * (d % 3) + 3 from by omega,
      show d + e + 3 = 4 * (d / 3) + d % 3 + (e - d / 3) + 3 from by omega]
  exact main_transition_aux (d / 3) (d % 3) (e - d / 3) hr

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e + 1⟩ ∧ d / 3 ≤ e)
  · intro c ⟨d, e, hq, hde⟩; subst hq
    exact ⟨⟨0, 0, 0, 3 * d + 3, d + e + 3⟩,
      ⟨3 * d + 2, d + e + 2, rfl, by omega⟩,
      main_transition d e hde⟩
  · exact ⟨0, 0, rfl, by omega⟩
