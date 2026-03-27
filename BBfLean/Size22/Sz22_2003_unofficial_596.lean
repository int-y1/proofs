import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #596: [35/6, 121/2, 4/55, 3/7, 12/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 2  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_596

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R3,R2,R2 repeated: drain c while increasing e
theorem drain : ∀ k c e, ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+3*k+1⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show e + 2 + 2 = (e + 3) + 1 from by ring]
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1,R1,R3 chain: mixing phase
theorem r1r1r3_chain : ∀ k c d, ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Even case: n=2*m, increase = 2*m+4
theorem even_trans (m : ℕ) : ⟨0, 0, 0, 2*m, e+m+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+1, e+3*m+5⟩ := by
  -- Phase 1: R4 chain
  rw [show (2:ℕ)*m = 0 + 2*m from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (d := 0) (e := e+m+1) (2*m) 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5
  step fm
  -- Phase 3: R1,R1,R3 chain
  rw [show (2:ℕ)*m+1 = 1 + 2*m from by ring]
  apply stepStar_trans (r1r1r3_chain (b := 1) (e := e) m 0 0)
  simp only [Nat.zero_add]
  -- Phase 4: R1,R2
  step fm; step fm
  -- Phase 5: drain
  rw [show m + 1 = 0 + (m + 1) from by ring,
      show e + 2 = (e + 1) + 1 from by ring]
  apply stepStar_trans (drain (d := 2*m+1) (m+1) 0 (e+1))
  ring_nf; finish

-- Odd case: n=2*m+1, increase = 2*m+5
theorem odd_trans (m : ℕ) : ⟨0, 0, 0, 2*m+1, e+m+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+2, e+3*m+7⟩ := by
  -- Phase 1: R4 chain
  rw [show (2:ℕ)*m+1 = 0 + (2*m+1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (d := 0) (e := e+m+2) (2*m+1) 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5
  step fm
  -- Phase 3: R1,R1,R3 chain
  rw [show (2:ℕ)*m+2 = 2 + 2*m from by ring,
      show e + m + 1 = e + 1 + m from by ring]
  apply stepStar_trans (r1r1r3_chain (b := 2) (e := e+1) m 0 0)
  simp only [Nat.zero_add]
  -- Phase 4: R1,R1
  step fm; step fm
  -- Phase 5: drain
  rw [show m + 2 = 0 + (m + 2) from by ring]
  apply stepStar_trans (drain (d := 2*m+2) (m+2) 0 e)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n e, q = ⟨0, 0, 0, n, e⟩ ∧ e ≥ n + 2)
  · intro c ⟨n, e, hq, he⟩; subst hq
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + m + 1 := ⟨e - m - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 2*m+1, e'+3*m+5⟩,
        ⟨2*m+1, e'+3*m+5, rfl, by omega⟩, even_trans m⟩
    · rw [show 2 * m + 1 = 2 * m + 1 from rfl] at hm; subst hm
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + m + 2 := ⟨e - m - 2, by omega⟩
      exact ⟨⟨0, 0, 0, 2*m+2, e'+3*m+7⟩,
        ⟨2*m+2, e'+3*m+7, rfl, by omega⟩, odd_trans m⟩
  · exact ⟨0, 2, rfl, by omega⟩
