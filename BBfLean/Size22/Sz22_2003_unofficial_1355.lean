import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1355: [63/10, 4/33, 11/2, 5/7, 42/11]

Vector representation:
```
-1  2 -1  1  0
 2 -1  0  0 -1
-1  0  0  0  1
 0  0  1 -1  0
 1  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1355

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d+1, e⟩
  | _ => none

-- R4: transfer d to c
theorem d_to_c : ∀ k c e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

-- R3: transfer a to e (when b=0, c=0)
theorem a_to_e : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- Drain with a >= 1: (a+1, b, 0, d, e) ⊢* (0, 0, 0, d, a+1+b+e)
-- Induction on b, with case split on e in the step case.
theorem drain_a1 : ∀ b a d e, ⟨a + 1, b, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, a + 1 + b + e⟩ := by
  intro b; induction' b with b ih <;> intro a d e
  · apply stepStar_trans (a_to_e (a + 1) d e)
    ring_nf; finish
  · rcases e with _ | e
    · -- e=0: R3 fires (a+1>=1, and R2 needs e>=1 which fails)
      step fm; step fm
      apply stepStar_trans (ih (a + 1) d 0)
      ring_nf; finish
    · -- e>=1: R2 fires (b+1>=1 and e+1>=1, priority over R3)
      step fm
      apply stepStar_trans (ih (a + 2) d e)
      ring_nf; finish

-- Even interleave chain: consumes 2k from c using k rounds of R2,R1,R1.
-- (0, b+1, 2k, d, e+k+1) ⊢* (0, 0, 0, d+2k, b+3k+e+2)
theorem interleave_even : ∀ k b d e,
    ⟨0, b + 1, 2 * k, d, e + k + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, b + 3 * k + e + 2⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · -- k=0: (0, b+1, 0, d, e+1). R2 fires.
    step fm
    apply stepStar_trans (drain_a1 b 1 d e)
    ring_nf; finish
  · -- k+1: (0, b+1, 2k+2, d, e+k+2). R2, R1, R1 then IH.
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    show ⟨0, b + 3 + 1, 2 * k, d + 2, e + k + 1⟩ [fm]⊢* _
    apply stepStar_trans (ih (b + 3) (d + 2) e)
    ring_nf; finish

-- Odd interleave chain: consumes 2k+1 from c.
-- (0, b+1, 2k+1, d, e+k+1) ⊢* (0, 0, 0, d+2k+1, b+3k+e+3)
theorem interleave_odd : ∀ k b d e,
    ⟨0, b + 1, 2 * k + 1, d, e + k + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k + 1, b + 3 * k + e + 3⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · -- k=0: (0, b+1, 1, d, e+1). R2, R1, then drain_a1.
    step fm; step fm
    apply stepStar_trans (drain_a1 (b + 2) 0 (d + 1) e)
    ring_nf; finish
  · -- k+1: (0, b+1, 2k+3, d, e+k+2). R2, R1, R1 then IH.
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    show ⟨0, b + 3 + 1, 2 * k + 1, d + 2, e + k + 1⟩ [fm]⊢* _
    apply stepStar_trans (ih (b + 3) (d + 2) e)
    ring_nf; finish

-- Main transition for even n (n=2k): (0, 0, 2k+1, 0, e+k+2) ⊢⁺ (0, 0, 2k+2, 0, e+3k+4)
theorem main_even (k e : ℕ) :
    ⟨0, 0, 2 * k + 1, 0, e + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * k + 2, 0, e + 3 * k + 4⟩ := by
  -- R5, R1: (0,0,2k+1,0,e+k+2) -> (1,1,2k+1,1,e+k+1) -> (0,3,2k,2,e+k+1)
  step fm; step fm
  -- (0, 3, 2k, 2, e+k+1) = (0, 2+1, 2k, 2, e+k+1)
  apply stepStar_trans (interleave_even k 2 2 e)
  rw [show 2 + 2 * k = 0 + (2 * k + 2) from by ring]
  apply stepStar_trans (d_to_c (2 * k + 2) 0 (2 + 3 * k + e + 2) (d := 0))
  ring_nf; finish

-- Main transition for odd n (n=2k+1): (0, 0, 2k+2, 0, e+k+2) ⊢⁺ (0, 0, 2k+3, 0, e+3k+5)
theorem main_odd (k e : ℕ) :
    ⟨0, 0, 2 * k + 2, 0, e + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * k + 3, 0, e + 3 * k + 5⟩ := by
  -- R5, R1: (0,0,2k+2,0,e+k+2) -> (1,1,2k+2,1,e+k+1) -> (0,3,2k+1,2,e+k+1)
  step fm; step fm
  -- (0, 3, 2k+1, 2, e+k+1) = (0, 2+1, 2k+1, 2, e+k+1)
  apply stepStar_trans (interleave_odd k 2 2 e)
  rw [show 2 + 2 * k + 1 = 0 + (2 * k + 3) from by ring]
  apply stepStar_trans (d_to_c (2 * k + 3) 0 (2 + 3 * k + e + 3) (d := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c, 0, e⟩ ∧ c ≥ 1 ∧ 2 * e ≥ c + 3)
  · intro q ⟨c, e, hq, hc, he⟩; subst hq
    rcases Nat.even_or_odd c with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- c even: c = 2K, K ≥ 1
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + (k + 2) := ⟨e - (k + 2), by omega⟩
      refine ⟨⟨0, 0, 2 * k + 3, 0, e' + 3 * k + 5⟩,
        ⟨2 * k + 3, e' + 3 * k + 5, rfl, by omega, by omega⟩, ?_⟩
      exact main_odd k e'
    · -- c odd: c = 2K + 1
      subst hK
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + (K + 2) := ⟨e - (K + 2), by omega⟩
      refine ⟨⟨0, 0, 2 * K + 2, 0, e' + 3 * K + 4⟩,
        ⟨2 * K + 2, e' + 3 * K + 4, rfl, by omega, by omega⟩, ?_⟩
      exact main_even K e'
  · exact ⟨1, 2, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1355
