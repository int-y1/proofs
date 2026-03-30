import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1081: [5/6, 196/55, 847/2, 3/7, 2/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1  2 -1
-1  0  0  1  2
 0  1  0 -1  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1081

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 repeated: move d to b (a=0, c=0).
theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (b := b + 1)); ring_nf; finish

-- R3 repeated: drain a (b=0, c=0).
theorem a_drain : ∀ k, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1) (e := e + 2)); ring_nf; finish

-- Interleaved R2+R1+R1 chain.
theorem interleaved_chain :
    ∀ k, ⟨0, b + 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, b, c + 1 + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · simp; exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (b := b) (c := c + 1) (d := d + 2) (e := e))
    ring_nf; finish

-- Combined c-drain and a-drain.
theorem combined_drain :
    ∀ C, ∀ p q E, ⟨p + 1, (0 : ℕ), C, q, E⟩ [fm]⊢*
      ⟨0, 0, 0, q + p + 4 * C + 1, 2 * p + 3 * C + E + 2⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih
  intro p q E
  rcases C with _ | C
  · apply stepStar_trans (a_drain (p + 1) (d := q) (e := E))
    ring_nf; finish
  · rcases E with _ | E
    · rcases C with _ | C
      · step fm; step fm
        apply stepStar_trans (ih 0 (by omega) (p + 1) (q + 3) 1)
        ring_nf; finish
      · step fm; step fm; step fm
        apply stepStar_trans (ih C (by omega) (p + 3) (q + 5) 0)
        ring_nf; finish
    · step fm
      apply stepStar_trans (ih C (by omega) (p + 2) (q + 2) E)
      ring_nf; finish

-- Transition for D=1.
theorem trans_d1 : ⟨0, 0, 0, 1, e + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4, e + 4⟩ := by
  step fm; step fm; step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (combined_drain 0 1 2 e)
  ring_nf; finish

-- Opening phase: d_to_b + R5 + R1 for D = B+1.
-- (0, 0, 0, B+1, E) ->* (0, B+1, 0, 0, E) -> (1, B+1, 0, 0, E-1) -> (0, B, 1, 0, E-1)
-- But step fm sees R5 pattern on (0, B+1, 0, 0, E).
-- R1: a+1=0 fails. R2: c+1=0 fails. R3: a+1=0 fails. R4: d+1=0 fails. R5: e+1. Needs E >= 1.
-- Actually (0, B+1, 0, 0, E): R4 needs d+1 matches but d=0. R5: e+1 needs E >= 1.
-- Hmm, but (0, B+1, 0, 0, E) = (a, b, c, d, e) with a=0, b=B+1, c=0, d=0, e=E.
-- Check rules: R1: a+1=1? a=0, no. R2: c+1=1? c=0, no. R3: a+1=1? no. R4: d+1=1? d=0, no.
-- R5: e+1? Only if E >= 1. (0, B+1, 0, 0, E+1) -> R5: (1, B+1, 0, 0, E).
-- Then (1, B+1, 0, 0, E): R1: a+1=2? a=1>=1, b+1=B+2? b=B+1>=1. Yes! R1 fires.
-- R1: (0, B, 1, 0, E).

-- For transition lemmas, let me build the full thing without breaking into d_to_b + R5 + R1.
-- Instead: use d_to_b to get (0, B+1, 0, 0, E+1), then step fm (R5), step fm (R1).

-- Transition for D even (D = 2m+2, m >= 0).
-- (0,0,0, 2m+2, e+m+2) ⊢⁺ (0,0,0, 6m+7, e+3m+5)
theorem trans_even :
    ⟨0, 0, 0, 2 * m + 2, e + m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * m + 7, e + 3 * m + 5⟩ := by
  -- Phase 1: d_to_b
  rw [show (2 * m + 2 : ℕ) = 0 + (2 * m + 2) from by ring,
      show e + m + 2 = (e + m + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2 * m + 2) (b := 0) (d := 0) (e := (e + m + 1) + 1))
  rw [show (0 : ℕ) + (2 * m + 2) = (2 * m + 1) + 1 from by ring]
  -- State: (0, (2m+1)+1, 0, 0, (e+m+1)+1). R5 fires.
  step fm -- R5: (1, (2m+1)+1, 0, 0, e+m+1)
  -- State: (1, (2m+1)+1, 0, 0, e+m+1). R1 fires (a=1>=1, b=(2m+1)+1>=1).
  step fm -- R1: (0, 2m+1, 1, 0, e+m+1)
  -- Now rewrite for interleaved_chain
  rw [show (2 * m + 1 : ℕ) = 1 + 2 * m from by ring,
      show e + m + 1 = (e + 1) + m from by ring]
  apply stepStar_trans (interleaved_chain m (b := 1) (c := 0) (d := 0) (e := e + 1))
  rw [show (0 : ℕ) + 1 + m = m + 1 from by ring,
      show (0 : ℕ) + 2 * m = 2 * m from by ring]
  -- State: (0, 1, m+1, 2m, e+1). R2 fires (c=m+1>=1, e=e+1>=1).
  rw [show (e + 1 : ℕ) = e + 1 from by ring]
  step fm -- R2: (2, 1, m, 2m+2, e)
  -- State: (2, 1, m, 2m+2, e). R1 fires (a=2>=1, b=1>=1).
  step fm -- R1: (1, 0, m+1, 2m+2, e)
  -- Now apply combined_drain
  apply stepStar_trans (combined_drain (m + 1) 0 (2 * m + 2) e)
  ring_nf; finish

-- Transition for D odd >= 3 (D = 2m+3, m >= 0).
-- (0,0,0, 2m+3, e+m+3) ⊢⁺ (0,0,0, 6m+10, e+3m+7)
theorem trans_odd :
    ⟨0, 0, 0, 2 * m + 3, e + m + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * m + 10, e + 3 * m + 7⟩ := by
  rw [show (2 * m + 3 : ℕ) = 0 + (2 * m + 3) from by ring,
      show e + m + 3 = (e + m + 2) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2 * m + 3) (b := 0) (d := 0) (e := (e + m + 2) + 1))
  rw [show (0 : ℕ) + (2 * m + 3) = (2 * (m + 1)) + 1 from by ring]
  step fm -- R5
  step fm -- R1
  rw [show (2 * (m + 1) : ℕ) = 0 + 2 * (m + 1) from by ring,
      show e + m + 2 = (e + 1) + (m + 1) from by ring]
  apply stepStar_trans (interleaved_chain (m + 1) (b := 0) (c := 0) (d := 0) (e := e + 1))
  rw [show (0 : ℕ) + 1 + (m + 1) = m + 2 from by ring,
      show (0 : ℕ) + 2 * (m + 1) = 2 * m + 2 from by ring]
  -- State: (0, 0, m+2, 2m+2, e+1). R2 fires.
  rw [show (e + 1 : ℕ) = e + 1 from by ring]
  step fm -- R2: (2, 0, m+1, 2m+4, e)
  -- Now apply combined_drain
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (combined_drain (m + 1) 1 (2 * m + 4) e)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e⟩ ∧ 2 * e ≥ d + 3)
  · intro c ⟨d, e, hq, he⟩; subst hq
    rcases d with _ | d
    · obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 := ⟨e - 2, by omega⟩
      exact ⟨⟨0, 0, 0, 4, f + 4⟩, ⟨3, f + 4, rfl, by omega⟩, trans_d1⟩
    · rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- d even: d = 2m, D = d+2 = 2m+2 (even D), use trans_even
        obtain ⟨f, rfl⟩ : ∃ f, e = f + m + 2 := ⟨e - m - 2, by omega⟩
        refine ⟨⟨0, 0, 0, 6 * m + 7, f + 3 * m + 5⟩,
          ⟨6 * m + 6, f + 3 * m + 5, rfl, by omega⟩, ?_⟩
        have h1 : (⟨0, 0, 0, d + 1 + 1, f + m + 2⟩ : Q) =
                   ⟨0, 0, 0, 2 * m + 2, f + m + 2⟩ := by subst hm; ring_nf
        rw [h1]; exact trans_even
      · -- d odd: d = 2m+1, D = d+2 = 2m+3 (odd D), use trans_odd
        obtain ⟨f, rfl⟩ : ∃ f, e = f + m + 3 := ⟨e - m - 3, by omega⟩
        refine ⟨⟨0, 0, 0, 6 * m + 10, f + 3 * m + 7⟩,
          ⟨6 * m + 9, f + 3 * m + 7, rfl, by omega⟩, ?_⟩
        have h1 : (⟨0, 0, 0, d + 1 + 1, f + m + 3⟩ : Q) =
                   ⟨0, 0, 0, 2 * m + 3, f + m + 3⟩ := by subst hm; ring_nf
        rw [h1]; exact trans_odd
  · exact ⟨0, 2, rfl, by omega⟩

end Sz22_2003_unofficial_1081
