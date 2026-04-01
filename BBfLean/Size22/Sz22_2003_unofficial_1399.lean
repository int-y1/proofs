import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1399: [7/15, 1/3, 1/847, 78/7, 55/13, 7/2]

Vector representation:
```
 0 -1 -1  1  0  0
 0 -1  0  0  0  0
 0  0  0 -1 -2  0
 1  1  0 -1  0  1
 0  0  1  0  1 -1
-1  0  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1399

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e+2, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a+1, b+1, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | _ => none

-- R5 chain: transfer f to c and e (generalized).
theorem r5_chain : ∀ k c e, ⟨a, (0 : ℕ), c, 0, e, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) (e + 1)); ring_nf; finish

-- Specialized R5 (e=0).
theorem r5_e0 (k : ℕ) : ⟨a, (0 : ℕ), 0, 0, 0, k⟩ [fm]⊢* ⟨a, 0, k, 0, k, 0⟩ := by
  have := r5_chain k 0 0 (a := a)
  simp only [Nat.zero_add] at this; exact this

-- Specialized R5 (e=1).
theorem r5_e1 (k : ℕ) : ⟨a, (0 : ℕ), 0, 0, 1, k⟩ [fm]⊢* ⟨a, 0, k, 0, k + 1, 0⟩ := by
  have := r5_chain k 0 1 (a := a)
  simp only [Nat.zero_add] at this
  rw [show 1 + k = k + 1 from by ring] at this; exact this

-- R6/R3 drain (e=0): reduce e by pairs of 2.
theorem r6r3_drain_e0 : ∀ k a, ⟨a + k, (0 : ℕ), c, 0, 2 * k, 0⟩ [fm]⊢*
    ⟨a, 0, c, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm
    exact ih a

-- R6/R3 drain (e=1): reduce e by pairs of 2 leaving remainder 1.
theorem r6r3_drain_e1 : ∀ k a, ⟨a + k, (0 : ℕ), c, 0, 2 * k + 1, 0⟩ [fm]⊢*
    ⟨a, 0, c, 0, 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm
    exact ih a

-- R1/R4 chain with e=0.
theorem r1r4_chain_e0 : ∀ k a f, ⟨a, (1 : ℕ), k, 0, 0, f⟩ [fm]⊢*
    ⟨a + k, 1, 0, 0, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a f
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) (f + 1)); ring_nf; finish

-- R1/R4 chain with e=1.
theorem r1r4_chain_e1 : ∀ k a f, ⟨a, (1 : ℕ), k, 0, 1, f⟩ [fm]⊢*
    ⟨a + k, 1, 0, 0, 1, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a f
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) (f + 1)); ring_nf; finish

-- Case e=0, f=2m: (b+m+1, 0, 0, 0, 0, 2m) ⊢⁺ (b+2m+1, 0, 0, 0, 0, 2m+1).
theorem trans_e0_feven (m b : ℕ) :
    ⟨b + m + 1, (0 : ℕ), 0, 0, 0, 2 * m⟩ [fm]⊢⁺ ⟨b + 2 * m + 1, 0, 0, 0, 0, 2 * m + 1⟩ := by
  apply stepStar_stepPlus_stepPlus (r5_e0 (2 * m) (a := b + m + 1))
  rw [show b + m + 1 = (b + 1) + m from by ring]
  apply stepStar_stepPlus_stepPlus (r6r3_drain_e0 m (b + 1) (c := 2 * m))
  step fm; step fm
  apply stepStar_trans (r1r4_chain_e0 (2 * m) (b + 1) 1)
  rw [show b + 1 + 2 * m = b + 2 * m + 1 from by ring,
      show 1 + 2 * m = (2 * m + 1 : ℕ) from by ring]
  step fm; finish

-- Case e=0, f=2m+1: (b+m+1, 0, 0, 0, 0, 2m+1) ⊢⁺ (b+2m+2, 0, 0, 0, 1, 2m+2).
theorem trans_e0_fodd (m b : ℕ) :
    ⟨b + m + 1, (0 : ℕ), 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺
    ⟨b + 2 * m + 2, 0, 0, 0, 1, 2 * m + 2⟩ := by
  apply stepStar_stepPlus_stepPlus (r5_e0 (2 * m + 1) (a := b + m + 1))
  -- State: (b+m+1, 0, 2m+1, 0, 2m+1, 0)
  rw [show b + m + 1 = (b + 1) + m from by ring]
  apply stepStar_stepPlus_stepPlus (r6r3_drain_e1 m (b + 1) (c := 2 * m + 1))
  -- State: (b+1, 0, 2m+1, 0, 1, 0)
  step fm; step fm
  apply stepStar_trans (r1r4_chain_e1 (2 * m + 1) (b + 1) 1)
  rw [show b + 1 + (2 * m + 1) = b + 2 * m + 2 from by ring,
      show 1 + (2 * m + 1) = (2 * m + 2 : ℕ) from by ring]
  step fm; finish

-- Case e=1, f=2m: (b+m+1, 0, 0, 0, 1, 2m) ⊢⁺ (b+2m+1, 0, 0, 0, 1, 2m+1).
theorem trans_e1_feven (m b : ℕ) :
    ⟨b + m + 1, (0 : ℕ), 0, 0, 1, 2 * m⟩ [fm]⊢⁺
    ⟨b + 2 * m + 1, 0, 0, 0, 1, 2 * m + 1⟩ := by
  apply stepStar_stepPlus_stepPlus (r5_e1 (2 * m) (a := b + m + 1))
  -- State: (b+m+1, 0, 2m, 0, 2m+1, 0)
  rw [show b + m + 1 = (b + 1) + m from by ring]
  apply stepStar_stepPlus_stepPlus (r6r3_drain_e1 m (b + 1) (c := 2 * m))
  -- State: (b+1, 0, 2m, 0, 1, 0)
  step fm; step fm
  apply stepStar_trans (r1r4_chain_e1 (2 * m) (b + 1) 1)
  rw [show b + 1 + 2 * m = b + 2 * m + 1 from by ring,
      show 1 + 2 * m = (2 * m + 1 : ℕ) from by ring]
  step fm; finish

-- Case e=1, f=2m+1: (b+m+2, 0, 0, 0, 1, 2m+1) ⊢⁺ (b+2m+2, 0, 0, 0, 0, 2m+2).
theorem trans_e1_fodd (m b : ℕ) :
    ⟨b + m + 2, (0 : ℕ), 0, 0, 1, 2 * m + 1⟩ [fm]⊢⁺
    ⟨b + 2 * m + 2, 0, 0, 0, 0, 2 * m + 2⟩ := by
  apply stepStar_stepPlus_stepPlus (r5_e1 (2 * m + 1) (a := b + m + 2))
  -- State: (b+m+2, 0, 2m+1, 0, 2m+2, 0)
  rw [show b + m + 2 = (b + 1) + (m + 1) from by ring,
      show 2 * m + 1 + 1 = 2 * (m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r6r3_drain_e0 (m + 1) (b + 1) (c := 2 * m + 1))
  -- State: (b+1, 0, 2m+1, 0, 0, 0)
  step fm; step fm
  apply stepStar_trans (r1r4_chain_e0 (2 * m + 1) (b + 1) 1)
  rw [show b + 1 + (2 * m + 1) = b + 2 * m + 2 from by ring,
      show 1 + (2 * m + 1) = (2 * m + 2 : ℕ) from by ring]
  step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 0, 4⟩) (by execute fm 36)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e f, q = ⟨a, 0, 0, 0, e, f⟩ ∧ e ≤ 1 ∧ f ≥ 2 ∧ a ≥ f)
  · intro c ⟨a, e, f, hq, he, hf, haf⟩; subst hq
    rcases e with _ | _ | e
    · -- e = 0
      rcases Nat.even_or_odd f with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- f even = 2m
        rw [show m + m = 2 * m from by ring] at hm; subst hm
        refine ⟨⟨a + m, 0, 0, 0, 0, 2 * m + 1⟩,
          ⟨a + m, 0, 2 * m + 1, rfl, by omega, by omega, by omega⟩, ?_⟩
        rw [show a = (a - m - 1) + m + 1 from by omega,
            show (a - m - 1) + m + 1 + m = (a - m - 1) + 2 * m + 1 from by ring]
        exact trans_e0_feven m (a - m - 1)
      · -- f odd = 2m + 1
        subst hm
        refine ⟨⟨a + m + 1, 0, 0, 0, 1, 2 * m + 2⟩,
          ⟨a + m + 1, 1, 2 * m + 2, rfl, by omega, by omega, by omega⟩, ?_⟩
        rw [show a = (a - m - 1) + m + 1 from by omega,
            show (a - m - 1) + m + 1 + m + 1 = (a - m - 1) + 2 * m + 2 from by ring]
        exact trans_e0_fodd m (a - m - 1)
    · -- e = 1
      rcases Nat.even_or_odd f with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- f even = 2m
        rw [show m + m = 2 * m from by ring] at hm; subst hm
        refine ⟨⟨a + m, 0, 0, 0, 1, 2 * m + 1⟩,
          ⟨a + m, 1, 2 * m + 1, rfl, by omega, by omega, by omega⟩, ?_⟩
        rw [show a = (a - m - 1) + m + 1 from by omega,
            show (a - m - 1) + m + 1 + m = (a - m - 1) + 2 * m + 1 from by ring]
        exact trans_e1_feven m (a - m - 1)
      · -- f odd = 2m + 1
        subst hm
        refine ⟨⟨a + m, 0, 0, 0, 0, 2 * m + 2⟩,
          ⟨a + m, 0, 2 * m + 2, rfl, by omega, by omega, by omega⟩, ?_⟩
        rw [show a = (a - m - 2) + m + 2 from by omega,
            show (a - m - 2) + m + 2 + m = (a - m - 2) + 2 * m + 2 from by ring]
        exact trans_e1_fodd m (a - m - 2)
    · omega
  · exact ⟨4, 0, 4, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_1399
