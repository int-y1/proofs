import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1497: [7/15, 9/77, 22/3, 25/11, 99/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 1 -1  0  0  1
 0  0  2  0 -1
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1497

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- R3 chain: drain b with c=d=0.
theorem r3_chain : ∀ k, ∀ a e, ⟨a, k, (0 : ℕ), 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e; step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- R4 chain: drain e to c.
theorem r4_chain : ∀ k, ∀ a c, ⟨a, (0 : ℕ), c, 0, k⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; simp; exists 0
  | succ k ih =>
    intro a c; step fm
    apply stepStar_trans (ih a (c + 2))
    ring_nf; finish

-- Main drain round: R5,R1,R1,R2,R1,R1.
theorem main_drain : ∀ k, ∀ A C D, ⟨A + k, (0 : ℕ), C + 4 * k, D, 0⟩ [fm]⊢* ⟨A, 0, C, D + 3 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro A C D; simp; exists 0
  | succ k ih =>
    intro A C D
    rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 4 * (k + 1) = ((C + 4 * k) + 2) + 2 from by ring]
    step fm; step fm; step fm
    rw [show D + 2 = (D + 1) + 1 from by ring]
    step fm
    rw [show (C + 4 * k) + 2 = ((C + 4 * k) + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih A C (D + 3))
    ring_nf; finish

-- Partial round for odd B: c=2 remainder.
theorem partial_odd (A D : ℕ) :
    ⟨A + 1, (0 : ℕ), 2, D, 0⟩ [fm]⊢* ⟨A, 2, 0, D + 1, 0⟩ := by
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  step fm; step fm; step fm
  rw [show D + 2 = (D + 1) + 1 from by ring]
  step fm; ring_nf; finish

-- Partial for even B: c=0 remainder.
theorem partial_even (A D : ℕ) :
    ⟨A + 1, (0 : ℕ), 0, D + 1, 0⟩ [fm]⊢* ⟨A, 4, 0, D, 0⟩ := by
  step fm; step fm; ring_nf; finish

-- R3+R2 chain: (x, b+1, 0, K, 0) ⊢* (x+K, b+K+1, 0, 0, 0)
theorem r3r2_chain : ∀ K, ∀ x b, ⟨x, b + 1, (0 : ℕ), K, 0⟩ [fm]⊢* ⟨x + K, b + K + 1, 0, 0, 0⟩ := by
  intro K; induction K with
  | zero => intro x b; simp; exists 0
  | succ K ih =>
    intro x b
    rw [show b + 1 = b + 1 from rfl,
        show (K + 1 : ℕ) = K + 1 from rfl]
    step fm -- R3: (x+1, b, 0, K+1, 1)
    step fm -- R2: (x+1, b+2, 0, K, 0)
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (x + 1) (b + 1))
    ring_nf; finish

-- Odd B case: (a, 2k+3, 0, 0, 0) ⊢⁺ (a+4k+5, 3k+6, 0, 0, 0)
theorem main_odd (a k : ℕ) :
    ⟨a, 2 * k + 3, (0 : ℕ), 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * k + 5, 3 * k + 6, 0, 0, 0⟩ := by
  -- Phase 1: R3 drain (2k+3) steps
  apply stepStar_stepPlus_stepPlus (r3_chain (2 * k + 3) a 0)
  rw [show a + (2 * k + 3) = a + 2 * k + 3 from by ring,
      show (0 : ℕ) + (2 * k + 3) = 2 * k + 3 from by ring]
  -- State: (a+2k+3, 0, 0, 0, 2k+3)
  -- Phase 2: R4 drain
  apply stepPlus_stepStar_stepPlus
  · step fm; finish
  -- State after 1 R4: (a+2k+3, 0, 2, 0, 2k+2)
  apply stepStar_trans (r4_chain (2 * k + 2) (a + 2 * k + 3) 2)
  rw [show 2 + 2 * (2 * k + 2) = 4 * k + 6 from by ring]
  -- State: (a+2k+3, 0, 4k+6, 0, 0)
  -- Phase 3: main drain (k+1 rounds)
  rw [show a + 2 * k + 3 = (a + k + 2) + (k + 1) from by ring,
      show 4 * k + 6 = 2 + 4 * (k + 1) from by ring]
  apply stepStar_trans (main_drain (k + 1) (a + k + 2) 2 0)
  rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring]
  -- State: (a+k+2, 0, 2, 3k+3, 0)
  -- Phase 4a: partial odd round
  rw [show a + k + 2 = (a + k + 1) + 1 from by ring]
  apply stepStar_trans (partial_odd (a + k + 1) (3 * k + 3))
  rw [show 3 * k + 3 + 1 = 3 * k + 4 from by ring]
  -- State: (a+k+1, 2, 0, 3k+4, 0)
  -- Phase 5: R3+R2 chain (3k+4 rounds)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 3 * k + 4 = 3 * k + 4 from rfl]
  apply stepStar_trans (r3r2_chain (3 * k + 4) (a + k + 1) 1)
  ring_nf; finish

-- Even B case: (a, 2k+4, 0, 0, 0) ⊢⁺ (a+4k+6, 3k+9, 0, 0, 0)
theorem main_even (a k : ℕ) :
    ⟨a, 2 * k + 4, (0 : ℕ), 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * k + 6, 3 * k + 9, 0, 0, 0⟩ := by
  -- Phase 1: R3 drain (2k+4) steps
  apply stepStar_stepPlus_stepPlus (r3_chain (2 * k + 4) a 0)
  rw [show a + (2 * k + 4) = a + 2 * k + 4 from by ring,
      show (0 : ℕ) + (2 * k + 4) = 2 * k + 4 from by ring]
  -- Phase 2: R4 drain
  apply stepPlus_stepStar_stepPlus
  · step fm; finish
  apply stepStar_trans (r4_chain (2 * k + 3) (a + 2 * k + 4) 2)
  rw [show 2 + 2 * (2 * k + 3) = 4 * k + 8 from by ring]
  -- State: (a+2k+4, 0, 4k+8, 0, 0)
  -- Phase 3: main drain (k+2 rounds)
  rw [show a + 2 * k + 4 = (a + k + 2) + (k + 2) from by ring,
      show 4 * k + 8 = 0 + 4 * (k + 2) from by ring]
  apply stepStar_trans (main_drain (k + 2) (a + k + 2) 0 0)
  rw [show 0 + 3 * (k + 2) = 3 * k + 6 from by ring]
  -- State: (a+k+2, 0, 0, 3k+6, 0)
  -- Phase 4b: partial even
  rw [show a + k + 2 = (a + k + 1) + 1 from by ring,
      show 3 * k + 6 = (3 * k + 5) + 1 from by ring]
  apply stepStar_trans (partial_even (a + k + 1) (3 * k + 5))
  -- State: (a+k+1, 4, 0, 3k+5, 0)
  -- Phase 5: R3+R2 chain (3k+5 rounds)
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show 3 * k + 5 = 3 * k + 5 from rfl]
  apply stepStar_trans (r3r2_chain (3 * k + 5) (a + k + 1) 3)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 6, 0, 0, 0⟩) (by execute fm 24)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a b, q = ⟨a, b + 3, (0 : ℕ), 0, 0⟩)
  · intro q ⟨a, b, hq⟩
    subst hq
    rcases Nat.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      rw [show k + k + 3 = 2 * k + 3 from by ring]
      refine ⟨⟨a + 4 * k + 5, 3 * k + 6, 0, 0, 0⟩, ⟨a + 4 * k + 5, 3 * k + 3, by ring_nf⟩, main_odd a k⟩
    · subst hk
      rw [show 2 * k + 1 + 3 = 2 * k + 4 from by ring]
      refine ⟨⟨a + 4 * k + 6, 3 * k + 9, 0, 0, 0⟩, ⟨a + 4 * k + 6, 3 * k + 6, by ring_nf⟩, main_even a k⟩
  · exact ⟨4, 3, by ring_nf⟩

end Sz22_2003_unofficial_1497
