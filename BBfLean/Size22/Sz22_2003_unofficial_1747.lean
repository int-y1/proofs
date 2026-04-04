import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1747: [8/15, 99/14, 55/2, 7/11, 3/7]

Vector representation:
```
 3 -1 -1  0  0
-1  2  0 -1  1
-1  0  1  0  1
 0  0  0  1 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1747

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1: R3 chain. Drain a into c and e (b=0, d=0).
theorem r3_chain : ∀ k, ∀ c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show k + 1 = (k + 1) from rfl]
    step fm
    apply stepStar_trans (ih (c + 1) (e + 1))
    ring_nf; finish

-- Phase 2: R4 chain. Move e to d (a=0, b=0).
theorem e_to_d : ∀ k, ∀ c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

-- Phase 4: R2+R1+R1 interleaved chain.
-- Each round: (a, 0, c+2, d+1, e) -> R2 -> (a-1, 2, c+2, d, e+1) -> R1 -> (a+2, 1, c+1, d, e+1) -> R1 -> (a+5, 0, c, d, e+1)
-- Net per round: a += 5, c -= 2, d -= 1, e += 1
theorem r2r1r1_chain : ∀ k, ∀ a d e, ⟨a + 1, 0, 2 * k, d + k, e⟩ [fm]⊢* ⟨a + 5 * k + 1, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + 1 = (a + 1) from rfl,
        show 2 * (k + 1) = 2 * k + 1 + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R2: a >= 1, d >= 1
    step fm  -- R1: b >= 1, c >= 1
    step fm  -- R1: b >= 1, c >= 1
    rw [show a + 1 + 5 = (a + 5) + 1 from by ring]
    apply stepStar_trans (ih (a + 5) d (e + 1))
    ring_nf; finish

-- Phase 5: R2 drain. R2 chain with accumulating b (c=0).
theorem r2_drain : ∀ k, ∀ a b e, ⟨a + k, b, 0, k, e⟩ [fm]⊢* ⟨a, b + 2 * k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k + 1) = k + 1 from rfl]
    step fm  -- R2
    apply stepStar_trans (ih a (b + 2) (e + 1))
    ring_nf; finish

-- Phase 6: R3+R1 interleaved chain (a >= 1, c=0, d=0).
-- Each round: (a, b+1, 0, 0, e) -> R3 (since a >= 1, d=0, b could be >= 1 but c=0 so R1 won't fire) -> (a-1, b+1, 1, 0, e+1) -> R1 (b >= 1, c >= 1) -> (a+2, b, 0, 0, e+1)
-- Net per round: a += 2, b -= 1, e += 1
theorem r3r1_chain : ∀ k, ∀ a e, ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show a + 1 = (a + 1) from rfl]
    step fm  -- R3: a >= 1
    step fm  -- R1: b >= 1, c >= 1
    rw [show a + 1 + 2 = (a + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) (e + 1))
    ring_nf; finish

-- Main transition: (2a+3, 0, 0, 0, 2e) ->+ (8a+6e+11, 0, 0, 0, 4a+6e+4)
-- where e <= 2a+3 (ensures natural subtraction works)
theorem main_trans (a e : ℕ) (he : e ≤ 2 * a + 3) :
    ⟨2 * a + 3, 0, 0, 0, 2 * e⟩ [fm]⊢⁺ ⟨8 * a + 6 * e + 11, 0, 0, 0, 4 * a + 6 * e + 4⟩ := by
  -- Phase 1: R3 chain
  have h1 : ⟨2 * a + 3, 0, 0, 0, 2 * e⟩ [fm]⊢⁺ ⟨0, 0, 2 * a + 3, 0, 2 * a + 2 * e + 3⟩ := by
    rw [show 2 * a + 3 = (2 * a + 2) + 1 from by ring]
    step fm
    apply stepStar_trans (r3_chain (2 * a + 2) 1 (2 * e + 1))
    ring_nf; finish
  -- Phase 2: R4 chain
  have h2 : ⟨0, 0, 2 * a + 3, 0, 2 * a + 2 * e + 3⟩ [fm]⊢* ⟨0, 0, 2 * a + 3, 2 * a + 2 * e + 3, 0⟩ := by
    rw [show 2 * a + 2 * e + 3 = 2 * a + 2 * e + 3 from rfl]
    apply stepStar_trans (e_to_d (2 * a + 2 * e + 3) (2 * a + 3) 0)
    ring_nf; finish
  -- Phase 3: R5 + R1
  have h3 : ⟨0, 0, 2 * a + 3, 2 * a + 2 * e + 3, 0⟩ [fm]⊢* ⟨3, 0, 2 * a + 2, 2 * a + 2 * e + 2, 0⟩ := by
    rw [show 2 * a + 2 * e + 3 = (2 * a + 2 * e + 2) + 1 from by ring,
        show 2 * a + 3 = (2 * a + 2) + 1 from by ring]
    step fm; step fm; ring_nf; finish
  -- Phase 4: R2+R1+R1 chain (a+1 rounds)
  have h4 : ⟨3, 0, 2 * a + 2, 2 * a + 2 * e + 2, 0⟩ [fm]⊢* ⟨5 * a + 8, 0, 0, a + 2 * e + 1, a + 1⟩ := by
    rw [show (3 : ℕ) = 2 + 1 from by ring,
        show 2 * a + 2 = 2 * (a + 1) from by ring,
        show 2 * a + 2 * e + 2 = (a + 2 * e + 1) + (a + 1) from by ring]
    apply stepStar_trans (r2r1r1_chain (a + 1) 2 (a + 2 * e + 1) 0)
    ring_nf; finish
  -- Phase 5: R2 drain (a+2e+1 steps)
  have h5 : ⟨5 * a + 8, 0, 0, a + 2 * e + 1, a + 1⟩ [fm]⊢* ⟨4 * a + 7 - 2 * e, 2 * a + 4 * e + 2, 0, 0, 2 * a + 2 * e + 2⟩ := by
    rw [show 5 * a + 8 = (4 * a + 7 - 2 * e) + (a + 2 * e + 1) from by omega,
        show a + 2 * e + 1 = a + 2 * e + 1 from rfl]
    apply stepStar_trans (r2_drain (a + 2 * e + 1) (4 * a + 7 - 2 * e) 0 (a + 1))
    ring_nf; finish
  -- Phase 6: R3+R1 chain (2a+4e+2 rounds)
  have h6 : ⟨4 * a + 7 - 2 * e, 2 * a + 4 * e + 2, 0, 0, 2 * a + 2 * e + 2⟩ [fm]⊢* ⟨8 * a + 6 * e + 11, 0, 0, 0, 4 * a + 6 * e + 4⟩ := by
    rw [show 4 * a + 7 - 2 * e = (4 * a + 6 - 2 * e) + 1 from by omega]
    apply stepStar_trans (r3r1_chain (2 * a + 4 * e + 2) (4 * a + 6 - 2 * e) (2 * a + 2 * e + 2))
    have ha : 4 * a + 6 - 2 * e + 2 * (2 * a + 4 * e + 2) + 1 = 8 * a + 6 * e + 11 := by omega
    have he2 : (2 * a + 2 * e + 2) + (2 * a + 4 * e + 2) = 4 * a + 6 * e + 4 := by ring
    rw [ha, he2]; finish
  -- Compose all phases
  exact stepPlus_stepStar_stepPlus
    (stepPlus_stepStar_stepPlus
      (stepPlus_stepStar_stepPlus
        (stepPlus_stepStar_stepPlus
          (stepPlus_stepStar_stepPlus h1 h2) h3) h4) h5) h6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 0⟩)
  · execute fm 4
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨2 * a + 3, 0, 0, 0, 2 * e⟩ ∧ e ≤ 2 * a + 3)
  · intro c ⟨a, e, hq, he⟩; subst hq
    exact ⟨⟨2 * (4 * a + 3 * e + 4) + 3, 0, 0, 0, 2 * (2 * a + 3 * e + 2)⟩,
           ⟨4 * a + 3 * e + 4, 2 * a + 3 * e + 2, rfl, by omega⟩,
           by rw [show 2 * (4 * a + 3 * e + 4) + 3 = 8 * a + 6 * e + 11 from by ring,
                  show 2 * (2 * a + 3 * e + 2) = 4 * a + 6 * e + 4 from by ring];
              exact main_trans a e he⟩
  · exact ⟨0, 0, by simp, by omega⟩
