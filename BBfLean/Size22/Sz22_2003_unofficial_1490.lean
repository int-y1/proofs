import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1490: [7/15, 81/77, 22/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 0  4  0 -1 -1
 1 -1  0  0  1
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1490

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+4, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem bulk_round : ∀ k, ∀ a c d,
    ⟨a + k, 0, c + 5 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 4 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 5 * (k + 1) = (c + 5 * k) + 1 + 1 + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 4))
    ring_nf; finish

theorem r3r2_chain : ∀ k, ∀ a b d,
    ⟨a, b + 1, 0, d + k, 0⟩ [fm]⊢* ⟨a + k, b + 1 + 3 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    rw [show b + 4 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (b + 3) d)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a e,
    ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ a c,
    ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm
    apply stepStar_trans (ih a (c + 1))
    ring_nf; finish

theorem drain_phase (a b d : ℕ) :
    ⟨a, b + 1, 0, d, 0⟩ [fm]⊢* ⟨a + 4 * d + b + 1, 0, b + 1 + 3 * d, 0, 0⟩ := by
  rw [show d = 0 + d from by ring]
  apply stepStar_trans (r3r2_chain d a b 0)
  apply stepStar_trans (r3_chain (b + 1 + 3 * d) (a + d) 0)
  rw [show 0 + (b + 1 + 3 * d) = b + 1 + 3 * d from by ring]
  apply stepStar_trans (r4_chain (b + 1 + 3 * d) (a + d + (b + 1 + 3 * d)) 0)
  ring_nf; finish

-- Tail for r=0: R5 then R2.
theorem tail_r0 (a d : ℕ) :
    ⟨a + 1, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a, 5, 0, d, 0⟩ := by
  step fm; step fm; finish

-- Tail for r=1: R5, R1, R2.
theorem tail_r1 (a d : ℕ) :
    ⟨a + 1, 0, 1, d, 0⟩ [fm]⊢⁺ ⟨a, 4, 0, d, 0⟩ := by
  step fm; step fm; step fm; finish

-- Tail for r=2: R5, R1, R2, R1, R3, R2.
theorem tail_r2 (a d : ℕ) :
    ⟨a + 1, 0, 2, d, 0⟩ [fm]⊢⁺ ⟨a + 1, 6, 0, d, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Tail for r=3: R5, R1, R2, R1*2, R3, R2.
theorem tail_r3 (a d : ℕ) :
    ⟨a + 1, 0, 3, d, 0⟩ [fm]⊢⁺ ⟨a + 1, 5, 0, d + 1, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Tail for r=4: R5, R1, R2, R1*3, R3, R2.
theorem tail_r4 (a d : ℕ) :
    ⟨a + 1, 0, 4, d, 0⟩ [fm]⊢⁺ ⟨a + 1, 4, 0, d + 2, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Combined tail + drain for r=2:
-- (a+1, 0, 2, d, 0) ⊢⁺ (a + 4*d + 7, 0, 3*d + 6, 0, 0)
theorem tail_drain_r2 (a d : ℕ) :
    ⟨a + 1, 0, 2, d, 0⟩ [fm]⊢⁺ ⟨a + 4 * d + 7, 0, 3 * d + 6, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (tail_r2 a d)
  rw [show (6 : ℕ) = 5 + 1 from by ring]
  apply stepStar_trans (drain_phase (a + 1) 5 d)
  ring_nf; finish

-- Combined tail + drain for r=3:
-- (a+1, 0, 3, d, 0) ⊢⁺ (a + 4*d + 10, 0, 3*d + 8, 0, 0)
theorem tail_drain_r3 (a d : ℕ) :
    ⟨a + 1, 0, 3, d, 0⟩ [fm]⊢⁺ ⟨a + 4 * d + 10, 0, 3 * d + 8, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (tail_r3 a d)
  rw [show (5 : ℕ) = 4 + 1 from by ring]
  apply stepStar_trans (drain_phase (a + 1) 4 (d + 1))
  ring_nf; finish

-- Combined tail + drain for r=4:
-- (a+1, 0, 4, d, 0) ⊢⁺ (a + 4*d + 13, 0, 3*d + 10, 0, 0)
theorem tail_drain_r4 (a d : ℕ) :
    ⟨a + 1, 0, 4, d, 0⟩ [fm]⊢⁺ ⟨a + 4 * d + 13, 0, 3 * d + 10, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (tail_r4 a d)
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (drain_phase (a + 1) 3 (d + 2))
  ring_nf; finish

-- Combined tail + drain for r=0:
-- (a+1, 0, 0, d+1, 0) ⊢⁺ (a + 4*d + 5, 0, 3*d + 5, 0, 0)
theorem tail_drain_r0 (a d : ℕ) :
    ⟨a + 1, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a + 4 * d + 5, 0, 3 * d + 5, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (tail_r0 a d)
  rw [show (5 : ℕ) = 4 + 1 from by ring]
  apply stepStar_trans (drain_phase a 4 d)
  ring_nf; finish

-- Combined tail + drain for r=1:
-- (a+1, 0, 1, d, 0) ⊢⁺ (a + 4*d + 4, 0, 3*d + 4, 0, 0)
theorem tail_drain_r1 (a d : ℕ) :
    ⟨a + 1, 0, 1, d, 0⟩ [fm]⊢⁺ ⟨a + 4 * d + 4, 0, 3 * d + 4, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (tail_r1 a d)
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (drain_phase a 3 d)
  ring_nf; finish

-- Full transition for c ≡ 2 (mod 5), c = 5q+2:
theorem trans_r2 (a q : ℕ) :
    ⟨a + q + 1, 0, 5 * q + 2, 0, 0⟩ [fm]⊢⁺ ⟨a + 16 * q + 7, 0, 12 * q + 6, 0, 0⟩ := by
  rw [show a + q + 1 = (a + 1) + q from by ring,
      show 5 * q + 2 = 2 + 5 * q from by ring]
  apply stepStar_stepPlus_stepPlus (bulk_round q (a + 1) 2 0)
  rw [show 0 + 4 * q = 4 * q from by ring]
  apply stepPlus_stepStar_stepPlus (tail_drain_r2 a (4 * q))
  ring_nf; finish

-- Full transition for c ≡ 3 (mod 5), c = 5q+3:
theorem trans_r3 (a q : ℕ) :
    ⟨a + q + 1, 0, 5 * q + 3, 0, 0⟩ [fm]⊢⁺ ⟨a + 16 * q + 10, 0, 12 * q + 8, 0, 0⟩ := by
  rw [show a + q + 1 = (a + 1) + q from by ring,
      show 5 * q + 3 = 3 + 5 * q from by ring]
  apply stepStar_stepPlus_stepPlus (bulk_round q (a + 1) 3 0)
  rw [show 0 + 4 * q = 4 * q from by ring]
  apply stepPlus_stepStar_stepPlus (tail_drain_r3 a (4 * q))
  ring_nf; finish

-- Full transition for c ≡ 4 (mod 5), c = 5q+4:
theorem trans_r4 (a q : ℕ) :
    ⟨a + q + 1, 0, 5 * q + 4, 0, 0⟩ [fm]⊢⁺ ⟨a + 16 * q + 13, 0, 12 * q + 10, 0, 0⟩ := by
  rw [show a + q + 1 = (a + 1) + q from by ring,
      show 5 * q + 4 = 4 + 5 * q from by ring]
  apply stepStar_stepPlus_stepPlus (bulk_round q (a + 1) 4 0)
  rw [show 0 + 4 * q = 4 * q from by ring]
  apply stepPlus_stepStar_stepPlus (tail_drain_r4 a (4 * q))
  ring_nf; finish

-- Full transition for c ≡ 0 (mod 5), c = 5*(q+1):
theorem trans_r0 (a q : ℕ) :
    ⟨a + q + 2, 0, 5 * (q + 1), 0, 0⟩ [fm]⊢⁺
    ⟨a + 16 * q + 17, 0, 12 * q + 14, 0, 0⟩ := by
  rw [show a + q + 2 = (a + 1) + (q + 1) from by ring,
      show 5 * (q + 1) = 0 + 5 * (q + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (bulk_round (q + 1) (a + 1) 0 0)
  rw [show 0 + 4 * (q + 1) = (4 * q + 3) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (tail_drain_r0 a (4 * q + 3))
  ring_nf; finish

-- Full transition for c ≡ 1 (mod 5), c = 5*(q+1)+1:
theorem trans_r1 (a q : ℕ) :
    ⟨a + q + 2, 0, 5 * (q + 1) + 1, 0, 0⟩ [fm]⊢⁺
    ⟨a + 16 * q + 20, 0, 12 * q + 16, 0, 0⟩ := by
  rw [show a + q + 2 = (a + 1) + (q + 1) from by ring,
      show 5 * (q + 1) + 1 = 1 + 5 * (q + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (bulk_round (q + 1) (a + 1) 1 0)
  rw [show 0 + 4 * (q + 1) = 4 * q + 4 from by ring]
  apply stepPlus_stepStar_stepPlus (tail_drain_r1 a (4 * q + 4))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 2, 0, 0⟩)
  · execute fm 4
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a + 1, 0, c, 0, 0⟩ ∧ c ≥ 2 ∧ 5 * a + 3 ≥ c)
  · intro q ⟨a, c, hq, hc2, hinv⟩; subst hq
    have h5 : c % 5 < 5 := Nat.mod_lt _ (by omega)
    obtain ⟨k, hk⟩ : ∃ k, c = 5 * k + c % 5 := ⟨c / 5, by omega⟩
    interval_cases (c % 5)
    · -- c ≡ 0 (mod 5): c = 5*k, k ≥ 1
      rw [Nat.add_zero] at hk; subst hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, a = F + k' + 1 := ⟨a - k' - 1, by omega⟩
      exact ⟨⟨F + 16 * k' + 17, 0, 12 * k' + 14, 0, 0⟩,
        ⟨F + 16 * k' + 16, 12 * k' + 14, by ring_nf, by omega, by omega⟩,
        trans_r0 F k'⟩
    · -- c ≡ 1 (mod 5): c = 5*k+1, k ≥ 1
      subst hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, a = F + k' + 1 := ⟨a - k' - 1, by omega⟩
      exact ⟨⟨F + 16 * k' + 20, 0, 12 * k' + 16, 0, 0⟩,
        ⟨F + 16 * k' + 19, 12 * k' + 16, by ring_nf, by omega, by omega⟩,
        trans_r1 F k'⟩
    · -- c ≡ 2 (mod 5): c = 5*k+2
      subst hk
      obtain ⟨F, rfl⟩ : ∃ F, a = F + k := ⟨a - k, by omega⟩
      exact ⟨⟨F + 16 * k + 7, 0, 12 * k + 6, 0, 0⟩,
        ⟨F + 16 * k + 6, 12 * k + 6, by ring_nf, by omega, by omega⟩,
        trans_r2 F k⟩
    · -- c ≡ 3 (mod 5): c = 5*k+3
      subst hk
      obtain ⟨F, rfl⟩ : ∃ F, a = F + k := ⟨a - k, by omega⟩
      exact ⟨⟨F + 16 * k + 10, 0, 12 * k + 8, 0, 0⟩,
        ⟨F + 16 * k + 9, 12 * k + 8, by ring_nf, by omega, by omega⟩,
        trans_r3 F k⟩
    · -- c ≡ 4 (mod 5): c = 5*k+4
      subst hk
      obtain ⟨F, rfl⟩ : ∃ F, a = F + k := ⟨a - k, by omega⟩
      exact ⟨⟨F + 16 * k + 13, 0, 12 * k + 10, 0, 0⟩,
        ⟨F + 16 * k + 12, 12 * k + 10, by ring_nf, by omega, by omega⟩,
        trans_r4 F k⟩
  · exact ⟨0, 2, by ring_nf, by omega, by omega⟩

end Sz22_2003_unofficial_1490
