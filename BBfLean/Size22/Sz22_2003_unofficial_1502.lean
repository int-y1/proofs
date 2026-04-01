import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1502: [7/15, 9/77, 242/3, 5/11, 99/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 1 -1  0  0  2
 0  0  1  0 -1
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1502

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ a c,
    ⟨a, (0 : ℕ), c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm; apply stepStar_trans (ih a (c + 1)); ring_nf; finish

theorem six_step_drain : ∀ k, ∀ a c d,
    ⟨a + k, (0 : ℕ), c + 4 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · simp; exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 4 * (k + 1) = (c + 4 * k + 2) + 1 + 1 from by ring]
    step fm
    rw [show (c + 4 * k + 2) + 1 + 1 = ((c + 4 * k + 2) + 1) + 1 from by ring]
    step fm
    rw [show (c + 4 * k + 2) + 1 = (c + 4 * k + 2) + 1 from rfl]
    step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring, show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show c + 4 * k + 2 = (c + 4 * k + 1) + 1 from by ring]
    step fm
    rw [show c + 4 * k + 1 = (c + 4 * k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a c (d + 3)); ring_nf; finish

-- R3,R2,R2 chain with e=0: each round a += 1, b += 3, d -= 2
theorem r3r2r2_chain_e0 : ∀ k, ∀ a b d,
    ⟨a, b + 1, (0 : ℕ), d + 2 * k, 0⟩ [fm]⊢* ⟨a + k, b + 3 * k + 1, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · simp; exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 1 + 1 from by ring]
    -- R3 fires (b+1>=1, c=0 so R1 no, R2 needs e+1 but e=0 so no).
    step fm
    -- After R3: (a+1, b, 0, (d+2k)+1+1, 2). Now R2 fires (d+1, e=2=1+1).
    rw [show (d + 2 * k) + 1 + 1 = ((d + 2 * k) + 1) + 1 from by ring,
        show (2 : ℕ) = (1 : ℕ) + 1 from rfl]
    step fm
    -- After R2: (a+1, b+2, 0, (d+2k)+1, 1). R2 again (d+1, e=1=0+1).
    rw [show (d + 2 * k) + 1 = (d + 2 * k) + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    -- After R2: (a+1, b+4, 0, d+2k, 0).
    rw [show b + 4 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (b + 3) d); ring_nf; finish

theorem r3_chain : ∀ k, ∀ a b e,
    ⟨a, b + k, (0 : ℕ), 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · simp; exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b (e + 2)); ring_nf; finish

theorem tail_d0 (B A : ℕ) :
    ⟨A, B + 1, (0 : ℕ), 0, 0⟩ [fm]⊢* ⟨A + B + 1, 0, 0, 0, 2 * B + 2⟩ := by
  have h := r3_chain (B + 1) A 0 0
  rw [show 0 + (B + 1) = B + 1 from by ring,
      show 0 + 2 * (B + 1) = 2 * B + 2 from by ring] at h; exact h

-- D=1 tail with E=0: R3 then R2 then R3 chain
-- (A, B+1, 0, 1, 0) -> R3: (A+1, B, 0, 1, 2) -> R2 (d=0+1, e=1+1): (A+1, B+2, 0, 0, 1)
-- -> R3 chain B+2 steps: (A+B+3, 0, 0, 0, 1+2*(B+2)) = (A+B+3, 0, 0, 0, 2B+5)
theorem tail_d1 (B A : ℕ) :
    ⟨A, B + 1, (0 : ℕ), 1, 0⟩ [fm]⊢* ⟨A + B + 3, 0, 0, 0, 2 * B + 5⟩ := by
  step fm
  rw [show (2 : ℕ) = (1 : ℕ) + 1 from rfl]
  step fm
  have h := r3_chain (B + 2) (A + 1) 0 1
  rw [show 0 + (B + 2) = B + 2 from by ring,
      show 1 + 2 * (B + 2) = 2 * B + 5 from by ring,
      show A + 1 + (B + 2) = A + B + 3 from by ring] at h; exact h

-- Unified d-drain (with E=0)
theorem d_drain (D A B : ℕ) :
    ⟨A, B + 1, (0 : ℕ), D, 0⟩ [fm]⊢* ⟨A + B + 1 + 2 * D, 0, 0, 0, 2 * B + 2 + 3 * D⟩ := by
  rcases Nat.even_or_odd D with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    rw [show 2 * k = 0 + 2 * k from by ring]
    apply stepStar_trans (r3r2r2_chain_e0 k A B 0)
    rw [show 0 + 2 * k = 2 * k from by ring]
    have h := tail_d0 (B + 3 * k) (A + k)
    rw [show B + 3 * k + 1 = (B + 3 * k) + 1 from by ring,
        show 2 * (B + 3 * k) + 2 = 2 * B + 2 + 3 * (2 * k) from by ring,
        show A + k + (B + 3 * k) + 1 = A + B + 1 + 2 * (2 * k) from by ring] at h; exact h
  · subst hk
    rw [show 2 * k + 1 = 1 + 2 * k from by ring]
    apply stepStar_trans (r3r2r2_chain_e0 k A B 1)
    rw [show 1 + 2 * k = 2 * k + 1 from by ring]
    have h := tail_d1 (B + 3 * k) (A + k)
    rw [show B + 3 * k + 1 = (B + 3 * k) + 1 from by ring,
        show 2 * (B + 3 * k) + 5 = 2 * B + 2 + 3 * (2 * k + 1) from by ring,
        show A + k + (B + 3 * k) + 3 = A + B + 1 + 2 * (2 * k + 1) from by ring] at h; exact h

theorem trans_c0 (a : ℕ) :
    ⟨a + 1, (0 : ℕ), 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 0, 5⟩ := by
  step fm; step fm; step fm; finish

-- r=0 phase: (a+1, 0, 0, 3k+3, 0) -> R5,R2 -> (a, 4, 0, 3k+2, 0) -> d_drain
-- R5: a+1 = _+1. fm matches R5 since b=0(no R1), e=0(no R2,R4), b=0(no R3).
-- After R5: (a, 2, 0, 3k+3, 1). R2: d=3k+3=(3k+2)+1, e=1=0+1.
-- After R2: (a, 4, 0, 3k+2, 0). d_drain(3k+2, a, 3).
theorem phase_r0 (a k : ℕ) :
    ⟨a + 1, (0 : ℕ), 0, 3 * k + 3, 0⟩ [fm]⊢⁺ ⟨a + 6 * k + 8, 0, 0, 0, 9 * k + 14⟩ := by
  rw [show 3 * k + 3 = (3 * k + 2) + 1 from by ring]
  step fm
  rw [show (3 * k + 2) + 1 = (3 * k + 2) + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show (4 : ℕ) = 3 + 1 from rfl]
  have hd := d_drain (3 * k + 2) a 3
  rw [show a + 3 + 1 + 2 * (3 * k + 2) = a + 6 * k + 8 from by ring,
      show 2 * 3 + 2 + 3 * (3 * k + 2) = 9 * k + 14 from by ring] at hd; exact hd

-- r=1 phase: (a+1, 0, 1, 3k, 0) -> R5 -> (a, 2, 1, 3k, 1) -> R1 -> (a, 1, 0, 3k+1, 1) -> R2 -> (a, 3, 0, 3k, 0)
-- Use step_stepStar with simp [fm] for R5 since d = 3*k is opaque
theorem phase_r1 (a k : ℕ) :
    ⟨a + 1, (0 : ℕ), 1, 3 * k, 0⟩ [fm]⊢⁺ ⟨a + 6 * k + 3, 0, 0, 0, 9 * k + 6⟩ := by
  apply step_stepStar_stepPlus
    (show (⟨a + 1, (0 : ℕ), 1, 3 * k, 0⟩ : Q) [fm]⊢ ⟨a, 2, 1, 3 * k, 1⟩ from by simp [fm])
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show 3 * k + 1 = (3 * k) + 1 from by ring, show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show (3 : ℕ) = 2 + 1 from rfl]
  have hd := d_drain (3 * k) a 2
  rw [show a + 2 + 1 + 2 * (3 * k) = a + 6 * k + 3 from by ring,
      show 2 * 2 + 2 + 3 * (3 * k) = 9 * k + 6 from by ring] at hd; exact hd

-- r=2 phase: (a+1, 0, 2, 3k, 0) -> R5 -> (a, 2, 2, 3k, 1) -> R1 -> (a, 1, 1, 3k+1, 1)
-- -> R1 -> (a, 0, 0, 3k+2, 1) -> R2 -> (a, 2, 0, 3k+1, 0) -> d_drain(3k+1, a, 1)
theorem phase_r2 (a k : ℕ) :
    ⟨a + 1, (0 : ℕ), 2, 3 * k, 0⟩ [fm]⊢⁺ ⟨a + 6 * k + 4, 0, 0, 0, 9 * k + 7⟩ := by
  apply step_stepStar_stepPlus
    (show (⟨a + 1, (0 : ℕ), 2, 3 * k, 0⟩ : Q) [fm]⊢ ⟨a, 2, 2, 3 * k, 1⟩ from by simp [fm])
  rw [show (2 : ℕ) = (0 + 1) + 1 from rfl, show (0 + 1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show 3 * k + 1 = (3 * k) + 1 from by ring, show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show (3 * k) + 1 + 1 = ((3 * k) + 1) + 1 from by ring, show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  have hd := d_drain (3 * k + 1) a 1
  rw [show a + 1 + 1 + 2 * (3 * k + 1) = a + 6 * k + 4 from by ring,
      show 2 * 1 + 2 + 3 * (3 * k + 1) = 9 * k + 7 from by ring] at hd; exact hd

-- r=3 phase: (a+1, 0, 3, 3k, 0) -> 8 steps -> (a+1, 4, 0, 3k, 0) -> d_drain(3k, a+1, 3)
theorem phase_r3 (a k : ℕ) :
    ⟨a + 1, (0 : ℕ), 3, 3 * k, 0⟩ [fm]⊢⁺ ⟨a + 6 * k + 5, 0, 0, 0, 9 * k + 8⟩ := by
  apply step_stepStar_stepPlus
    (show (⟨a + 1, (0 : ℕ), 3, 3 * k, 0⟩ : Q) [fm]⊢ ⟨a, 2, 3, 3 * k, 1⟩ from by simp [fm])
  rw [show (3 : ℕ) = (1 + 1) + 1 from rfl, show (1 + 1 : ℕ) = (0 + 1) + 1 from rfl,
      show (0 + 1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show 3 * k + 1 = (3 * k) + 1 from by ring, show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  -- (a, 0, 1, (3k)+1+1, 1). R2 (d = ((3k)+1)+1, e = 0+1)
  rw [show (3 * k) + 1 + 1 = ((3 * k) + 1) + 1 from by ring, show (1 : ℕ) = 0 + 1 from rfl,
      show (0 + 1 : ℕ) = 0 + 1 from rfl]
  step fm
  -- (a, 2, 1, (3k)+1, 0). R1 (b=1+1, c=0+1)
  apply stepStar_trans (step_stepStar (show (⟨a, 2, 1, (3 * k) + 1, (0 : ℕ)⟩ : Q) [fm]⊢ ⟨a, 1, 0, (3 * k) + 1 + 1, 0⟩ from by simp [fm]))
  -- (a, 1, 0, (3k)+1+1, 0). R3 (b=0+1)
  rw [show (3 * k) + 1 + 1 = (3 * k + 1) + 1 from by ring]
  step fm
  -- (a+1, 0, 0, (3k+1)+1, 2). R2 (d = (3k+1)+1, e = 2 = 1+1)
  rw [show (3 * k + 1) + 1 = (3 * k + 1) + 1 from rfl, show (2 : ℕ) = (1 : ℕ) + 1 from rfl]
  step fm
  -- (a+1, 2, 0, 3k+1, 1). R2 (d = (3k)+1, e = 0+1)
  rw [show 3 * k + 1 = (3 * k) + 1 from by ring, show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  -- (a+1, 4, 0, 3k, 0). d_drain(3k, a+1, 3).
  rw [show (4 : ℕ) = 3 + 1 from rfl]
  have hd := d_drain (3 * k) (a + 1) 3
  rw [show (a + 1) + 3 + 1 + 2 * (3 * k) = a + 6 * k + 5 from by ring,
      show 2 * 3 + 2 + 3 * (3 * k) = 9 * k + 8 from by ring] at hd; exact hd

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e⟩ ∧ e ≤ 4 * a + 3)
  · intro q ⟨a, e, hq, hinv⟩; subst hq
    rcases e with _ | e
    · exact ⟨_, ⟨a + 1, 5, rfl, by omega⟩, trans_c0 a⟩
    · have ⟨k, r, hr, hkr⟩ : ∃ k r, r < 4 ∧ e + 1 = 4 * k + r :=
        ⟨(e + 1) / 4, (e + 1) % 4, Nat.mod_lt _ (by omega), by omega⟩
      have hak : k ≤ a := by omega
      obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hak
      -- a = a' + k. Lean may have k + a' instead.
      -- Helper to build stepStar to (a'+1, 0, R, 3k, 0) for any R
      have mk_he : ∀ R, e + 1 = R + 4 * k →
          ⟨k + a' + 1, (0 : ℕ), 0, 0, e + 1⟩ [fm]⊢* ⟨a' + 1, 0, R, 3 * k, 0⟩ := by
        intro R hR; rw [hR]
        apply stepStar_trans (e_to_c (R + 4 * k) (k + a' + 1) 0)
        rw [show 0 + (R + 4 * k) = R + 4 * k from by ring,
            show k + a' + 1 = (a' + 1) + k from by ring]
        have h := six_step_drain k (a' + 1) R 0
        rw [show 0 + 3 * k = 3 * k from by ring] at h; exact h
      rcases r with _ | _ | _ | _ | r
      · -- r=0: e+1 = 4k. Need k >= 1.
        rcases k with _ | k
        · omega
        · have he := mk_he 0 (by omega)
          refine ⟨_, ⟨a' + 6 * k + 7, 9 * k + 14, rfl, by omega⟩, ?_⟩
          apply stepStar_stepPlus_stepPlus
          · convert he using 3
          · convert phase_r0 a' k using 3
      · -- r=1
        have he := mk_he 1 (by omega)
        exact ⟨_, ⟨a' + 6 * k + 2, 9 * k + 6, rfl, by omega⟩,
          stepStar_stepPlus_stepPlus he (phase_r1 a' k)⟩
      · -- r=2
        have he := mk_he 2 (by omega)
        exact ⟨_, ⟨a' + 6 * k + 3, 9 * k + 7, rfl, by omega⟩,
          stepStar_stepPlus_stepPlus he (phase_r2 a' k)⟩
      · -- r=3
        have he := mk_he 3 (by omega)
        exact ⟨_, ⟨a' + 6 * k + 4, 9 * k + 8, rfl, by omega⟩,
          stepStar_stepPlus_stepPlus he (phase_r3 a' k)⟩
      · omega
  · exact ⟨0, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1502
