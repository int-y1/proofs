import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #537: [28/15, 9/2, 11/3, 5/847, 14/11]

Vector representation:
```
 2 -1 -1  1  0
-1  2  0  0  0
 0 -1  0  0  1
 0  0  1 -1 -2
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_537

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: (0, 0, c, d+k, e+2*k) →* (0, 0, c+k, d, e)
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d+k, e+2*k⟩ [fm]⊢* ⟨0, 0, c+k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring,
      show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R2 drain: (a, b, 0, D, f) →* (0, b+2*a, 0, D, f)
theorem r2_drain : ∀ a, ∀ b D f, ⟨a, b, 0, D, f⟩ [fm]⊢* ⟨0, b+2*a, 0, D, f⟩ := by
  intro a; induction' a with a ih <;> intro b D f
  · exists 0
  rw [show (a + 1 : ℕ) = a + 1 from rfl]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3 drain: (0, b, 0, D, f) →* (0, 0, 0, D, f+b)
theorem r3_drain : ∀ b, ∀ D f, ⟨0, b, 0, D, f⟩ [fm]⊢* ⟨0, 0, 0, D, f+b⟩ := by
  intro b; induction' b with b ih <;> intro D f
  · exists 0
  rw [show (b + 1 : ℕ) = b + 1 from rfl]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R1R1R2 chain: (A, 2, c+2*k, D, f) →* (A+3*k, 2, c, D+2*k, f)
theorem r1r1r2_chain : ∀ k, ∀ A D f c,
    ⟨A, 2, c+2*k, D, f⟩ [fm]⊢* ⟨A+3*k, 2, c, D+2*k, f⟩ := by
  intro k; induction' k with k ih <;> intro A D f c
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
      show D + 2 * (k + 1) = (D + 2 * k) + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- Even d: full transition from (0,0,0,d,e) to (0,0,0,d+1,e+d+1) when d=2k+2, e>=2d+1
-- (0,0,0,2k+2,f+4k+5) →⁺ (0,0,0,2k+3,f+6k+8)
-- Phase 1: R4 (2k+2 times): → (0,0,2k+2,0,f+1)
-- Phase 2: R5+R2: → (0,2,2k+2,1,f)
-- Phase 3: R1R1R2 (k+1 rounds, c_rem=0): (0,2,0+2*(k+1),1,f) →* (3k+3,2,0,2k+3,f)
-- Phase 4: R2 drain (3k+3 steps): → (0,6k+8,0,2k+3,f)
-- Phase 5: R3 drain (6k+8 steps): → (0,0,0,2k+3,f+6k+8)
theorem even_trans {k f : ℕ} :
    ⟨0, 0, 0, 2*k+2, f+4*k+5⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*k+3, f+6*k+8⟩ := by
  -- R4 chain
  have h1 := r4_chain (2*k+2) 0 0 (f+1)
  rw [Nat.zero_add, show (f+1) + 2*(2*k+2) = f+4*k+5 from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  -- R5 + R2
  step fm; step fm
  -- R1R1R2 chain: need to rewrite 2*k+2 as 0 + 2*(k+1) in the goal
  -- Goal should be: (0, 2, 2*k+2, 1, f) [fm]⊢* ...
  -- We use r1r1r2_chain (k+1) 0 1 f 0 which gives:
  -- (0, 2, 0+2*(k+1), 1, f) →* (0+3*(k+1), 2, 0, 1+2*(k+1), f)
  have h2 := r1r1r2_chain (k+1) 0 1 f 0
  rw [Nat.zero_add, show (0:ℕ)+3*(k+1) = 3*k+3 from by ring,
      show (1:ℕ)+2*(k+1) = 2*k+3 from by ring] at h2
  -- h2 : (0, 2, 2*(k+1), 1, f) →* (3*k+3, 2, 0, 2*k+3, f)
  -- But goal has 2*k+2, and h2 has 2*(k+1). These are definitionally equal.
  apply stepStar_trans h2
  -- R2 drain
  apply stepStar_trans (r2_drain (3*k+3) 2 (2*k+3) f)
  -- R3 drain
  apply stepStar_trans (r3_drain (2+2*(3*k+3)) (2*k+3) f)
  ring_nf; finish

-- Odd d: (0,0,0,2k+1,f+4k+3) →⁺ (0,0,0,2k+2,f+6k+5)
-- Phase 1: R4 (2k+1 times): → (0,0,2k+1,0,f+1)
-- Phase 2: R5+R2: → (0,2,2k+1,1,f)
-- Phase 3: R1R1R2 (k rounds, c_rem=1): (0,2,1+2*k,1,f) →* (3k,2,1,2k+1,f)
-- Phase 3b: R1: → (3k+2,1,0,2k+2,f)
-- Phase 4: R2 drain (3k+2 steps): → (0,6k+5,0,2k+2,f)
-- Phase 5: R3 drain: → (0,0,0,2k+2,f+6k+5)
theorem odd_trans {k f : ℕ} :
    ⟨0, 0, 0, 2*k+1, f+4*k+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*k+2, f+6*k+5⟩ := by
  -- R4 chain
  have h1 := r4_chain (2*k+1) 0 0 (f+1)
  rw [Nat.zero_add, show (f+1) + 2*(2*k+1) = f+4*k+3 from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  -- R5 + R2
  step fm; step fm
  -- R1R1R2 chain with c_rem=1
  have h2 := r1r1r2_chain k 0 1 f 1
  rw [show (0:ℕ)+3*k = 3*k from by ring] at h2
  -- h2 : (0, 2, 1+2*k, 1, f) →* (3*k, 2, 1, 1+2*k, f)
  -- Goal has 2*k+1; rewrite to 1+2*k to match h2
  rw [show (2*k+1 : ℕ) = 1 + 2*k from by ring]
  apply stepStar_trans h2
  -- One more R1: (3*k, 2, 1, 1+2*k, f): b=2>=1, c=1>=1 → R1 fires
  rw [show (2:ℕ) = 1+1 from rfl, show (1:ℕ) = 0+1 from rfl]
  step fm
  -- After R1: (3*k+2, 1, 0, 1+2*k+1, f). Normalize d.
  rw [show 1 + 2 * k + 1 = 2*k+2 from by ring]
  -- R2 drain
  apply stepStar_trans (r2_drain (3*k+2) 1 (2*k+2) f)
  -- R3 drain
  apply stepStar_trans (r3_drain (1+2*(3*k+2)) (2*k+2) f)
  ring_nf; finish

-- Special case d=1: (0,0,0,1,f+3) →⁺ (0,0,0,2,f+5)
-- R4: (0,0,0,1,f+3) → (0,0,1,0,f+1)
-- R5: → (1,0,1,1,f). R2: → (0,2,1,1,f). R1: → (2,1,0,2,f).
-- R2 drain (2): → (0,5,0,2,f). R3 drain (5): → (0,0,0,2,f+5).
theorem d1_trans {f : ℕ} : ⟨0, 0, 0, 1, f+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2, f+5⟩ := by
  have h1 := r4_chain 1 0 0 (f+1)
  rw [Nat.zero_add, show (f+1)+2*1 = f+3 from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  step fm; step fm
  rw [show (1:ℕ) = 0+1 from rfl]
  step fm
  apply stepStar_trans (r2_drain 2 1 2 f)
  apply stepStar_trans (r3_drain 5 2 f)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 1 ∧ e ≥ 2 * d + 1)
  · intro c ⟨d, e, hq, hd, he⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d even: d = K + K = 2*K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨f, rfl⟩ : ∃ f, e = f + 4 * k + 5 := ⟨e - 4 * k - 5, by omega⟩
      exact ⟨⟨0, 0, 0, 2*k+3, f+6*k+8⟩,
        ⟨2*k+3, f+6*k+8, rfl, by omega, by omega⟩, even_trans⟩
    · -- d odd: d = 2*K+1
      subst hK
      rcases K with _ | K'
      · -- K=0, d=1
        obtain ⟨f, rfl⟩ : ∃ f, e = f + 3 := ⟨e - 3, by omega⟩
        exact ⟨⟨0, 0, 0, 2, f+5⟩,
          ⟨2, f+5, rfl, by omega, by omega⟩, d1_trans⟩
      · -- K=K'+1, d=2*(K'+1)+1=2*K'+3
        obtain ⟨f, rfl⟩ : ∃ f, e = f + 4 * (K'+1) + 3 := ⟨e - 4*(K'+1) - 3, by omega⟩
        exact ⟨⟨0, 0, 0, 2*(K'+1)+2, f+6*(K'+1)+5⟩,
          ⟨2*(K'+1)+2, f+6*(K'+1)+5, rfl, by omega, by omega⟩, odd_trans⟩
  · exact ⟨1, 3, rfl, by omega, by omega⟩
