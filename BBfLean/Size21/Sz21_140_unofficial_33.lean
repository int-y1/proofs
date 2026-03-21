import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #33: [35/6, 121/2, 4/55, 3/7, 6/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_33

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: d → b (when a=0, c=0)
theorem d_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b d; exists 0
  | succ k ih =>
    intro b d
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R1,R1,R3 interleaved rounds: 3 steps per round
-- After k rounds: (2, b+2k, c, d, e+k) →* (2, b, c+k, d+2k, e)
theorem r1r1r3_rounds : ∀ k, ∀ b c d e, ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e⟩ := by
  intro k; induction k with
  | zero => intro b c d e; exists 0
  | succ k ih =>
    intro b c d e
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R1
    step fm  -- R1
    rw [show c + 2 = (c + 1) + 1 from by ring]
    step fm  -- R3
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- R3,R2,R2 chain: each cycle reduces c by 1, increases e by 3
-- (0, 0, c+k, d, e+k) →* (0, 0, c, d, e+4k)
theorem r3r2r2_chain : ∀ k, ∀ c d e, ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d, e+4*k⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R3
    step fm  -- R2
    step fm  -- R2
    rw [show e + k + 4 = (e + 4) + k from by ring]
    apply stepStar_trans (ih c d (e + 4))
    ring_nf; finish

-- Even n case (n = 2m):
-- (0, 0, 0, 2m+1, e+2m+2) →⁺ (0, 0, 0, 2m+2, e+4m+5)
theorem main_trans_even (m : ℕ) : ∀ e, ⟨0, 0, 0, 2*m+1, e+2*m+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+2, e+4*m+5⟩ := by
  intro e
  -- Phase 1: R4×(2m+1) → (0, 2m+1, 0, 0, e+2m+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*m+1, 0, 0, e+2*m+2⟩)
  · have h := @d_to_b (e+2*m+2) (2*m+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phases 2-4: R5, R1, R3 (3 steps)
  rw [show e + 2 * m + 2 = (e + 2 * m + 1) + 1 from by ring]
  step fm  -- R5: → (1, 2m+2, 0, 0, e+2m+1)
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm  -- R1: → (0, 2m+1, 1, 1, e+2m+1)
  rw [show e + 2 * m + 1 = (e + 2 * m) + 1 from by ring]
  step fm  -- R3: → (2, 2m+1, 0, 1, e+2m)
  -- Phase 5: m rounds of R1,R1,R3
  rw [show 2 * m + 1 = 1 + 2 * m from by ring,
      show e + 2 * m = (e + m) + m from by ring]
  apply stepStar_trans (r1r1r3_rounds m 1 0 1 (e+m))
  -- State: (2, 1, 0+m, 1+2m, e+m)
  -- Phase 6: R1
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm  -- R1: → (1, 0, m+1, 1+2m+1, e+m)
  -- Phase 7: R2
  step fm  -- R2: → (0, 0, m+1, 1+2m+1, e+m+2)
  -- State after step fm: (0, 0, 0+m+1, 1+2*m+1, e+m+2)
  -- Phase 8: (m+1) cycles of R3,R2,R2
  -- Need to rewrite to match r3r2r2_chain signature: (0, 0, c+k, d, e+k)
  -- c=0, k=m+1, d=1+2*m+1, e_base=e+1
  -- 0+m+1 matches c+k with c=0, k=m+1
  -- e+m+2 = (e+1)+(m+1)
  rw [show 0 + m + 1 = 0 + (m + 1) from by ring,
      show e + m + 2 = (e + 1) + (m + 1) from by ring]
  apply stepStar_trans (r3r2r2_chain (m+1) 0 (1+2*m+1) (e+1))
  ring_nf; finish

-- Odd n case (n = 2m+1):
-- (0, 0, 0, 2m+2, e+2m+3) →⁺ (0, 0, 0, 2m+3, e+4m+7)
theorem main_trans_odd (m : ℕ) : ∀ e, ⟨0, 0, 0, 2*m+2, e+2*m+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+3, e+4*m+7⟩ := by
  intro e
  -- Phase 1: R4×(2m+2) → (0, 2m+2, 0, 0, e+2m+3)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*m+2, 0, 0, e+2*m+3⟩)
  · have h := @d_to_b (e+2*m+3) (2*m+2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phases 2-4: R5, R1, R3
  rw [show e + 2 * m + 3 = (e + 2 * m + 2) + 1 from by ring]
  step fm  -- R5
  rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
  step fm  -- R1
  rw [show e + 2 * m + 2 = (e + 2 * m + 1) + 1 from by ring]
  step fm  -- R3
  -- Phase 5: (m+1) rounds of R1,R1,R3
  rw [show 2 * m + 2 = 0 + 2 * (m + 1) from by ring,
      show e + 2 * m + 1 = (e + m) + (m + 1) from by ring]
  apply stepStar_trans (r1r1r3_rounds (m+1) 0 0 1 (e+m))
  -- State: (2, 0, 0+(m+1), 1+2*(m+1), e+m)
  -- Phase 6: R2, R2
  step fm  -- R2
  step fm  -- R2
  -- State: (0, 0, 0+(m+1), 1+2*(m+1), e+m+2+2)
  rw [show e + m + 2 + 2 = (e + 3) + (m + 1) from by ring]
  apply stepStar_trans (r3r2r2_chain (m+1) 0 (1+2*(m+1)) (e+3))
  ring_nf; finish

-- Combined main transition
theorem main_trans : ∀ d e, ⟨0, 0, 0, d+1, e+d+2⟩ [fm]⊢⁺ ⟨0, 0, 0, d+2, e+2*d+5⟩ := by
  intro d e
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- d even: d = 2m (hm : d = m + m)
    subst hm
    have h := main_trans_even m e
    rw [show m + m + 1 = 2 * m + 1 from by ring,
        show e + (m + m) + 2 = e + 2 * m + 2 from by ring,
        show m + m + 2 = 2 * m + 2 from by ring,
        show e + 2 * (m + m) + 5 = e + 4 * m + 5 from by ring]
    exact h
  · -- d odd: d = 2m + 1
    subst hm
    have h := main_trans_odd m e
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show e + (2 * m + 1) + 2 = e + 2 * m + 3 from by ring,
        show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show e + 2 * (2 * m + 1) + 5 = e + 4 * m + 7 from by ring]
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1, 0, 0, 0, 0) →* (0, 0, 0, 1, 4) in 6 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 4⟩) (by execute fm 6)
  -- C(d, e) = (0, 0, 0, d+1, e+d+2), init = (0, 2) giving (0,0,0,1,4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 0, p.1+1, p.2+p.1+2⟩) ⟨0, 2⟩
  intro ⟨d, e⟩
  refine ⟨⟨d+1, e+d+2⟩, ?_⟩
  show ⟨0, 0, 0, d+1, e+d+2⟩ [fm]⊢⁺ ⟨0, 0, 0, d+1+1, e+d+2+(d+1)+2⟩
  rw [show d + 1 + 1 = d + 2 from by ring,
      show e + d + 2 + (d + 1) + 2 = e + 2 * d + 5 from by ring]
  exact main_trans d e

end Sz21_140_unofficial_33
