import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #232: [11/105, 18/5, 25/33, 49/2, 5/7]

Vector representation:
```
 0 -1 -1 -1  1
 1  2 -1  0  0
 0 -1  2  0 -1
-1  0  0  2  0
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_232

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: a → d
theorem a_to_d : ∀ k a b d, ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d+2*k, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Inner loop: R3,R1,R2 reducing d by 1 and increasing a by 1
-- Needs e >= 1 (written as e+1) and d >= k (written as d+k)
-- State: (a, 2, 0, d+k, e+1)
-- R3 fires because b=2=1+1 >= 1 and e+1 >= 1 (and c=0, so R1,R2 don't fire)
-- After R3: (a, 1, 2, d+k, e)
-- R1 fires because b=1>=1, c=2>=1, d+k>=1 (when k>=1, written as d+(k-1)+1)
-- After R1: (a, 0, 1, d+k-1, e+1)
-- R2 fires because c=1>=1 (b=0 so R1 can't fire)
-- After R2: (a+1, 2, 0, d+k-1, e+1)
theorem inner_loop : ∀ k a d e, ⟨a, 2, 0, d+k, e+1⟩ [fm]⊢* ⟨a+k, 2, 0, d, e+1⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    -- State: (a, 1+1, 0, (d+k)+1, e+1). R3 matches: b+1=1+1, e+1.
    step fm
    -- After R3: (a, 1, 0+2, (d+k)+1, e) -> simp -> (a, 1, 2, d+k+1, e)
    -- R1 matches: b+1=1, c+1=2=1+1, d+1=(d+k)+1... but is d+k+1 in form d'+1?
    -- After simp [Nat.succ_eq_add_one, Nat.reduceAdd], it should be d+k+1 = (d+k)+1?
    -- Actually Nat.succ_eq_add_one converts Nat.succ to +1.
    -- The 2 became 0+2 after R3 output (c+2 where c=0), then simp: 0+2=2. Hmm.
    -- Let me check: R3 output is (a, b, c+2, d, e) where b=1, c=0. So (a, 1, 0+2, ...).
    -- After `simp only [Nat.succ_eq_add_one, Nat.reduceAdd]`: 0+2 = 2.
    -- So state is (a, 1, 2, d+k+1, e). For R1: need b+1=1 (b=0? no b=1), c+1, d+1.
    -- Wait R1 pattern is (a, b+1, c+1, d+1, e). State: (a, 1, 2, d+k+1, e).
    -- b+1=1 means b=0. 1=0+1 ✓. c+1=2 means c=1. 2=1+1 ✓. d+1=d+k+1 means d'=d+k.
    -- d+k+1 = (d+k)+1 ✓. So R1 should match.
    -- But does step fm see it that way? 1 needs to be in form b+1, i.e., 0+1.
    -- After simp, 1 is just 1, not 0+1. But Lean's pattern matching on Nat.succ should still work.
    step fm
    -- After R1: (a, 0, 1, d+k, e+1).
    -- For R2: c+1=1 means c=0. 1=0+1. R2 pattern: (a, b, c+1, d, e).
    -- R1 doesn't match because b=0. So R2 fires.
    step fm
    -- After R2: (a+1, 2, 0, d+k, e+1).
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Tail expand: R3,R2,R2 reducing e and increasing a,b
-- (A, b+2, 0, 0, e+k) ⊢* (A+2*k, b+3*k+2, 0, 0, e)
theorem tail_expand : ∀ k a b e, ⟨a, b+2, 0, 0, e+k⟩ [fm]⊢* ⟨a+2*k, b+3*k+2, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show b + 2 = (b + 1) + 1 from by ring]
    -- State: (a, (b+1)+1, 0, 0, (e+k)+1). R3 matches: b+1=(b+1), e+1=(e+k).
    step fm
    -- After R3: (a, b+1, 2, 0, e+k). R2: c+1=2=1+1.
    -- But R1 first: b+1>=1, c+1: 2=1+1 so c=1. d+1: d=0. No d>=1. R1 fails.
    -- R2: c+1=2. Actually c=2, so c+1=3? No. The state has c=2 (from c+2 where c=0).
    -- Wait: R3 result is (a, b, c+2, d, e). With b=b+1-1=b+1-1... hmm.
    -- R3 match: (a, b'+1, c', d, e'+1). b'+1 = (b+1)+1, so b'=b+1. c'=0. d=0. e'+1=(e+k)+1, e'=e+k.
    -- R3 result: (a, b', c'+2, d, e') = (a, b+1, 0+2, 0, e+k) = (a, b+1, 2, 0, e+k).
    -- After simp: (a, b+1, 2, 0, e+k).
    -- Now R1: (a, b'+1, c'+1, d'+1, e'). b'+1 = b+1, c'+1 = 2 = 1+1, d'+1: d=0. No. R1 fails.
    -- R2: (a, b', c'+1, d, e'). c'+1 = 2 = 1+1. So c'=1. Matches.
    -- R2 result: (a+1, b'+2, c', d, e') where b'=b+1, c'=1, d=0, e'=e+k.
    -- = (a+1, b+1+2, 1, 0, e+k) = (a+1, b+3, 1, 0, e+k).
    step fm
    -- After R2: (a+1, b+3, 1, 0, e+k).
    -- R1: b+3>=1, c=1>=1 but d=0. Fail.
    -- R2: c+1=1=0+1. So c'=0. Result: (a+2, b+3+2, 0, 0, e+k) = (a+2, b+5, 0, 0, e+k).
    step fm
    -- After R2: (a+2, b+5, 0, 0, e+k).
    -- Need to apply IH: (a+2, (b+3)+2, 0, 0, e+k) ⊢* (a+2+2*k, (b+3)+3*k+2, 0, 0, e)
    apply stepStar_trans (ih (a + 2) (b + 3) e)
    ring_nf; finish

-- Drain period: R1,R1,R3 loop
-- (0, 3*k, 2, d+2*k, e) ⊢* (0, 0, 2, d, e+k)
theorem drain_period : ∀ k d e, ⟨0, 3*k, 2, d+2*k, e⟩ [fm]⊢* ⟨0, 0, 2, d, e+k⟩ := by
  intro k; induction k with
  | zero => intro d e; simp; exists 0
  | succ k ih =>
    intro d e
    rw [show 3 * (k + 1) = 3 * k + 2 + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    -- State: (0, (3*k+2)+1, 1+1, (d+2*k+1)+1, e). R1 matches.
    step fm
    -- After R1: (0, 3*k+2, 1, d+2*k+1, e+1). Hmm, let me check.
    -- R1: (a, b+1, c+1, d+1, e) => (a, b, c, d, e+1).
    -- a=0, b+1=3*k+2+1 so b=3*k+2, c+1=1+1=2 so c=1, d+1=(d+2*k+1)+1 so d'=d+2*k+1, e=e.
    -- Result: (0, 3*k+2, 1, d+2*k+1, e+1). Hmm after simp it's the same.
    -- Wait: result is (a, b, c, d, e+1) = (0, 3*k+2, 1, d+2*k+1, e+1).
    -- After simp: same.
    -- Now: need to match R1 again. (0, (3*k+1)+1, (0)+1, (d+2*k)+1, e+1).
    -- 3*k+2 = (3*k+1)+1. 1 = 0+1. d+2*k+1 = (d+2*k)+1. e+1.
    rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring,
        show d + 2 * k + 1 = (d + 2 * k) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    -- After R1: (0, 3*k+1, 0, d+2*k, e+1+1).
    -- Now R3: (0, (3*k)+1, 0, d+2*k, (e+1)+1). b+1=3*k+1, e+1=e+1+1.
    -- 3*k+1 = (3*k)+1. e+1+1 = (e+1)+1.
    rw [show 3 * k + 1 = 3 * k + 1 from rfl]
    -- R3: (a, b+1, c, d, e+1). b+1=3*k+1... is 3*k+1 in form b'+1?
    -- 3*k+1 = (3*k) + 1. Yes if Lean sees it that way.
    -- Hmm, after Lean simplification, 3*k+1 should be Nat.add (3*k) 1 which matches b+1 with b=3*k.
    -- e+1+1: this is Nat.add (Nat.add e 1) 1. For e+1 pattern: e'+1 where e'=e+1.
    -- But we need the state in the form (a, b+1, c, d, e'+1).
    -- Let me just try step fm directly.
    step fm
    -- After R3: (0, 3*k, 0+2, d+2*k, e+1) = (0, 3*k, 2, d+2*k, e+1).
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- drain3: helper for clean drain
-- (0, 3*k+1, 1, d+2*k+1, e) ⊢* (0, 0, 0, d, e+k+1)
theorem drain3 : ∀ k d e, ⟨0, 3*k+1, 1, d+2*k+1, e⟩ [fm]⊢* ⟨0, 0, 0, d, e+k+1⟩ := by
  intro k; induction k with
  | zero =>
    intro d e
    rw [show 3 * 0 + 1 = 0 + 1 from by ring,
        show d + 2 * 0 + 1 = d + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    -- State: (0, 0+1, 0+1, d+1, e). R1 matches.
    step fm
    -- After R1: (0, 0, 0, d, e+1).
    ring_nf; finish
  | succ k ih =>
    intro d e
    -- State: (0, 3*(k+1)+1, 1, d+2*(k+1)+1, e)
    -- = (0, 3*k+4, 1, d+2*k+3, e)
    -- R1: need b+1, c+1, d+1. b+1=3*k+4=(3*k+3)+1. c+1=1=0+1. d+1=d+2*k+3=(d+2*k+2)+1.
    rw [show 3 * (k + 1) + 1 = (3 * k + 3) + 1 from by ring,
        show d + 2 * (k + 1) + 1 = (d + 2 * k + 2) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    -- After R1: (0, 3*k+3, 0, d+2*k+2, e+1).
    -- R3: b+1=3*k+3=(3*k+2)+1. e+1. c=0.
    rw [show 3 * k + 3 = (3 * k + 2) + 1 from by ring]
    step fm
    -- After R3: (0, 3*k+2, 2, d+2*k+2, e).
    -- R1: b+1=(3*k+1)+1, c+1=2=1+1, d+1=(d+2*k+1)+1.
    rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring,
        show d + 2 * k + 2 = (d + 2 * k + 1) + 1 from by ring]
    step fm
    -- After R1: (0, 3*k+1, 1, d+2*k+1, e+1).
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- Grind loop: R1,R3,R2 reducing d and increasing a
-- (a, 2, 1, d+k, e) ⊢* (a+k, 2, 1, d, e)
theorem grind : ∀ k a d e, ⟨a, 2, 1, d+k, e⟩ [fm]⊢* ⟨a+k, 2, 1, d, e⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    -- State: (a, 1+1, 0+1, (d+k)+1, e). R1 matches.
    step fm
    -- After R1: (a, 1, 0, d+k, e+1).
    -- R3: b+1=1=0+1, e+1. c=0.
    step fm
    -- After R3: (a, 0, 2, d+k, e).
    -- R2: c+1=2=1+1.
    step fm
    -- After R2: (a+1, 2, 1, d+k, e).
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Main transition: (0,0,0,D+1,E+1) ⊢⁺ (0,0,0,4*D+6*E+6,E+3)
theorem main_trans (D E : ℕ) :
    ⟨0, 0, 0, D+1, E+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*D+6*E+6, E+3⟩ := by
  -- Phase 1: R5 (gives stepPlus)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 0, 1, D, E + 1⟩)
  · show fm ⟨0, 0, 0, D + 1, E + 1⟩ = some ⟨0, 0, 1, D, E + 1⟩; simp [fm]
  -- Phase 1b: R2
  step fm
  -- State: (1, 2, 0, D, E+1)
  -- Phase 2: inner loop D times: (1, 2, 0, D, E+1) -> (D+1, 2, 0, 0, E+1)
  apply stepStar_trans (c₂ := ⟨D + 1, 2, 0, 0, E + 1⟩)
  · have h := inner_loop D 1 0 E
    rw [show (0 : ℕ) + D = D from by ring,
        show 1 + D = D + 1 from by ring] at h; exact h
  -- Phase 3: tail expand (E+1) times: (D+1, 2, 0, 0, E+1) -> (D+2*E+3, 3*E+5, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨D + 2 * E + 3, 3 * E + 5, 0, 0, 0⟩)
  · have h := tail_expand (E + 1) (D + 1) 0 0
    rw [show (0 : ℕ) + 2 = 2 from by ring,
        show (0 : ℕ) + (E + 1) = E + 1 from by ring,
        show D + 1 + 2 * (E + 1) = D + 2 * E + 3 from by ring,
        show 0 + 3 * (E + 1) + 2 = 3 * E + 5 from by ring] at h; exact h
  -- Phase 4: a_to_d: (D+2*E+3, 3*E+5, 0, 0, 0) -> (0, 3*E+5, 0, 2*D+4*E+6, 0)
  apply stepStar_trans (c₂ := ⟨0, 3 * E + 5, 0, 2 * D + 4 * E + 6, 0⟩)
  · have h := a_to_d (D + 2 * E + 3) 0 (3 * E + 5) 0
    rw [show (0 : ℕ) + (D + 2 * E + 3) = D + 2 * E + 3 from by ring,
        show 0 + 2 * (D + 2 * E + 3) = 2 * D + 4 * E + 6 from by ring] at h; exact h
  -- Phase 5: incomplete drain setup (3 steps)
  -- (0, 3*E+5, 0, 2*D+4*E+6, 0)
  -- R5: (0, 3*E+5, 1, 2*D+4*E+5, 0)
  rw [show 2 * D + 4 * E + 6 = (2 * D + 4 * E + 5) + 1 from by ring]
  step fm
  -- R1: need b+1, c+1, d+1. 3*E+5=(3*E+4)+1. 1=0+1. 2*D+4*E+5=(2*D+4*E+4)+1.
  rw [show 3 * E + 5 = (3 * E + 4) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * D + 4 * E + 5 = (2 * D + 4 * E + 4) + 1 from by ring]
  step fm
  -- After R1: (0, 3*E+4, 0, 2*D+4*E+4, 1)
  -- R3: b+1=(3*E+3)+1. e+1=1=0+1. But wait, e=1 from R1 result e+1.
  -- State is (0, 3*E+4, 0, 2*D+4*E+4, 0+1). R3: b+1=(3*E+3)+1, e+1=0+1.
  rw [show 3 * E + 4 = (3 * E + 3) + 1 from by ring]
  step fm
  -- After R3: (0, 3*E+3, 2, 2*D+4*E+4, 0)
  -- Phase 5b: drain_period (E+1) times
  apply stepStar_trans (c₂ := ⟨0, 0, 2, 2 * D + 2 * E + 2, E + 1⟩)
  · have h := drain_period (E + 1) (2 * D + 2 * E + 2) 0
    rw [show 3 * (E + 1) = 3 * E + 3 from by ring,
        show 2 * D + 2 * E + 2 + 2 * (E + 1) = 2 * D + 4 * E + 4 from by ring,
        show (0 : ℕ) + (E + 1) = E + 1 from by ring] at h; exact h
  -- Phase 6a: R2: (0, 0, 2, 2*D+2*E+2, E+1) -> (1, 2, 1, 2*D+2*E+2, E+1)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  -- Phase 6b: grind (2*D+2*E+2) times
  apply stepStar_trans (c₂ := ⟨2 * D + 2 * E + 3, 2, 1, 0, E + 1⟩)
  · have h := grind (2 * D + 2 * E + 2) 1 0 (E + 1)
    rw [show (0 : ℕ) + (2 * D + 2 * E + 2) = 2 * D + 2 * E + 2 from by ring,
        show 1 + (2 * D + 2 * E + 2) = 2 * D + 2 * E + 3 from by ring] at h; exact h
  -- Phase 6c: R2: (2*D+2*E+3, 2, 1, 0, E+1) -> (2*D+2*E+4, 4, 0, 0, E+1)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- Phase 7: tail expand (E+1) times
  apply stepStar_trans (c₂ := ⟨2 * D + 4 * E + 6, 3 * E + 7, 0, 0, 0⟩)
  · have h := tail_expand (E + 1) (2 * D + 2 * E + 4) 2 0
    rw [show (2 : ℕ) + 2 = 4 from by ring,
        show (0 : ℕ) + (E + 1) = E + 1 from by ring,
        show 2 * D + 2 * E + 4 + 2 * (E + 1) = 2 * D + 4 * E + 6 from by ring,
        show 2 + 3 * (E + 1) + 2 = 3 * E + 7 from by ring] at h; exact h
  -- Phase 8: a_to_d: -> (0, 3*E+7, 0, 4*D+8*E+12, 0)
  apply stepStar_trans (c₂ := ⟨0, 3 * E + 7, 0, 4 * D + 8 * E + 12, 0⟩)
  · have h := a_to_d (2 * D + 4 * E + 6) 0 (3 * E + 7) 0
    rw [show (0 : ℕ) + (2 * D + 4 * E + 6) = 2 * D + 4 * E + 6 from by ring,
        show 0 + 2 * (2 * D + 4 * E + 6) = 4 * D + 8 * E + 12 from by ring] at h; exact h
  -- Phase 9: clean drain via R5 + drain3
  -- R5: (0, 3*E+7, 0, 4*D+8*E+12, 0) -> (0, 3*E+7, 1, 4*D+8*E+11, 0)
  rw [show 4 * D + 8 * E + 12 = (4 * D + 8 * E + 11) + 1 from by ring]
  step fm
  -- drain3 with k=E+2: (0, 3*(E+2)+1, 1, d+2*(E+2)+1, 0) ⊢* (0, 0, 0, d, (E+2)+1)
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 4 * D + 6 * E + 6, E + 3⟩)
  · have h := drain3 (E + 2) (4 * D + 6 * E + 6) 0
    rw [show 3 * (E + 2) + 1 = 3 * E + 7 from by ring,
        show 4 * D + 6 * E + 6 + 2 * (E + 2) + 1 = 4 * D + 8 * E + 11 from by ring,
        show (0 : ℕ) + (E + 2) + 1 = E + 3 from by ring] at h; exact h
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩) (by execute fm 20)
  show ¬halts fm ⟨(0 : ℕ), 0, 0, 1 + 1, 1 + 1⟩
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨D, E⟩ ↦ ⟨0, 0, 0, D + 1, E + 1⟩) ⟨1, 1⟩
  intro ⟨D, E⟩
  refine ⟨⟨4 * D + 6 * E + 5, E + 2⟩, ?_⟩
  show ⟨0, 0, 0, D + 1, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * D + 6 * E + 5 + 1, E + 2 + 1⟩
  rw [show 4 * D + 6 * E + 5 + 1 = 4 * D + 6 * E + 6 from by ring,
      show E + 2 + 1 = E + 3 from by ring]
  exact main_trans D E

end Sz22_2003_unofficial_232
