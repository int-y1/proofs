import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #246: [11/105, 9/55, 50/3, 49/2, 3/7]

Vector representation:
```
 0 -1 -1 -1  1
 0  2 -1  0 -1
 1 -1  2  0  0
-1  0  0  2  0
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_246

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Rule 3 fires B times: (A, B, C, 0, 0) ->* (A+B, 0, C+2B, 0, 0)
theorem pump : ∀ B A C, ⟨A, B, C, 0, 0⟩ [fm]⊢* ⟨A + B, 0, C + 2 * B, 0, 0⟩ := by
  intro B; induction B with
  | zero => intro A C; simp; exists 0
  | succ B ih =>
    intro A C
    rw [show A + (B + 1) = (A + 1) + B from by ring,
        show C + 2 * (B + 1) = (C + 2) + 2 * B from by ring]
    step fm
    apply stepStar_trans (ih (A + 1) (C + 2))
    ring_nf; finish

-- Rule 4 fires A times: (A, 0, C, D, 0) ->* (0, 0, C, D+2A, 0)
theorem deplete : ∀ A C D, ⟨A, 0, C, D, 0⟩ [fm]⊢* ⟨0, 0, C, D + 2 * A, 0⟩ := by
  intro A; induction A with
  | zero => intro C D; simp; exists 0
  | succ A ih =>
    intro C D
    rw [show D + 2 * (A + 1) = (D + 2) + 2 * A from by ring]
    step fm
    apply stepStar_trans (ih C (D + 2))
    ring_nf; finish

-- Initial drain: (0, 0, C+2, D+2, 0) ->* (0, 2, C, D, 0)
theorem init_drain (C D : ℕ) :
    ⟨0, 0, C + 2, D + 2, 0⟩ [fm]⊢* ⟨0, 2, C, D, 0⟩ := by
  rw [show D + 2 = (D + 1) + 1 from by ring,
      show C + 2 = (C + 1) + 1 from by ring]
  step fm
  rw [show C + 1 = (C + 1) from rfl,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  step fm; finish

-- Drain loop: (0, 2, X+3k, Y+2k, Z) ->* (0, 2, X, Y, Z+k)
theorem drain_loop : ∀ k X Y Z,
    ⟨0, 2, X + 3 * k, Y + 2 * k, Z⟩ [fm]⊢* ⟨0, 2, X, Y, Z + k⟩ := by
  intro k; induction k with
  | zero => intro X Y Z; simp; exists 0
  | succ k ih =>
    intro X Y Z
    rw [show X + 3 * (k + 1) = (X + 3 * k + 2) + 1 from by ring,
        show Y + 2 * (k + 1) = (Y + 2 * k + 1) + 1 from by ring]
    step fm
    rw [show X + 3 * k + 2 = (X + 3 * k + 1) + 1 from by ring,
        show Y + 2 * k + 1 = (Y + 2 * k) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    rw [show X + 3 * k + 1 = (X + 3 * k) + 1 from by ring,
        show (2 : ℕ) = 0 + 2 from by ring]
    step fm
    apply stepStar_trans (ih X Y (Z + 1))
    ring_nf; finish

-- Accumulation with b=2: (K, 2, 0, D, E) ->* (K+D, 2, 0, 0, E)
theorem accum_b2 : ∀ D K E,
    ⟨K, 2, 0, D, E⟩ [fm]⊢* ⟨K + D, 2, 0, 0, E⟩ := by
  intro D; induction D with
  | zero => intro K E; simp; exists 0
  | succ D ih =>
    intro K E
    rw [show K + (D + 1) = (K + 1) + D from by ring,
        show D + 1 = D + 1 from rfl]
    -- (K, 2, 0, D+1, E): b=2>=1, c=0, so rule 3: (K+1, 1, 2, D+1, E)
    step fm
    -- (K+1, 1, 2, D+1, E): rule 1 (b>=1,c>=1,d>=1): (K+1, 0, 1, D, E+1)
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    -- (K+1, 0, 1, D, E+1): rule 2 (c>=1,e>=1): (K+1, 2, 0, D, E)
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show E + 1 = E + 1 from rfl]
    step fm
    apply stepStar_trans (ih (K + 1) E)
    ring_nf; finish

-- Accumulation with c=2: (A, 0, 2, D, E+1) ->* (A+D, 0, 2, 0, E+1)
theorem accum_c2 : ∀ D A E,
    ⟨A, 0, 2, D, E + 1⟩ [fm]⊢* ⟨A + D, 0, 2, 0, E + 1⟩ := by
  intro D; induction D with
  | zero => intro A E; simp; exists 0
  | succ D ih =>
    intro A E
    rw [show A + (D + 1) = (A + 1) + D from by ring,
        show (2 : ℕ) = 1 + 1 from by ring,
        show E + 1 = E + 1 from rfl,
        show D + 1 = D + 1 from rfl]
    -- (A, 0, 2, D+1, E+1): rule 2 (c>=1,e>=1): (A, 2, 1, D+1, E)
    step fm
    -- (A, 2, 1, D+1, E): rule 1: (A, 1, 0, D, E+1)
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    -- (A, 1, 0, D, E+1): rule 3 (b>=1): (A+1, 0, 2, D, E+1)
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    apply stepStar_trans (ih (A + 1) E)
    ring_nf; finish

-- Endgame: (M, B0+2, 0, 0, 2k+2) ->* (M+k+1, B0+3k+5, 0, 0, 0)
theorem endgame : ∀ k M B0,
    ⟨M, B0 + 2, 0, 0, 2 * k + 2⟩ [fm]⊢* ⟨M + k + 1, B0 + 3 * k + 5, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero =>
    intro M B0; simp
    -- (M, B0+2, 0, 0, 2): rule 3 -> (M+1, B0+1, 2, 0, 2)
    rw [show B0 + 2 = (B0 + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    -- state: (M+(0+1), B0+1, 2, 0, 1+1)
    -- rule 2 (c>=1, e>=1): -> (M+1, B0+3, 1, 0, 1)
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    -- state: (M+(0+1), B0+1+2, 0+1, 0, 1)
    rw [show B0 + 1 + 2 = B0 + 3 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring,
        show (0 : ℕ) + 1 = 0 + 1 from by ring]
    step fm
    rw [show B0 + 3 + 2 = B0 + 5 from by ring]
    finish
  | succ k ih =>
    intro M B0
    -- (M, B0+2, 0, 0, 2(k+1)+2) = (M, B0+2, 0, 0, 2k+4)
    -- Step 1: rule 3: -> (M+1, B0+1, 2, 0, 2k+4)
    rw [show 2 * (k + 1) + 2 = (2 * k + 3) + 1 from by ring,
        show B0 + 2 = (B0 + 1) + 1 from by ring]
    step fm
    -- state: (M+(0+1), B0+1, 2, 0, (2*k+3)+1)
    -- Step 2: rule 2 (c=2>=1, e=2k+4>=1): -> (M+1, B0+3, 1, 0, 2k+3)
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    -- state: (M + 1, B0 + 3, 1, 0, 2*k+3)
    -- Step 3: rule 2 (c=1>=1, e=2k+3>=1): -> (M+1, B0+5, 0, 0, 2k+2)
    rw [show B0 + 1 + 2 = B0 + 3 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring,
        show 2 * k + 3 = (2 * k + 2) + 1 from by ring]
    step fm
    rw [show B0 + 3 + 2 = (B0 + 3) + 2 from by ring]
    apply stepStar_trans (ih (M + 1) (B0 + 3))
    ring_nf; finish

-- r=2 resolution: (0, 2, 2, D+3, E) ->* (1, 0, 2, D, E+2) in 4 steps
theorem r2_fix (D E : ℕ) :
    ⟨0, 2, 2, D + 3, E⟩ [fm]⊢* ⟨1, 0, 2, D, E + 2⟩ := by
  -- (0, 2, 2, D+3, E): rule 1 (b>=1,c>=1,d>=1): (0, 1, 1, D+2, E+1)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show D + 3 = (D + 2) + 1 from by ring]
  step fm
  -- (0, 1, 1, D+2, E+1): rule 1: (0, 0, 0, D+1, E+2)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show D + 2 = (D + 1) + 1 from by ring,
      show E + 1 = (E + 1) from rfl]
  step fm
  -- (0, 0, 0, D+1, E+2): rule 5 (d>=1): (0, 1, 0, D, E+2)
  rw [show D + 1 = D + 1 from rfl]
  step fm
  -- (0, 1, 0, D, E+2): rule 3 (b>=1): (1, 0, 2, D, E+2)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; finish

-- Convert (M, 0, 2, 0, E+2) ->* (M, 4, 0, 0, E)
theorem c2_to_b4 (M E : ℕ) :
    ⟨M, 0, 2, 0, E + 2⟩ [fm]⊢* ⟨M, 4, 0, 0, E⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show E + 2 = (E + 1) + 1 from by ring]
  -- rule 2 (c>=1, e>=1): -> (M, 2, 1, 0, E+1)
  step fm
  -- state after step fm + simp: (M, 2, 1, 0, E+1)
  -- The step produces (M, 0+2, 0+1, 0, E+1), then Nat.reduceAdd simplifies
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show E + 1 = E + 1 from rfl]
  -- rule 2 (c>=1, e>=1): -> (M, 4, 0, 0, E)
  step fm; finish

-- Main cycle Case 1: B ≡ 1 (mod 3), B = 3(m+1)+1, m ≥ 0
-- (A, 3(m+1)+1, 0, 0, 0) ->+ (A', 3(m+1)+2, 0, 0, 0)
theorem cycle_case1 (A m : ℕ) :
    ⟨A, 3 * m + 4, 0, 0, 0⟩ [fm]⊢⁺ ⟨2 * A + 3 * m + 3, 3 * m + 5, 0, 0, 0⟩ := by
  set B := 3 * m + 4
  set S := A + B
  -- First step (rule 3): (A, B, 0, 0, 0) -> (A+1, B-1, 2, 0, 0)
  rw [show B = (B - 1) + 1 from by omega]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- Now everything is stepStar
  -- Remaining pump: (A+1, B-1, 2, 0, 0) ->* (A+B, 0, 2B, 0, 0)
  apply stepStar_trans (pump (B - 1) (A + 1) 2)
  rw [show A + 1 + (B - 1) = S from by omega,
      show 2 + 2 * (B - 1) = 2 * B from by omega]
  -- Phase 2: deplete S times
  apply stepStar_trans (deplete S (2 * B) 0)
  rw [show (0 : ℕ) + 2 * S = 2 * S from by ring]
  -- Phase 3: init drain
  rw [show 2 * B = (2 * B - 2) + 2 from by omega,
      show 2 * S = (2 * S - 2) + 2 from by omega]
  apply stepStar_trans (init_drain (2 * B - 2) (2 * S - 2))
  -- Phase 4: drain loop
  rw [show 2 * B - 2 = 0 + 3 * (2 * m + 2) from by omega,
      show 2 * S - 2 = (2 * S - 2 - 2 * (2 * m + 2)) + 2 * (2 * m + 2) from by omega]
  apply stepStar_trans (drain_loop (2 * m + 2) 0 (2 * S - 2 - 2 * (2 * m + 2)) 0)
  rw [show (0 : ℕ) + (2 * m + 2) = 2 * m + 2 from by ring]
  -- Phase 5: accumulation b=2
  set D_rem := 2 * S - 2 - 2 * (2 * m + 2)
  apply stepStar_trans (accum_b2 D_rem 0 (2 * m + 2))
  rw [show (0 : ℕ) + D_rem = D_rem from by ring]
  -- Phase 6: endgame
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (endgame m D_rem 0)
  simp only [Nat.zero_add]
  have hD : D_rem + m + 1 = 2 * A + 3 * m + 3 := by omega
  have hB : 3 * m + 5 = 3 * m + 5 := rfl
  rw [hD]; finish

-- Main cycle Case 2: B ≡ 2 (mod 3), B = 3(m+1)+2, m ≥ 0
-- (A, 3(m+1)+2, 0, 0, 0) ->+ (A', 3(m+2)+1, 0, 0, 0)
theorem cycle_case2 (A m : ℕ) :
    ⟨A, 3 * m + 5, 0, 0, 0⟩ [fm]⊢⁺ ⟨2 * A + 3 * m + 3, 3 * m + 7, 0, 0, 0⟩ := by
  set B := 3 * m + 5
  set S := A + B
  -- First step (rule 3): get stepPlus
  rw [show B = (B - 1) + 1 from by omega]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- Remaining pump
  apply stepStar_trans (pump (B - 1) (A + 1) 2)
  rw [show A + 1 + (B - 1) = S from by omega,
      show 2 + 2 * (B - 1) = 2 * B from by omega]
  -- Phase 2: deplete
  apply stepStar_trans (deplete S (2 * B) 0)
  rw [show (0 : ℕ) + 2 * S = 2 * S from by ring]
  -- Phase 3: init drain
  rw [show 2 * B = (2 * B - 2) + 2 from by omega,
      show 2 * S = (2 * S - 2) + 2 from by omega]
  apply stepStar_trans (init_drain (2 * B - 2) (2 * S - 2))
  -- Phase 4: drain loop
  rw [show 2 * B - 2 = 2 + 3 * (2 * m + 2) from by omega,
      show 2 * S - 2 = (2 * S - 2 - 2 * (2 * m + 2)) + 2 * (2 * m + 2) from by omega]
  apply stepStar_trans (drain_loop (2 * m + 2) 2 (2 * S - 2 - 2 * (2 * m + 2)) 0)
  rw [show (0 : ℕ) + (2 * m + 2) = 2 * m + 2 from by ring]
  -- Phase 4b: r=2 fix
  set D_rem := 2 * S - 2 - 2 * (2 * m + 2)
  rw [show D_rem = (D_rem - 3) + 3 from by omega]
  apply stepStar_trans (r2_fix (D_rem - 3) (2 * m + 2))
  rw [show 2 * m + 2 + 2 = (2 * m + 3) + 1 from by omega]
  -- Phase 5: accumulation c=2
  apply stepStar_trans (accum_c2 (D_rem - 3) 1 (2 * m + 3))
  rw [show (2 * m + 3) + 1 = 2 * m + 4 from by omega,
      show 1 + (D_rem - 3) = D_rem - 2 from by omega]
  -- Phase 5b: c2_to_b4
  rw [show 2 * m + 4 = (2 * m + 2) + 2 from by omega]
  apply stepStar_trans (c2_to_b4 (D_rem - 2) (2 * m + 2))
  -- Phase 6: endgame
  rw [show (4 : ℕ) = 2 + 2 from by ring]
  apply stepStar_trans (endgame m (D_rem - 2) 2)
  have hD : D_rem - 2 + m + 1 = 2 * A + 3 * m + 3 := by omega
  rw [hD, show 2 + 3 * m + 5 = 3 * m + 7 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 4, 0, 0, 0⟩) (by execute fm 27)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A m, q = ⟨A, 3 * m + 4, 0, 0, 0⟩ ∨ q = ⟨A, 3 * m + 5, 0, 0, 0⟩)
  · intro c ⟨A, m, hq⟩
    rcases hq with hq | hq <;> subst hq
    · exact ⟨⟨2 * A + 3 * m + 3, 3 * m + 5, 0, 0, 0⟩,
             ⟨2 * A + 3 * m + 3, m, Or.inr rfl⟩,
             cycle_case1 A m⟩
    · exact ⟨⟨2 * A + 3 * m + 3, 3 * m + 7, 0, 0, 0⟩,
             ⟨2 * A + 3 * m + 3, m + 1, Or.inl (by ring_nf)⟩,
             cycle_case2 A m⟩
  · exact ⟨2, 0, Or.inl rfl⟩

end Sz22_2003_unofficial_246
