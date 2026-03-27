import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #86: [1/30, 14/3, 27/385, 5/7, 33/2]

Vector representation:
```
-1 -1 -1  0  0
 1 -1  0  1  0
 0  3 -1 -1 -1
 0  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_86

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- (a, 0, 0, d+2, e+1) -> (a+3, 0, 0, d+3, e) in 5 steps
-- R4, R3, R2, R2, R2
theorem growth_step (a d e : ℕ) :
    (⟨a, 0, 0, d+2, e+1⟩ : Q) [fm]⊢* ⟨a+3, 0, 0, d+3, e⟩ := by
  execute fm 5

theorem growth_chain : ∀ K : ℕ, ∀ a d e : ℕ,
    (⟨a, 0, 0, d+2, e+K⟩ : Q) [fm]⊢* ⟨a+3*K, 0, 0, d+K+2, e⟩ := by
  intro K; induction K with
  | zero => intro a d e; simp; exists 0
  | succ K ih =>
    intro a d e
    rw [show e + (K + 1) = (e + 1) + K from by ring]
    apply stepStar_trans (ih a d (e + 1))
    -- goal: (a+3*K, 0, 0, d+K+2, e+1) ⊢* (a+3*(K+1), 0, 0, d+(K+1)+2, e)
    -- need to match growth_step: need d+K+2 = (d+K)+2
    have := growth_step (a + 3 * K) (d + K) e
    rw [show a + 3 * K + 3 = a + 3 * (K + 1) from by ring,
        show d + K + 3 = d + (K + 1) + 2 from by ring] at this
    exact this

theorem d_to_c : ∀ K : ℕ, ∀ a c : ℕ,
    (⟨a, 0, c, K, 0⟩ : Q) [fm]⊢* ⟨a, 0, c+K, 0, 0⟩ := by
  intro K; induction K with
  | zero => intro a c; simp; exists 0
  | succ K ih =>
    intro a c
    step fm
    apply stepStar_trans (ih a (c + 1))
    rw [show c + 1 + K = c + (K + 1) from by ring]
    finish

theorem r5_r1_chain : ∀ K : ℕ, ∀ a c e : ℕ,
    (⟨a+2*K, 0, c+K, 0, e⟩ : Q) [fm]⊢* ⟨a, 0, c, 0, e+K⟩ := by
  intro K; induction K with
  | zero => intro a c e; simp; exists 0
  | succ K ih =>
    intro a c e
    rw [show a + 2 * (K + 1) = (a + 2 * K) + 2 from by ring,
        show c + (K + 1) = (c + K) + 1 from by ring]
    -- (a+2*K+2, 0, c+K+1, 0, e) R5-> (a+2*K+1, 1, c+K+1, 0, e+1) R1-> (a+2*K, 0, c+K, 0, e+1)
    apply stepStar_trans
      (by execute fm 2 : (⟨(a+2*K)+2, 0, (c+K)+1, 0, e⟩ : Q) [fm]⊢* ⟨a+2*K, 0, c+K, 0, e+1⟩)
    have := ih a c (e + 1)
    rw [show e + 1 + K = e + (K + 1) from by ring] at this
    exact this

theorem wind_down_chain : ∀ k : ℕ, ∀ e : ℕ,
    (⟨2*k+1, 0, 0, 0, e⟩ : Q) [fm]⊢* ⟨1, 0, 0, 0, e+2*k⟩ := by
  intro k; induction k with
  | zero => intro e; exists 0
  | succ k ih =>
    intro e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    apply stepStar_trans
      (by execute fm 5 : (⟨(2*k+1)+2, 0, 0, 0, e⟩ : Q) [fm]⊢* ⟨2*k+1, 0, 0, 0, e+2⟩)
    have := ih (e + 2)
    rw [show e + 2 + 2 * k = e + 2 * (k + 1) from by ring] at this
    exact this

theorem big_transition (n : ℕ) :
    (⟨1, 0, 0, 0, 2*n+6⟩ : Q) [fm]⊢⁺ ⟨1, 0, 0, 0, 4*n+14⟩ := by
  have h1 : (⟨1, 0, 0, 0, 2*n+6⟩ : Q) [fm]⊢ ⟨0, 1, 0, 0, 2*n+7⟩ := by
    unfold fm; ring_nf
  apply step_stepStar_stepPlus h1
  -- 8 more opening steps
  apply stepStar_trans (by execute fm 8 : (⟨0, 1, 0, 0, 2*n+7⟩ : Q) [fm]⊢* ⟨4, 0, 0, 3, 2*n+7⟩)
  -- growth_chain K = 2*n+7
  rw [show (3 : ℕ) = 1 + 2 from by ring, show 2*n+7 = 0 + (2*n+7) from by ring]
  apply stepStar_trans (growth_chain (2*n+7) 4 1 0)
  rw [show 4 + 3 * (2 * n + 7) = 6*n+25 from by ring,
      show 1 + (2 * n + 7) + 2 = 2*n+10 from by ring]
  -- d_to_c
  apply stepStar_trans (d_to_c (2*n+10) (6*n+25) 0)
  -- r5_r1_chain: need (6*n+25, 0, 0+(2*n+10), 0, 0) to match (a+2*K, 0, c+K, 0, e)
  -- with a=2*n+5, c=0, K=2*n+10, e=0
  -- Current LHS: (6*n+25, 0, 0+(2*n+10), 0, 0)
  -- r5_r1_chain needs: ((2*n+5)+2*(2*n+10), 0, 0+(2*n+10), 0, 0)
  -- 6*n+25 should unify with (2*n+5)+2*(2*n+10) but Lean may not see this
  rw [show (6*n+25 : ℕ) = (2*n+5) + 2*(2*n+10) from by ring]
  apply stepStar_trans (r5_r1_chain (2*n+10) (2*n+5) 0 0)
  rw [show (0 : ℕ) + (2*n+10) = 2*n+10 from by ring,
      show (2*n+5 : ℕ) = 2*(n+2)+1 from by ring]
  apply stepStar_trans (wind_down_chain (n+2) (2*n+10))
  rw [show 2*n+10 + 2*(n+2) = 4*n+14 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 6⟩)
  · unfold c₀
    -- (1,0,0,0,0) -> (7,0,0,4,0) in 14 steps
    apply stepStar_trans
      (by execute fm 14 : (⟨1, 0, 0, 0, 0⟩ : Q) [fm]⊢* ⟨7, 0, 0, 4, 0⟩)
    -- d_to_c 4: (7,0,0,4,0) -> (7,0,4,0,0)
    apply stepStar_trans (d_to_c 4 7 0)
    -- r5_r1_chain 3: (7,0,4,0,0) -> (1,0,1,0,3)
    rw [show 0 + 4 = 4 from by ring,
        show (7 : ℕ) = 1 + 2 * 3 from by ring, show (4 : ℕ) = 1 + 3 from by ring]
    apply stepStar_trans (r5_r1_chain 3 1 1 0)
    rw [show (0 : ℕ) + 3 = 3 from by ring]
    -- (1,0,1,0,3) -> (13,0,0,6,0) in 21 steps
    apply stepStar_trans
      (by execute fm 21 : (⟨1, 0, 1, 0, 3⟩ : Q) [fm]⊢* ⟨13, 0, 0, 6, 0⟩)
    -- d_to_c 6: (13,0,0,6,0) -> (13,0,6,0,0)
    apply stepStar_trans (d_to_c 6 13 0)
    -- r5_r1_chain 6: (13,0,6,0,0) -> (1,0,0,0,6)
    rw [show 0 + 6 = 6 from by ring,
        show (13 : ℕ) = 1 + 2 * 6 from by ring, show (6 : ℕ) = 0 + 6 from by ring]
    apply stepStar_trans (r5_r1_chain 6 1 0 0)
    rw [show (0 : ℕ) + 6 = 6 from by ring]
    finish
  · rw [show (6 : ℕ) = 2 * 0 + 6 from by ring]
    apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun n ↦ ⟨1, 0, 0, 0, 2*n+6⟩) 0
    intro n
    refine ⟨2*n+4, ?_⟩
    have := big_transition n
    rw [show 2 * (2 * n + 4) + 6 = 4 * n + 14 from by ring]
    exact this

end Sz22_2003_unofficial_86
