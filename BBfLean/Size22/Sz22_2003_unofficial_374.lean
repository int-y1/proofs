import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #374: [2/15, 9/14, 275/2, 7/5, 50/11]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  0
-1  0  2  0  1
 0  0 -1  1  0
 1  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_374

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

theorem c_to_d : ∀ j c d e,
    ⟨0, 0, c + j, d, e⟩ [fm]⊢* ⟨0, 0, c, d + j, e⟩ := by
  intro j; induction j with
  | zero => intros; exists 0
  | succ j ih =>
    intro c d e
    rw [show c + (j + 1) = (c + 1) + j from by ring]
    apply stepStar_trans (ih (c + 1) d e)
    step fm
    rw [show d + j + 1 = d + (j + 1) from by ring]; finish

theorem a_to_ce : ∀ j a c e,
    ⟨a + j, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * j, 0, e + j⟩ := by
  intro j; induction j with
  | zero => intros; simp; exists 0
  | succ j ih =>
    intro a c e
    -- Split off last step: ih first, then one R3 step
    rw [show a + (j + 1) = (a + 1) + j from by ring]
    apply stepStar_trans (ih (a + 1) c e)
    -- Now at (a+1, 0, c+2*j, 0, e+j)
    step fm
    rw [show c + 2 * j + 2 = c + 2 * (j + 1) from by ring,
        show e + j + 1 = e + (j + 1) from by ring]
    finish

theorem drain_b : ∀ j a b e,
    ⟨a + 1, b + 2 * j, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + j, b, 0, 0, e + j⟩ := by
  intro j; induction j with
  | zero => intros; simp; exists 0
  | succ j ih =>
    intro a b e
    rw [show b + 2 * (j + 1) = b + 2 * j + 2 from by ring]
    have h1 := ih a (b + 2) e
    rw [show (b + 2) + 2 * j = b + 2 * j + 2 from by ring] at h1
    apply stepStar_trans h1
    rw [show a + 1 + j = a + j + 1 from by ring]
    step fm; step fm; step fm
    rw [show a + j + 1 + 1 = a + 1 + (j + 1) from by ring,
        show e + j + 1 = e + (j + 1) from by ring]; finish

theorem inner_round : ∀ b d e,
    ⟨0, b + 2, 0, d + 3, e + 1⟩ [fm]⊢* ⟨0, b + 6, 0, d, e⟩ := by
  intro b d e
  step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem inner_loop : ∀ j b d e,
    ⟨0, b + 2, 0, d + 3 * j, e + j⟩ [fm]⊢* ⟨0, b + 2 + 4 * j, 0, d, e⟩ := by
  intro j; induction j with
  | zero => intros; simp; exists 0
  | succ j ih =>
    intro b d e
    -- Split off last round: first ih, then inner_round
    rw [show d + 3 * (j + 1) = (d + 3) + 3 * j from by ring,
        show e + (j + 1) = (e + 1) + j from by ring]
    apply stepStar_trans (ih b (d + 3) (e + 1))
    have h := inner_round (b + 4 * j) d e
    rw [show b + 4 * j + 2 = b + 2 + 4 * j from by ring,
        show b + 4 * j + 6 = b + 2 + 4 * (j + 1) from by ring] at h
    exact h

theorem first_round : ∀ d e,
    ⟨0, 0, 0, d + 3, e + 1⟩ [fm]⊢⁺ ⟨0, 4, 0, d, e⟩ := by
  intro d e
  step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem tail_r0 : ∀ b e,
    ⟨0, b + 2, 0, 0, e + 1⟩ [fm]⊢* ⟨3, b, 0, 0, e⟩ := by
  intro b e; step fm; step fm; step fm; ring_nf; finish

theorem tail_r1 : ∀ b e,
    ⟨0, b + 2, 0, 1, e + 1⟩ [fm]⊢* ⟨3, b, 0, 0, e + 1⟩ := by
  intro b e
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem tail_r2 : ∀ b e,
    ⟨0, b + 2, 0, 2, e + 1⟩ [fm]⊢* ⟨2, b + 2, 0, 0, e + 1⟩ := by
  intro b e
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Full transition chain: first_round + inner_loop + tail_r0 + drain + a_to_ce + c_to_d
-- D=3(j+1), E=e+j+2
theorem main_trans_r0 (j e : ℕ) :
    ⟨0, 0, 0, 3 * j + 3, e + j + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * j + 8, e + 4 * j + 5⟩ := by
  apply stepPlus_stepStar_stepPlus
  · have h := first_round (3 * j) (e + j + 1)
    rw [show e + j + 1 + 1 = e + j + 2 from by ring] at h; exact h
  apply stepStar_trans
  · have h := inner_loop j 2 0 (e + 1)
    rw [show 0 + 3 * j = 3 * j from by ring,
        show (e + 1) + j = e + j + 1 from by ring,
        show 2 + 2 + 4 * j = 4 * j + 4 from by ring] at h; exact h
  apply stepStar_trans
  · have h := tail_r0 (4 * j + 2) e
    rw [show 4 * j + 2 + 2 = 4 * j + 4 from by ring] at h; exact h
  apply stepStar_trans
  · have h := drain_b (2 * j + 1) 2 0 e
    rw [show 0 + 2 * (2 * j + 1) = 4 * j + 2 from by ring,
        show 2 + 1 + (2 * j + 1) = 2 * j + 4 from by ring,
        show e + (2 * j + 1) = e + 2 * j + 1 from by ring] at h; exact h
  apply stepStar_trans
  · have h := a_to_ce (2 * j + 4) 0 0 (e + 2 * j + 1)
    rw [show 0 + (2 * j + 4) = 2 * j + 4 from by ring,
        show 0 + 2 * (2 * j + 4) = 4 * j + 8 from by ring,
        show e + 2 * j + 1 + (2 * j + 4) = e + 4 * j + 5 from by ring] at h; exact h
  have h := c_to_d (4 * j + 8) 0 0 (e + 4 * j + 5)
  rw [show 0 + (4 * j + 8) = 4 * j + 8 from by ring] at h; exact h

-- D=3(j+1)+1, E=e+j+2
theorem main_trans_r1 (j e : ℕ) :
    ⟨0, 0, 0, 3 * j + 4, e + j + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * j + 8, e + 4 * j + 6⟩ := by
  apply stepPlus_stepStar_stepPlus
  · have h := first_round (3 * j + 1) (e + j + 1)
    rw [show 3 * j + 1 + 3 = 3 * j + 4 from by ring,
        show e + j + 1 + 1 = e + j + 2 from by ring] at h; exact h
  apply stepStar_trans
  · have h := inner_loop j 2 1 (e + 1)
    rw [show 1 + 3 * j = 3 * j + 1 from by ring,
        show (e + 1) + j = e + j + 1 from by ring,
        show 2 + 2 + 4 * j = 4 * j + 4 from by ring] at h; exact h
  apply stepStar_trans
  · have h := tail_r1 (4 * j + 2) e
    rw [show 4 * j + 2 + 2 = 4 * j + 4 from by ring] at h; exact h
  apply stepStar_trans
  · have h := drain_b (2 * j + 1) 2 0 (e + 1)
    rw [show 0 + 2 * (2 * j + 1) = 4 * j + 2 from by ring,
        show 2 + 1 + (2 * j + 1) = 2 * j + 4 from by ring,
        show (e + 1) + (2 * j + 1) = e + 2 * j + 2 from by ring] at h; exact h
  apply stepStar_trans
  · have h := a_to_ce (2 * j + 4) 0 0 (e + 2 * j + 2)
    rw [show 0 + (2 * j + 4) = 2 * j + 4 from by ring,
        show 0 + 2 * (2 * j + 4) = 4 * j + 8 from by ring,
        show e + 2 * j + 2 + (2 * j + 4) = e + 4 * j + 6 from by ring] at h; exact h
  have h := c_to_d (4 * j + 8) 0 0 (e + 4 * j + 6)
  rw [show 0 + (4 * j + 8) = 4 * j + 8 from by ring] at h; exact h

-- D=3(j+1)+2, E=e+j+2
theorem main_trans_r2 (j e : ℕ) :
    ⟨0, 0, 0, 3 * j + 5, e + j + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * j + 8, e + 4 * j + 7⟩ := by
  apply stepPlus_stepStar_stepPlus
  · have h := first_round (3 * j + 2) (e + j + 1)
    rw [show 3 * j + 2 + 3 = 3 * j + 5 from by ring,
        show e + j + 1 + 1 = e + j + 2 from by ring] at h; exact h
  apply stepStar_trans
  · have h := inner_loop j 2 2 (e + 1)
    rw [show 2 + 3 * j = 3 * j + 2 from by ring,
        show (e + 1) + j = e + j + 1 from by ring,
        show 2 + 2 + 4 * j = 4 * j + 4 from by ring] at h; exact h
  apply stepStar_trans
  · have h := tail_r2 (4 * j + 2) e
    rw [show 4 * j + 2 + 2 = 4 * j + 4 from by ring] at h; exact h
  -- Now at (2, 4j+4, 0, 0, e+1). Note: tail_r2 gives (2, b+2, ...) = (2, 4j+2+2, ...)
  -- which Lean normalizes to (2, 4*j+4, ...) or (2, 4*j+2+2, ...).
  apply stepStar_trans
  · have h := drain_b (2 * j + 2) 1 0 (e + 1)
    rw [show 0 + 2 * (2 * j + 2) = 4 * j + 4 from by ring,
        show 1 + 1 + (2 * j + 2) = 2 * j + 4 from by ring,
        show (e + 1) + (2 * j + 2) = e + 2 * j + 3 from by ring] at h; exact h
  apply stepStar_trans
  · have h := a_to_ce (2 * j + 4) 0 0 (e + 2 * j + 3)
    rw [show 0 + (2 * j + 4) = 2 * j + 4 from by ring,
        show 0 + 2 * (2 * j + 4) = 4 * j + 8 from by ring,
        show e + 2 * j + 3 + (2 * j + 4) = e + 4 * j + 7 from by ring] at h; exact h
  have h := c_to_d (4 * j + 8) 0 0 (e + 4 * j + 7)
  rw [show 0 + (4 * j + 8) = 4 * j + 8 from by ring] at h; exact h

theorem special_d2 (e : ℕ) :
    ⟨0, 0, 0, 2, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4, e + 3⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 2, e + 1⟩ = some ⟨1, 0, 2, 2, e⟩; rfl
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans
  · have h := a_to_ce 2 0 0 (e + 1)
    rw [show 0 + 2 = 2 from by ring,
        show 0 + 2 * 2 = 4 from by ring,
        show e + 1 + 2 = e + 3 from by ring] at h; exact h
  have h := c_to_d 4 0 0 (e + 3)
  rw [show 0 + 4 = 4 from by ring] at h; exact h

-- C(d,e) = (0, 0, 0, d+4, e+d+3)
-- C(0,0) = (0, 0, 0, 4, 3)
theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 3⟩) (by execute fm 17)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d + 4, e + d + 3⟩) ⟨0, 0⟩
  intro ⟨d, e⟩
  have hmod : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
  rcases hmod with hr | hr | hr
  · -- d = 3m
    obtain ⟨m, hm⟩ : ∃ m, d = 3 * m := ⟨d / 3, by omega⟩
    subst hm
    refine ⟨⟨4 * m + 4, e + 2 * m⟩, ?_⟩
    show ⟨0, 0, 0, 3 * m + 4, e + 3 * m + 3⟩ [fm]⊢⁺
         ⟨0, 0, 0, 4 * m + 4 + 4, e + 2 * m + (4 * m + 4) + 3⟩
    rw [show 4 * m + 4 + 4 = 4 * m + 8 from by ring,
        show e + 2 * m + (4 * m + 4) + 3 = e + 6 * m + 7 from by ring]
    have h := main_trans_r1 m (e + 2 * m + 1)
    rw [show e + 2 * m + 1 + m + 2 = e + 3 * m + 3 from by ring,
        show e + 2 * m + 1 + 4 * m + 6 = e + 6 * m + 7 from by ring] at h
    exact h
  · -- d = 3m+1
    obtain ⟨m, hm⟩ : ∃ m, d = 3 * m + 1 := ⟨d / 3, by omega⟩
    subst hm
    refine ⟨⟨4 * m + 4, e + 2 * m + 2⟩, ?_⟩
    show ⟨0, 0, 0, 3 * m + 1 + 4, e + (3 * m + 1) + 3⟩ [fm]⊢⁺
         ⟨0, 0, 0, 4 * m + 4 + 4, e + 2 * m + 2 + (4 * m + 4) + 3⟩
    rw [show 3 * m + 1 + 4 = 3 * m + 5 from by ring,
        show e + (3 * m + 1) + 3 = e + 3 * m + 4 from by ring,
        show 4 * m + 4 + 4 = 4 * m + 8 from by ring,
        show e + 2 * m + 2 + (4 * m + 4) + 3 = e + 6 * m + 9 from by ring]
    have h := main_trans_r2 m (e + 2 * m + 2)
    rw [show e + 2 * m + 2 + m + 2 = e + 3 * m + 4 from by ring,
        show e + 2 * m + 2 + 4 * m + 7 = e + 6 * m + 9 from by ring] at h
    exact h
  · -- d = 3m+2
    obtain ⟨m, hm⟩ : ∃ m, d = 3 * m + 2 := ⟨d / 3, by omega⟩
    subst hm
    refine ⟨⟨4 * m + 8, e + 2 * m⟩, ?_⟩
    show ⟨0, 0, 0, 3 * m + 2 + 4, e + (3 * m + 2) + 3⟩ [fm]⊢⁺
         ⟨0, 0, 0, 4 * m + 8 + 4, e + 2 * m + (4 * m + 8) + 3⟩
    rw [show 3 * m + 2 + 4 = 3 * m + 6 from by ring,
        show e + (3 * m + 2) + 3 = e + 3 * m + 5 from by ring,
        show 4 * m + 8 + 4 = 4 * m + 12 from by ring,
        show e + 2 * m + (4 * m + 8) + 3 = e + 6 * m + 11 from by ring]
    have h := main_trans_r0 (m + 1) (e + 2 * m + 2)
    rw [show 3 * (m + 1) + 3 = 3 * m + 6 from by ring,
        show e + 2 * m + 2 + (m + 1) + 2 = e + 3 * m + 5 from by ring,
        show 4 * (m + 1) + 8 = 4 * m + 12 from by ring,
        show e + 2 * m + 2 + 4 * (m + 1) + 5 = e + 6 * m + 11 from by ring] at h
    exact h

end Sz22_2003_unofficial_374
