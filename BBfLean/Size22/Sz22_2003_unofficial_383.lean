import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #383: [2/15, 99/14, 25/2, 7/11, 14/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_383

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer e to d
theorem e_to_d : ∀ n, ∀ c d,
    ⟨0, 0, c, d, n⟩ [fm]⊢* ⟨0, 0, c, d + n, 0⟩ := by
  intro n; induction n with
  | zero => intro c d; exists 0
  | succ n ih =>
    intro c d
    rw [show d + (n + 1) = (d + 1) + n from by ring]
    step fm
    exact ih c (d + 1)

-- R3 drain: transfer a to c (when b=0, d=0)
theorem r3_drain : ∀ a, ∀ c e,
    ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * a + c, 0, e⟩ := by
  intro a; induction a with
  | zero => intro c e; simp; exists 0
  | succ a ih =>
    intro c e
    show ⟨a + 1, 0, c, 0, e⟩ [fm]⊢* _
    step fm
    apply stepStar_trans (ih (c + 2) e)
    rw [show 2 * a + (c + 2) = 2 * (a + 1) + c from by ring]
    finish

-- R2 drain with c=0: transfer d to b and e
theorem r2_drain : ∀ k, ∀ a b e,
    ⟨a + k, b, 0, k, e⟩ [fm]⊢* ⟨a, b + 2 * k, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    show ⟨(a + k) + 1, b, 0, k + 1, e⟩ [fm]⊢* _
    step fm
    apply stepStar_trans (ih a (b + 2) (e + 1))
    rw [show (b + 2) + 2 * k = b + 2 * (k + 1) from by ring,
        show (e + 1) + k = e + (k + 1) from by ring]
    finish

-- Triple step: R1, R1, R2 in the inner loop of Phase C
theorem triple_step : ∀ a c d e,
    ⟨a, 2, c + 2, d + 1, e⟩ [fm]⊢* ⟨a + 1, 2, c, d, e + 1⟩ := by
  intro a c d e
  step fm; step fm; step fm
  ring_nf; finish

-- Iterate triple step k times
theorem triple_iter : ∀ k, ∀ a c d e,
    ⟨a, 2, c + 2 * k, d + k, e⟩ [fm]⊢* ⟨a + k, 2, c, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c d e; exists 0
  | succ k ih =>
    intro a c d e
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (triple_step _ _ _ _)
    apply stepStar_trans (ih (a + 1) c d (e + 1))
    rw [show (a + 1) + k = a + (k + 1) from by ring,
        show (e + 1) + k = e + (k + 1) from by ring]
    finish

-- drain_ab: drain a and b to c when d=0, e fixed
theorem drain_ab : ∀ b, ∀ a e,
    ⟨a + 1, b, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * a + b + 2, 0, e⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a e
  rcases b with _ | _ | b
  · show ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢* _
    step fm
    apply stepStar_trans (r3_drain a (0 + 2) e)
    ring_nf; finish
  · show ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢* _
    step fm; step fm; step fm
    apply stepStar_trans (r3_drain a (0 + 3) e)
    ring_nf; finish
  · show ⟨a + 1, b + 2, 0, 0, e⟩ [fm]⊢* _
    step fm; step fm; step fm
    have h := ih b (by omega) (a + 1) e
    apply stepStar_trans h
    ring_nf; finish

-- Phase D: (0, n+1, 2, 0, e) ->* (0, 0, n+3, 0, e)
theorem phase_d : ∀ n, ∀ e,
    ⟨0, n + 1, 2, 0, e⟩ [fm]⊢* ⟨0, 0, n + 3, 0, e⟩ := by
  intro n; rcases n with _ | n
  · intro e; step fm; step fm; finish
  · intro e
    show ⟨0, (n + 1) + 1, 2, 0, e⟩ [fm]⊢* _
    step fm; step fm
    show ⟨2, n, 0, 0, e⟩ [fm]⊢* _
    have h := drain_ab n 1 e
    rw [show 1 + 1 = 2 from rfl] at h
    apply stepStar_trans h
    ring_nf; finish

-- Phase C even: (0, 2, 2*m+1, 2*m, 1) ->* (1, 2*m+1, 0, 0, 2*m+1)
theorem phase_c_even : ∀ m,
    ⟨0, 2, 2 * m + 1, 2 * m, 1⟩ [fm]⊢* ⟨1, 2 * m + 1, 0, 0, 2 * m + 1⟩ := by
  intro m
  have h1 := triple_iter m 0 1 m 1
  simp only [show 1 + 2 * m = 2 * m + 1 from by ring,
             show m + m = 2 * m from by ring,
             show 0 + m = m from by ring,
             show 1 + m = m + 1 from by ring] at h1
  apply stepStar_trans h1
  step fm
  have h2 := r2_drain m 1 1 (m + 1)
  simp only [show 1 + m = m + 1 from by ring,
             show 1 + 2 * m = 2 * m + 1 from by ring,
             show (m + 1) + m = 2 * m + 1 from by ring] at h2
  exact h2

-- Phase C odd: (0, 2, 2*m+2, 2*m+1, 1) ->* (1, 2*m+2, 0, 0, 2*m+2)
theorem phase_c_odd : ∀ m,
    ⟨0, 2, 2 * m + 2, 2 * m + 1, 1⟩ [fm]⊢* ⟨1, 2 * m + 2, 0, 0, 2 * m + 2⟩ := by
  intro m
  have h1 := triple_iter m 0 2 (m + 1) 1
  simp only [show 2 + 2 * m = 2 * m + 2 from by ring,
             show (m + 1) + m = 2 * m + 1 from by ring,
             show 0 + m = m from by ring,
             show 1 + m = m + 1 from by ring] at h1
  apply stepStar_trans h1
  step fm; step fm
  have h2 := r2_drain (m + 1) 1 0 (m + 1)
  simp only [show 1 + (m + 1) = m + 2 from by ring,
             show 0 + 2 * (m + 1) = 2 * m + 2 from by ring,
             show (m + 1) + (m + 1) = 2 * m + 2 from by ring] at h2
  exact h2

-- R5 then R2: (0, 0, c+1, d, 0) -> (1, 0, c, d+1, 0) -> (0, 2, c, d, 1)
theorem r5_r2 : ∀ c d,
    ⟨0, 0, c + 1, d, 0⟩ [fm]⊢* ⟨0, 2, c, d, 1⟩ := by
  intro c d; step fm; step fm; finish

-- Combined: e_to_d, R5, R2
theorem phase_ab : ∀ n c,
    ⟨0, 0, c + 1, 0, n⟩ [fm]⊢* ⟨0, 2, c, n, 1⟩ := by
  intro n c
  apply stepStar_trans
  · have h := e_to_d n (c + 1) 0
    rw [show 0 + n = n from by ring] at h; exact h
  exact r5_r2 c n

-- Full one-step transition
-- (0, 0, n+2, 0, n) ⊢⁺ (0, 0, n+3, 0, n+1)
-- Phases: e_to_d, R5, R2, phase_c, R3, phase_d
-- For even n = 2m: phase_c uses phase_c_even
-- For odd n = 2m+1: phase_c uses phase_c_odd

theorem main_trans_even (m : ℕ) :
    ⟨0, 0, 2 * m + 2, 0, 2 * m⟩ [fm]⊢⁺ ⟨0, 0, 2 * m + 3, 0, 2 * m + 1⟩ := by
  -- Phase AB: e_to_d + R5 + R2
  apply stepStar_stepPlus_stepPlus
  · have h := phase_ab (2 * m) (2 * m + 1)
    rw [show (2 * m + 1) + 1 = 2 * m + 2 from by ring] at h
    exact h
  -- Phase C even
  apply stepStar_stepPlus_stepPlus
  · exact phase_c_even m
  -- R3 step + Phase D: ⊢⁺
  apply stepPlus_stepStar_stepPlus
  · apply step_stepPlus
    show fm ⟨1, 2 * m + 1, 0, 0, 2 * m + 1⟩ = some ⟨0, 2 * m + 1, 2, 0, 2 * m + 1⟩
    rfl
  -- Phase D
  exact phase_d (2 * m) (2 * m + 1)

theorem main_trans_odd (m : ℕ) :
    ⟨0, 0, 2 * m + 3, 0, 2 * m + 1⟩ [fm]⊢⁺ ⟨0, 0, 2 * m + 4, 0, 2 * m + 2⟩ := by
  -- Phase AB: e_to_d + R5 + R2
  apply stepStar_stepPlus_stepPlus
  · have h := phase_ab (2 * m + 1) (2 * m + 2)
    rw [show (2 * m + 2) + 1 = 2 * m + 3 from by ring] at h
    exact h
  -- Phase C odd
  apply stepStar_stepPlus_stepPlus
  · exact phase_c_odd m
  -- R3 step + Phase D: ⊢⁺
  apply stepPlus_stepStar_stepPlus
  · apply step_stepPlus
    show fm ⟨1, 2 * m + 2, 0, 0, 2 * m + 2⟩ = some ⟨0, 2 * m + 2, 2, 0, 2 * m + 2⟩
    rfl
  -- Phase D
  have h := phase_d (2 * m + 1) (2 * m + 2)
  rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
      show 2 * m + 1 + 3 = 2 * m + 4 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := Bool × ℕ)
    (fun ⟨p, m⟩ ↦ if p then ⟨0, 0, 2*m+3, 0, 2*m+1⟩ else ⟨0, 0, 2*m+2, 0, 2*m⟩)
    ⟨false, 0⟩
  intro ⟨p, m⟩
  cases p with
  | false => exact ⟨⟨true, m⟩, main_trans_even m⟩
  | true =>
    refine ⟨⟨false, m + 1⟩, ?_⟩
    simp only [show 2 * (m + 1) = 2 * m + 2 from by ring]
    exact main_trans_odd m

end Sz22_2003_unofficial_383
