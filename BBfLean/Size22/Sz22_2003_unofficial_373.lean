import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #373: [2/15, 9/14, 275/2, 7/5, 20/11]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  0
-1  0  2  0  1
 0  0 -1  1  0
 2  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_373

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

theorem r4_chain : ∀ k c d e, ⟨0, 0, c + k, d, e⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

theorem burn_triple : ⟨a + 1, b + 2, 0, 0, e⟩ [fm]⊢* ⟨a + 2, b, 0, 0, e + 1⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem burn_iter : ∀ k, ∀ a r e,
    ⟨a + 1, 2 * k + r, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + k, r, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a r e
  · simp; exists 0
  rw [show 2 * (k + 1) + r = (2 * k + r) + 2 from by ring]
  apply stepStar_trans burn_triple
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

theorem burn_odd_tail : ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢* ⟨a + 1, 0, 1, 0, e + 1⟩ := by
  step fm; step fm; finish

private theorem burn_r4_even (a k e : ℕ) :
    ⟨a + 1, 2 * k, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * a + 2 * k + 2, e + a + 2 * k + 1⟩ := by
  apply stepStar_trans (burn_iter k a 0 e)
  apply stepStar_trans
  · show ⟨a + 1 + k, 0, 0, 0, e + k⟩ [fm]⊢* ⟨0, 0, 0 + 2 * (a + 1 + k), 0, e + k + (a + 1 + k)⟩
    exact r3_chain (a + 1 + k) 0 (e + k)
  rw [show 0 + 2 * (a + 1 + k) = 0 + (2 * (a + 1 + k)) from by ring]
  apply stepStar_trans (r4_chain (2 * (a + 1 + k)) 0 0 (e + k + (a + 1 + k)))
  ring_nf; finish

private theorem burn_r4_odd (a k e : ℕ) :
    ⟨a + 1, 2 * k + 1, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * a + 2 * k + 3, e + a + 2 * k + 2⟩ := by
  apply stepStar_trans (burn_iter k a 1 e)
  rw [show a + 1 + k = (a + k) + 1 from by ring]
  apply stepStar_trans burn_odd_tail
  apply stepStar_trans (r3_chain ((a + k) + 1) 1 (e + k + 1))
  rw [show 1 + 2 * ((a + k) + 1) = 0 + (1 + 2 * ((a + k) + 1)) from by ring]
  apply stepStar_trans (r4_chain (1 + 2 * ((a + k) + 1)) 0 0 (e + k + 1 + ((a + k) + 1)))
  ring_nf; finish

theorem burn_r4 (a b e : ℕ) :
    ⟨a + 1, b, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * a + b + 2, e + a + b + 1⟩ := by
  rcases Nat.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk; rw [show k + k = 2 * k from by ring]
    apply stepStar_trans (burn_r4_even a k e); ring_nf; finish
  · subst hk
    apply stepStar_trans (burn_r4_odd a k e); ring_nf; finish

theorem mid_step_b0 : ⟨0, 0, 0, d + 3, e + 1⟩ [fm]⊢* ⟨0, 5, 0, d, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; ring_nf; finish

theorem mid_step_bpos : ⟨0, b + 1, 0, d + 3, e + 1⟩ [fm]⊢* ⟨0, b + 6, 0, d, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; ring_nf; finish

theorem mid_step : ⟨0, b, 0, d + 3, e + 1⟩ [fm]⊢* ⟨0, b + 5, 0, d, e⟩ := by
  match b with
  | 0 => exact mid_step_b0
  | b + 1 => rw [show b + 1 + 5 = b + 6 from by ring]; exact mid_step_bpos

theorem mid_iter : ∀ k, ∀ b d e,
    ⟨0, b, 0, d + 3 * k, e + k⟩ [fm]⊢* ⟨0, b + 5 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show d + 3 * (k + 1) = (d + 3 * k) + 3 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  apply stepStar_trans mid_step
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

theorem after_r5_d3 : ⟨2, 0, 1, d + 3, e⟩ [fm]⊢* ⟨0, 5, 0, d, e⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

theorem after_r5_d2 : ⟨2, 0, 1, 2, e⟩ [fm]⊢* ⟨1, 3, 0, 0, e⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem after_r5_d1 : ⟨2, 0, 1, 1, e⟩ [fm]⊢* ⟨2, 1, 0, 0, e⟩ := by
  step fm; step fm; ring_nf; finish

theorem exit_d0 : ⟨0, b + 1, 0, 0, e + 1⟩ [fm]⊢* ⟨3, b, 0, 0, e⟩ := by
  step fm; step fm; ring_nf; finish

theorem exit_d1 : ⟨0, b, 0, 1, e + 1⟩ [fm]⊢* ⟨2, b + 1, 0, 0, e⟩ := by
  match b with
  | 0 => step fm; step fm; step fm; ring_nf; finish
  | b + 1 =>
    step fm; step fm; step fm
    rw [show b + 1 + 1 = b + 2 from by ring]; ring_nf; finish

theorem exit_d2 : ⟨0, b, 0, 2, e + 1⟩ [fm]⊢* ⟨1, b + 3, 0, 0, e⟩ := by
  match b with
  | 0 => step fm; step fm; step fm; step fm; ring_nf; finish
  | b + 1 =>
    step fm; step fm; step fm; step fm
    rw [show b + 1 + 3 = b + 4 from by ring]; ring_nf; finish

-- D=1: (0,0,0,1,e+1) ⊢⁺ (0,0,0,5,e+3)
theorem main_d1 (e : ℕ) :
    ⟨0, 0, 0, 1, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 5, e + 3⟩ := by
  apply step_stepStar_stepPlus (show fm ⟨0, 0, 0, 1, e + 1⟩ = some ⟨2, 0, 1, 1, e⟩ from rfl)
  apply stepStar_trans after_r5_d1
  exact burn_r4 1 1 e

-- D=2: (0,0,0,2,e+1) ⊢⁺ (0,0,0,5,e+4)
theorem main_r2_q0 (e : ℕ) :
    ⟨0, 0, 0, 2, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 5, e + 4⟩ := by
  apply step_stepStar_stepPlus (show fm ⟨0, 0, 0, 2, e + 1⟩ = some ⟨2, 0, 1, 2, e⟩ from rfl)
  apply stepStar_trans after_r5_d2
  exact burn_r4 0 3 e

-- D=3(q+1)+2 = 3q+5: (0,0,0,3q+5,e+q+2) ⊢⁺ (0,0,0,5q+10,e+5q+9)
theorem main_r2_qpos (q e : ℕ) :
    ⟨0, 0, 0, 3 * q + 5, e + q + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * q + 10, e + 5 * q + 9⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 3 * q + 5, e + q + 2⟩ = some ⟨2, 0, 1, 3 * q + 5, e + q + 1⟩; rfl
  apply stepStar_trans
  · show ⟨2, 0, 1, 3 * q + 5, e + q + 1⟩ [fm]⊢* ⟨0, 5, 0, 3 * q + 2, e + q + 1⟩
    rw [show 3 * q + 5 = (3 * q + 2) + 3 from by ring]; exact after_r5_d3
  apply stepStar_trans
  · show ⟨0, 5, 0, 3 * q + 2, e + q + 1⟩ [fm]⊢* ⟨0, 5 + 5 * q, 0, 2, e + 1⟩
    rw [show 3 * q + 2 = 2 + 3 * q from by ring,
        show e + q + 1 = (e + 1) + q from by ring]; exact mid_iter q 5 2 (e + 1)
  apply stepStar_trans exit_d2
  apply stepStar_trans (burn_r4 0 (5 + 5 * q + 3) e)
  ring_nf; finish

-- D=3(q+1)+1 = 3q+4: (0,0,0,3q+4,e+q+2) ⊢⁺ (0,0,0,5q+10,e+5q+8)
theorem main_r1 (q e : ℕ) :
    ⟨0, 0, 0, 3 * q + 4, e + q + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * q + 10, e + 5 * q + 8⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 3 * q + 4, e + q + 2⟩ = some ⟨2, 0, 1, 3 * q + 4, e + q + 1⟩; rfl
  apply stepStar_trans
  · show ⟨2, 0, 1, 3 * q + 4, e + q + 1⟩ [fm]⊢* ⟨0, 5, 0, 3 * q + 1, e + q + 1⟩
    rw [show 3 * q + 4 = (3 * q + 1) + 3 from by ring]; exact after_r5_d3
  apply stepStar_trans
  · show ⟨0, 5, 0, 3 * q + 1, e + q + 1⟩ [fm]⊢* ⟨0, 5 + 5 * q, 0, 1, e + 1⟩
    rw [show 3 * q + 1 = 1 + 3 * q from by ring,
        show e + q + 1 = (e + 1) + q from by ring]; exact mid_iter q 5 1 (e + 1)
  apply stepStar_trans exit_d1
  apply stepStar_trans (burn_r4 1 (5 + 5 * q + 1) e)
  ring_nf; finish

-- D=3(q+1) = 3q+3: (0,0,0,3q+3,e+q+2) ⊢⁺ (0,0,0,5q+10,e+5q+7)
theorem main_r0 (q e : ℕ) :
    ⟨0, 0, 0, 3 * q + 3, e + q + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * q + 10, e + 5 * q + 7⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 3 * q + 3, e + q + 2⟩ = some ⟨2, 0, 1, 3 * q + 3, e + q + 1⟩; rfl
  apply stepStar_trans
  · show ⟨2, 0, 1, 3 * q + 3, e + q + 1⟩ [fm]⊢* ⟨0, 5, 0, 3 * q, e + q + 1⟩
    exact after_r5_d3
  apply stepStar_trans
  · show ⟨0, 5, 0, 3 * q, e + q + 1⟩ [fm]⊢* ⟨0, 5 + 5 * q, 0, 0, e + 1⟩
    rw [show 3 * q = 0 + 3 * q from by ring,
        show e + q + 1 = (e + 1) + q from by ring]; exact mid_iter q 5 0 (e + 1)
  apply stepStar_trans
  · show ⟨0, 5 + 5 * q, 0, 0, e + 1⟩ [fm]⊢* ⟨3, 5 * q + 4, 0, 0, e⟩
    rw [show 5 + 5 * q = 5 * q + 4 + 1 from by ring]; exact exit_d0
  apply stepStar_trans (burn_r4 2 (5 * q + 4) e)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e + 1⟩ ∧ 3 * (e + 1) ≥ d + 2)
  · intro c ⟨d, e, hq, hinv⟩
    subst hq
    have hmod : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · -- d ≡ 0 mod 3: d = 3*m
      have hd : d = 3 * (d / 3) := by omega
      rw [hd]; set m := d / 3
      rcases m with _ | m
      · -- m=0, d=0, D=1
        refine ⟨⟨0, 0, 0, 5, e + 2 + 1⟩, ⟨4, e + 2, rfl, by omega⟩, ?_⟩
        convert main_d1 e using 2
      · -- m>=1, d=3*(m+1), D=3*(m+1)+1=3m+4
        have he : e ≥ m + 1 := by omega
        obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le he
        refine ⟨⟨0, 0, 0, 5 * m + 10, e' + 5 * m + 7 + 1⟩,
          ⟨5 * m + 9, e' + 5 * m + 7, rfl, by omega⟩, ?_⟩
        convert main_r1 m e' using 2; ring_nf
    · -- d = 1 mod 3: d = 3*m + 1
      have hd : d = 3 * (d / 3) + 1 := by omega
      rw [hd]; set m := d / 3
      rcases m with _ | m
      · -- m=0, d=1, D=2
        refine ⟨⟨0, 0, 0, 5, e + 3 + 1⟩, ⟨4, e + 3, rfl, by omega⟩, ?_⟩
        convert main_r2_q0 e using 2
      · -- m>=1, d=3*(m+1)+1=3m+4, D=3m+5
        have he : e ≥ m + 1 := by omega
        obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le he
        refine ⟨⟨0, 0, 0, 5 * m + 10, e' + 5 * m + 8 + 1⟩,
          ⟨5 * m + 9, e' + 5 * m + 8, rfl, by omega⟩, ?_⟩
        convert main_r2_qpos m e' using 2; ring_nf
    · -- d = 2 mod 3: d = 3*m + 2, D = 3*m + 3 = 3*(m+1)
      have hd : d = 3 * (d / 3) + 2 := by omega
      rw [hd]; set m := d / 3
      have he : e ≥ m + 1 := by omega
      obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le he
      refine ⟨⟨0, 0, 0, 5 * m + 10, e' + 5 * m + 6 + 1⟩,
        ⟨5 * m + 9, e' + 5 * m + 6, rfl, by omega⟩, ?_⟩
      convert main_r0 m e' using 2; ring_nf
  · exact ⟨1, 0, rfl, by omega⟩

end Sz22_2003_unofficial_373
