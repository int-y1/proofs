import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #381: [2/15, 99/14, 1375/2, 7/11, 2/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  3  0  1
 0  0  0  1 -1
 1  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_381

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem e_to_d : ∀ k c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih c _ e); ring_nf; finish

theorem r2r1r1_iter : ∀ k a c d e,
    ⟨a + 1, 0, c + 2 * k, d + k, e⟩ [fm]⊢* ⟨a + 1 + k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (a + 1) c d (e + 1)); ring_nf; finish

theorem r2_chain : ∀ k a b d e,
    ⟨a + k, b, 0, d + k, e⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring, ← Nat.add_assoc]; step fm
  apply stepStar_trans (ih a (b + 2) d (e + 1)); ring_nf; finish

theorem r3_drain : ∀ k a c e,
    ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih a (c + 3) (e + 1)); ring_nf; finish

theorem drain_combine : ∀ B : ℕ, ∀ A E,
    ⟨A + 1, B, 0, 0, E⟩ [fm]⊢* ⟨0, 0, 3 * A + 2 * B + 3, 0, E + A + B + 1⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro A E
  rcases B with _ | _ | _ | _ | B
  · rw [show A + 1 = 0 + (A + 1) from by ring,
        show 3 * A + 2 * 0 + 3 = 0 + 3 * (A + 1) from by ring,
        show E + A + 0 + 1 = E + (A + 1) from by ring]
    exact r3_drain (A + 1) 0 0 E
  · step fm; step fm
    rw [show A + 1 = 0 + (A + 1) from by ring,
        show 3 * A + 2 * 1 + 3 = 2 + 3 * (A + 1) from by ring,
        show E + A + 1 + 1 = (E + 1) + (A + 1) from by ring]
    exact r3_drain (A + 1) 0 2 (E + 1)
  · step fm; step fm; step fm
    rw [show A + 1 + 1 = 0 + (A + 2) from by ring,
        show 3 * A + 2 * 2 + 3 = 1 + 3 * (A + 2) from by ring,
        show E + A + 2 + 1 = (E + 1) + (A + 2) from by ring]
    exact r3_drain (A + 2) 0 1 (E + 1)
  · step fm; step fm; step fm; step fm
    rw [show A + 1 + 1 + 1 = 0 + (A + 3) from by ring,
        show 3 * A + 2 * 3 + 3 = 0 + 3 * (A + 3) from by ring,
        show E + A + 3 + 1 = (E + 1) + (A + 3) from by ring]
    exact r3_drain (A + 3) 0 0 (E + 1)
  · step fm; step fm; step fm; step fm
    rw [show A + 1 + 1 + 1 = (A + 2) + 1 from by ring]
    apply stepStar_trans (ih (B + 1) (by omega) (A + 2) (E + 1)); ring_nf; finish

-- Case A: g >= e. c_val = g + e + 3 (with g being the actual gap from cycle_step).
-- Here we parameterize by g' = g - e (since g >= e), so c_val = (g' + e) + e + 3 = g' + 2e + 3.
-- After r2r1r1 (e+1): (e+2, 0, g', 0, e+1). Then r3_drain.
theorem main_trans_A (g' e : ℕ) :
    ⟨0, 0, g' + 2 * e + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, g' + 3 * e + 6, 0, 2 * e + 3⟩ := by
  have he2d : ⟨0, 0, g' + 2 * e + 3, 0, e + 1⟩ [fm]⊢* ⟨0, 0, g' + 2 * e + 3, e + 1, 0⟩ := by
    rw [show e + 1 = 0 + (e + 1) from by ring]; exact e_to_d (e + 1) (g' + 2 * e + 3) 0 0
  apply stepStar_stepPlus_stepPlus he2d
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, g' + 2 * e + 3, e + 1, 0⟩ = some ⟨1, 0, g' + 2 * e + 2, e + 1, 0⟩; rfl
  -- r2r1r1 (e+1): (1, 0, g'+2e+2, e+1, 0) -> (e+2, 0, g', 0, e+1)
  have hr := r2r1r1_iter (e + 1) 0 g' 0 0
  simp only [Nat.zero_add, show g' + 2 * (e + 1) = g' + 2 * e + 2 from by ring,
             show 1 + (e + 1) = e + 2 from by ring] at hr
  -- hr : (1, 0, g'+2e+2, e+1, 0) ⊢* (e+2, 0, g', 0, e+1)
  apply stepStar_trans hr
  rw [show e + 2 = 0 + (e + 2) from by ring,
      show g' + 3 * e + 6 = g' + 3 * (e + 2) from by ring,
      show 2 * e + 3 = (e + 1) + (e + 2) from by ring]
  exact r3_drain (e + 2) 0 g' (e + 1)

-- Case B even: g+e = 2p, g < e.
theorem main_trans_Beven (p e : ℕ) (hp : 2 * p ≥ e) (hpe : p < e) :
    ⟨0, 0, 2 * p + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 2 * p + e + 6, 0, 2 * e + 3⟩ := by
  have he2d : ⟨0, 0, 2 * p + 3, 0, e + 1⟩ [fm]⊢* ⟨0, 0, 2 * p + 3, e + 1, 0⟩ := by
    rw [show e + 1 = 0 + (e + 1) from by ring]; exact e_to_d (e + 1) (2 * p + 3) 0 0
  apply stepStar_stepPlus_stepPlus he2d
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2 * p + 3, e + 1, 0⟩ = some ⟨1, 0, 2 * p + 2, e + 1, 0⟩; rfl
  -- r2r1r1 (p+1)
  have hr := r2r1r1_iter (p + 1) 0 0 (e - p) 0
  simp only [Nat.zero_add, show 0 + 2 * (p + 1) = 2 * p + 2 from by ring,
             show (e - p) + (p + 1) = e + 1 from by omega,
             show 0 + 1 + (p + 1) = p + 2 from by ring] at hr
  apply stepStar_trans hr
  -- r2_chain (e-p)
  have hc := r2_chain (e - p) (2 * p + 2 - e) 0 0 (p + 1)
  simp only [show (2 * p + 2 - e) + (e - p) = p + 2 from by omega,
             show 0 + (e - p) = e - p from by ring,
             show 0 + 2 * (e - p) = 2 * e - 2 * p from by omega,
             show (p + 1) + (e - p) = e + 1 from by omega] at hc
  apply stepStar_trans hc
  -- drain_combine
  have hdr := drain_combine (2 * e - 2 * p) (2 * p + 1 - e) (e + 1)
  simp only [show (2 * p + 1 - e) + 1 = 2 * p + 2 - e from by omega,
             show 3 * (2 * p + 1 - e) + 2 * (2 * e - 2 * p) + 3 = 2 * p + e + 6 from by omega,
             show (e + 1) + (2 * p + 1 - e) + (2 * e - 2 * p) + 1 = 2 * e + 3 from by omega] at hdr
  exact hdr

-- Case B odd: g+e = 2p+1, g < e.
theorem main_trans_Bodd (p e : ℕ) (hp : 2 * p + 1 ≥ e) (hpe : p < e) :
    ⟨0, 0, 2 * p + 4, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 2 * p + e + 7, 0, 2 * e + 3⟩ := by
  have he2d : ⟨0, 0, 2 * p + 4, 0, e + 1⟩ [fm]⊢* ⟨0, 0, 2 * p + 4, e + 1, 0⟩ := by
    rw [show e + 1 = 0 + (e + 1) from by ring]; exact e_to_d (e + 1) (2 * p + 4) 0 0
  apply stepStar_stepPlus_stepPlus he2d
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2 * p + 4, e + 1, 0⟩ = some ⟨1, 0, 2 * p + 3, e + 1, 0⟩; rfl
  -- r2r1r1 (p+1)
  have hr := r2r1r1_iter (p + 1) 0 1 (e - p) 0
  simp only [Nat.zero_add, show 1 + 2 * (p + 1) = 2 * p + 3 from by ring,
             show (e - p) + (p + 1) = e + 1 from by omega,
             show 0 + 1 + (p + 1) = p + 2 from by ring] at hr
  apply stepStar_trans hr
  -- R2 then R1: (p+2, 0, 1, e-p, p+1) -> (p+1, 2, 1, e-p-1, p+2) -> (p+2, 1, 0, e-p-1, p+2)
  have hstep1 : ⟨p + 2, 0, 1, e - p, p + 1⟩ [fm]⊢* ⟨p + 2, 1, 0, e - p - 1, p + 2⟩ := by
    rw [show e - p = (e - p - 1) + 1 from by omega]; step fm; step fm; finish
  apply stepStar_trans hstep1
  -- r2_chain (e-p-1)
  have hc := r2_chain (e - p - 1) (2 * p + 3 - e) 1 0 (p + 2)
  simp only [show (2 * p + 3 - e) + (e - p - 1) = p + 2 from by omega,
             show 0 + (e - p - 1) = e - p - 1 from by ring,
             show 1 + 2 * (e - p - 1) = 2 * e - 2 * p - 1 from by omega,
             show (p + 2) + (e - p - 1) = e + 1 from by omega] at hc
  apply stepStar_trans hc
  -- drain_combine
  have hdr := drain_combine (2 * e - 2 * p - 1) (2 * p + 2 - e) (e + 1)
  simp only [show (2 * p + 2 - e) + 1 = 2 * p + 3 - e from by omega,
             show 3 * (2 * p + 2 - e) + 2 * (2 * e - 2 * p - 1) + 3 = 2 * p + e + 7 from by omega,
             show (e + 1) + (2 * p + 2 - e) + (2 * e - 2 * p - 1) + 1 = 2 * e + 3 from by omega] at hdr
  exact hdr

theorem cycle_step (g e : ℕ) :
    ⟨0, 0, g + e + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, g + 2 * e + 6, 0, 2 * e + 3⟩ := by
  by_cases he : g ≥ e
  · rw [show g + e + 3 = (g - e) + 2 * e + 3 from by omega,
        show g + 2 * e + 6 = (g - e) + 3 * e + 6 from by omega]
    exact main_trans_A (g - e) e
  · push_neg at he
    rcases Nat.even_or_odd (g + e) with ⟨p, hp⟩ | ⟨p, hp⟩
    · rw [show g + e + 3 = 2 * p + 3 from by omega,
          show g + 2 * e + 6 = 2 * p + e + 6 from by omega]
      exact main_trans_Beven p e (by omega) (by omega)
    · rw [show g + e + 3 = 2 * p + 4 from by omega,
          show g + 2 * e + 6 = 2 * p + e + 7 from by omega]
      exact main_trans_Bodd p e (by omega) (by omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨g, e⟩ ↦ ⟨0, 0, g + e + 3, 0, e + 1⟩) ⟨0, 0⟩
  intro ⟨g, e⟩
  exact ⟨⟨g + 1, 2 * e + 2⟩, by
    show ⟨0, 0, g + e + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, (g + 1) + (2 * e + 2) + 3, 0, (2 * e + 2) + 1⟩
    rw [show (g + 1) + (2 * e + 2) + 3 = g + 2 * e + 6 from by ring,
        show (2 * e + 2) + 1 = 2 * e + 3 from by ring]
    exact cycle_step g e⟩

end Sz22_2003_unofficial_381
