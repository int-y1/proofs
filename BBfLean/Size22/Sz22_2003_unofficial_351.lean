import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #351: [2/15, 1/98, 1/3, 429/2, 35/11, 2/13]

Vector representation:
```
 1 -1 -1  0  0  0
-1  0  0 -2  0  0
 0 -1  0  0  0  0
-1  1  0  0  1  1
 0  0  1  1 -1  0
 1  0  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_351

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+2, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

theorem phase_A : ∀ e c d f,
    ⟨0, 0, c, d, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + e, d + e, 0, f⟩ := by
  intro e; induction e with
  | zero => intro c d f; exists 0
  | succ e ih =>
    intro c d f; step fm
    apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem r6r2_loop : ∀ k c d f,
    ⟨0, 0, c, d + 2*k, 0, f + k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, 0, f⟩ := by
  intro k; induction k with
  | zero => intro c d f; exists 0
  | succ k ih =>
    intro c d f
    rw [show d + 2 * (k + 1) = d + 2 * k + 2 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem r1r4_d0 : ∀ n c e f,
    ⟨0, 1, c + n, 0, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 1, c, 0, e + n, f + n⟩ := by
  intro n; induction n with
  | zero => intro c e f; exists 0
  | succ n ih =>
    intro c e f
    rw [show c + (n + 1) = (c + n) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem r1r4_d1 : ∀ n c e f,
    ⟨0, 1, c + n, 1, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 1, c, 1, e + n, f + n⟩ := by
  intro n; induction n with
  | zero => intro c e f; exists 0
  | succ n ih =>
    intro c e f
    rw [show c + (n + 1) = (c + n) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _); ring_nf; finish

-- S0 even as stepStar. Uses (f+1)+k as the f-slot value.
-- Output: (0,0,0,0,1+2k,(f+1)+2k)
theorem trans_S0_even_star (k f : ℕ) :
    ⟨0, 0, 0, 0, 2*k, (f+1)+k⟩ [fm]⊢*
    ⟨(0 : ℕ), 0, 0, 0, 1 + 2*k, (f+1)+2*k⟩ := by
  apply stepStar_trans (phase_A (2*k) 0 0 ((f+1)+k))
  apply stepStar_trans (r6r2_loop k (0 + 2*k) 0 (f+1))
  apply stepStar_trans (step_stepStar (show fm ⟨0, 0, 0 + 2*k, 0, 0, f+1⟩ = _ from rfl))
  apply stepStar_trans (step_stepStar (show fm ⟨1, 0, 0 + 2*k, 0, 0, f⟩ = _ from rfl))
  apply stepStar_trans (r1r4_d0 (2*k) 0 1 (f+1))
  step fm; finish

-- S0 odd as stepStar
theorem trans_S0_odd_star (k f : ℕ) :
    ⟨0, 0, 0, 0, 2*k+1, (f+1)+k⟩ [fm]⊢*
    ⟨(0 : ℕ), 0, 0, 1, 1 + (2*k+1), (f+1)+(2*k+1)⟩ := by
  apply stepStar_trans (phase_A (2*k+1) 0 0 ((f+1)+k))
  conv in (occs := 2) 0 + (2 * k + 1) => rw [show (0 + (2*k+1) : ℕ) = 1 + 2*k from by omega]
  apply stepStar_trans (r6r2_loop k (0+(2*k+1)) 1 (f+1))
  apply stepStar_trans (step_stepStar (show fm ⟨0, 0, 0+(2*k+1), 1, 0, f+1⟩ = _ from rfl))
  apply stepStar_trans (step_stepStar (show fm ⟨1, 0, 0+(2*k+1), 1, 0, f⟩ = _ from rfl))
  apply stepStar_trans (r1r4_d1 (2*k+1) 0 1 (f+1))
  step fm; finish

-- S1 even as stepStar
theorem trans_S1_even_star (k f : ℕ) :
    ⟨0, 0, 0, 1, 2*k, (f+1)+k⟩ [fm]⊢*
    ⟨(0 : ℕ), 0, 0, 1, 1 + 2*k, (f+1)+2*k⟩ := by
  apply stepStar_trans (phase_A (2*k) 0 1 ((f+1)+k))
  apply stepStar_trans (r6r2_loop k (0+2*k) 1 (f+1))
  apply stepStar_trans (step_stepStar (show fm ⟨0, 0, 0+2*k, 1, 0, f+1⟩ = _ from rfl))
  apply stepStar_trans (step_stepStar (show fm ⟨1, 0, 0+2*k, 1, 0, f⟩ = _ from rfl))
  apply stepStar_trans (r1r4_d1 (2*k) 0 1 (f+1))
  step fm; finish

-- S1 odd as stepStar
theorem trans_S1_odd_star (k f : ℕ) :
    ⟨0, 0, 0, 1, 2*k+1, (f+1)+(k+1)⟩ [fm]⊢*
    ⟨(0 : ℕ), 0, 0, 0, 1 + (2*k+1), (f+1)+(2*k+1)⟩ := by
  apply stepStar_trans (phase_A (2*k+1) 0 1 ((f+1)+(k+1)))
  conv in (occs := 1) 1 + (2 * k + 1) => rw [show (1 + (2*k+1) : ℕ) = 0 + 2*(k+1) from by omega]
  apply stepStar_trans (r6r2_loop (k+1) (0+(2*k+1)) 0 (f+1))
  apply stepStar_trans (step_stepStar (show fm ⟨0, 0, 0+(2*k+1), 0, 0, f+1⟩ = _ from rfl))
  apply stepStar_trans (step_stepStar (show fm ⟨1, 0, 0+(2*k+1), 0, 0, f⟩ = _ from rfl))
  apply stepStar_trans (r1r4_d0 (2*k+1) 0 1 (f+1))
  step fm; finish

-- Chain 4 transitions: S0 odd -> S1 even -> S1 odd -> S0 even
theorem main_cycle (k f : ℕ) :
    ⟨0, 0, 0, 0, 2*k+1, (f+1)+k⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 0, 2*(k+2)+1, ((f+4*k+3)+1)+(k+2)⟩ := by
  have h1 := trans_S0_odd_star k f
  have h2 := trans_S1_even_star (k+1) (f+k)
  have h3 := trans_S1_odd_star (k+1) (f+2*k)
  have h4 := trans_S0_even_star (k+2) (f+3*k+1)
  have h12 : ⟨0,0,0,0,2*k+1,(f+1)+k⟩ [fm]⊢* ⟨(0:ℕ),0,0,1,1+2*(k+1),((f+k)+1)+2*(k+1)⟩ := by
    apply stepStar_trans h1
    rw [show (1+(2*k+1) : ℕ) = 2*(k+1) from by omega,
        show ((f+1)+(2*k+1) : ℕ) = ((f+k)+1)+(k+1) from by omega]
    exact h2
  have h123 : ⟨0,0,0,0,2*k+1,(f+1)+k⟩ [fm]⊢* ⟨(0:ℕ),0,0,0,1+(2*(k+1)+1),((f+2*k)+1)+(2*(k+1)+1)⟩ := by
    apply stepStar_trans h12
    rw [show (1+2*(k+1) : ℕ) = 2*(k+1)+1 from by omega,
        show (((f+k)+1)+2*(k+1) : ℕ) = ((f+2*k)+1)+((k+1)+1) from by omega]
    exact h3
  have h1234 : ⟨0,0,0,0,2*k+1,(f+1)+k⟩ [fm]⊢* ⟨(0:ℕ),0,0,0,1+2*(k+2),((f+3*k+1)+1)+2*(k+2)⟩ := by
    apply stepStar_trans h123
    rw [show (1+(2*(k+1)+1) : ℕ) = 2*(k+2) from by omega,
        show (((f+2*k)+1)+(2*(k+1)+1) : ℕ) = ((f+3*k+1)+1)+(k+2) from by omega]
    exact h4
  have final : ⟨0,0,0,0,2*k+1,(f+1)+k⟩ [fm]⊢* ⟨(0:ℕ),0,0,0,2*(k+2)+1,((f+4*k+3)+1)+(k+2)⟩ := by
    apply stepStar_trans h1234
    rw [show (1+2*(k+2) : ℕ) = 2*(k+2)+1 from by omega,
        show (((f+3*k+1)+1)+2*(k+2) : ℕ) = ((f+4*k+3)+1)+(k+2) from by omega]
    finish
  exact stepStar_stepPlus final (by
    intro h; simp only [Q, Prod.mk.injEq] at h; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 2)
  -- (0,0,0,0,1,1) = (0,0,0,0,2*0+1,(0+1)+0) so k=0, f=0.
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, f⟩ ↦ ⟨0, 0, 0, 0, 2*k + 1, (f+1)+k⟩) ⟨0, 0⟩
  intro ⟨k, f⟩
  exact ⟨⟨k + 2, f + 4*k + 3⟩, main_cycle k f⟩

end Sz22_2003_unofficial_351
