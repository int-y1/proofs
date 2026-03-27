import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #78: [1/18, 385/2, 2/65, 1/5, 39/7, 2/11]

Vector representation:
```
-1 -2  0  0  0  0
-1  0  1  1  1  0
 1  0 -1  0  0 -1
 0  0 -1  0  0  0
 0  1  0 -1  0  1
 1  0  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_78

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e+1, f⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

theorem r1r2_b0 : ∀ k, ∀ d e,
    (⟨1, 0, 0, d, e, f+k⟩ : Q) [fm]⊢* ⟨1, 0, 0, d+k, e+k, f⟩ := by
  intro k; induction k with
  | zero => intro d e; exists 0
  | succ k ih =>
    intro d e
    rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

theorem r1r2_b1 : ∀ k, ∀ d e,
    (⟨1, 1, 0, d, e, f+k⟩ : Q) [fm]⊢* ⟨1, 1, 0, d+k, e+k, f⟩ := by
  intro k; induction k with
  | zero => intro d e; exists 0
  | succ k ih =>
    intro d e
    rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

theorem r4 : ∀ k, ∀ b e f,
    (⟨0, b, 0, d+k, e, f⟩ : Q) [fm]⊢* ⟨0, b+k, 0, d, e, f+k⟩ := by
  intro k; induction k with
  | zero => intro b e f; exists 0
  | succ k ih =>
    intro b e f
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem drain_even : ∀ m, ∀ e f,
    (⟨0, 2*m, 0, 0, e+m, f⟩ : Q) [fm]⊢* ⟨0, 0, 0, 0, e, f⟩ := by
  intro m; induction m with
  | zero => intro e f; exists 0
  | succ m ih =>
    intro e f
    rw [show 2 * (m + 1) = (2 * m) + 2 from by ring,
        show e + (m + 1) = (e + m) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

theorem drain_odd : ∀ m, ∀ e f,
    (⟨0, 2*m+1, 0, 0, e+m, f⟩ : Q) [fm]⊢* ⟨0, 1, 0, 0, e, f⟩ := by
  intro m; induction m with
  | zero => intro e f; exists 0
  | succ m ih =>
    intro e f
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 from by ring,
        show e + (m + 1) = (e + m) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

-- Sub-round type 1: b=0, f odd (2j+1)
-- (1,0,0,0,e,2j+1) ⊢⁺ (1,0,0,0,e+j,2j+2)
theorem sr_b0_fodd (e : ℕ) :
    (⟨1, 0, 0, 0, e, 2*j+1⟩ : Q) [fm]⊢⁺ ⟨1, 0, 0, 0, e+j, 2*j+2⟩ := by
  rw [show (2*j+1 : ℕ) = 0 + (2*j+1) from by ring]
  apply stepStar_stepPlus_stepPlus (r1r2_b0 (2*j+1) 0 e)
  simp only [Nat.zero_add]
  step fm; step fm
  rw [show (2*j+1+1 : ℕ) = 0 + (2*j+2) from by ring,
      show e+(2*j+1)+1 = e+2*j+2 from by ring]
  apply stepStar_trans (r4 (2*j+2) 0 (e+2*j+2) 0)
  simp only [Nat.zero_add]
  rw [show (2*j+2 : ℕ) = 2*(j+1) from by ring,
      show e+2*j+2 = (e+j+1) + (j+1) from by ring]
  apply stepStar_trans (drain_even (j+1) (e+j+1) (2*j+2))
  rw [show e+j+1 = (e+j) + 1 from by ring]
  step fm; finish

-- Sub-round type 2: b=0, f even (2j+2)
-- (1,0,0,0,e,2j+2) ⊢⁺ (0,1,0,0,e+j+2,2j+3)
theorem sr_b0_feven (e : ℕ) :
    (⟨1, 0, 0, 0, e, 2*j+2⟩ : Q) [fm]⊢⁺ ⟨0, 1, 0, 0, e+j+2, 2*j+3⟩ := by
  rw [show (2*j+2 : ℕ) = 0 + (2*j+2) from by ring]
  apply stepStar_stepPlus_stepPlus (r1r2_b0 (2*j+2) 0 e)
  simp only [Nat.zero_add]
  step fm; step fm
  rw [show (2*j+2+1 : ℕ) = 0 + (2*j+3) from by ring,
      show e+(2*j+2)+1 = e+2*j+3 from by ring]
  apply stepStar_trans (r4 (2*j+3) 0 (e+2*j+3) 0)
  simp only [Nat.zero_add]
  rw [show (2*j+3 : ℕ) = 2*(j+1)+1 from by ring,
      show e+2*j+3 = (e+j+2) + (j+1) from by ring]
  apply stepStar_trans (drain_odd (j+1) (e+j+2) (2*j+3))
  ring_nf; finish

-- Sub-round type 3: b=1, f odd (2j+1)
-- (0,1,0,0,e+1,2j+1) ⊢⁺ (0,1,0,0,e+j+1,2j+2)
theorem sr_b1_fodd (e : ℕ) :
    (⟨0, 1, 0, 0, e+1, 2*j+1⟩ : Q) [fm]⊢⁺ ⟨0, 1, 0, 0, e+j+1, 2*j+2⟩ := by
  rw [show e+1 = e + 1 from by ring]; step fm
  rw [show (2*j+1 : ℕ) = 0 + (2*j+1) from by ring]
  apply stepStar_trans (r1r2_b1 (2*j+1) 0 e)
  simp only [Nat.zero_add]
  step fm; step fm
  rw [show (2*j+1+1 : ℕ) = 0 + (2*j+2) from by ring,
      show e+(2*j+1)+1 = e+2*j+2 from by ring]
  apply stepStar_trans (r4 (2*j+2) 1 (e+2*j+2) 0)
  simp only [Nat.zero_add]
  rw [show 1+(2*j+2) = 2*(j+1)+1 from by ring,
      show e+2*j+2 = (e+j+1) + (j+1) from by ring]
  apply stepStar_trans (drain_odd (j+1) (e+j+1) (2*j+2))
  ring_nf; finish

-- Sub-round type 4: b=1, f even (2j+2)
-- (0,1,0,0,e+1,2j+2) ⊢⁺ (1,0,0,0,e+j,2j+3)
theorem sr_b1_feven (e : ℕ) :
    (⟨0, 1, 0, 0, e+1, 2*j+2⟩ : Q) [fm]⊢⁺ ⟨1, 0, 0, 0, e+j, 2*j+3⟩ := by
  rw [show e+1 = e + 1 from by ring]; step fm
  rw [show (2*j+2 : ℕ) = 0 + (2*j+2) from by ring]
  apply stepStar_trans (r1r2_b1 (2*j+2) 0 e)
  simp only [Nat.zero_add]
  step fm; step fm
  rw [show (2*j+2+1 : ℕ) = 0 + (2*j+3) from by ring,
      show e+(2*j+2)+1 = e+2*j+3 from by ring]
  apply stepStar_trans (r4 (2*j+3) 1 (e+2*j+3) 0)
  simp only [Nat.zero_add]
  rw [show 1+(2*j+3) = 2*(j+2) from by ring,
      show e+2*j+3 = (e+j+1) + (j+2) from by ring]
  apply stepStar_trans (drain_even (j+2) (e+j+1) (2*j+3))
  rw [show e+j+1 = (e+j) + 1 from by ring]
  step fm; finish

-- C(k) = (1,0,0,0, 4k²+3k, 4k+3). Prove C(k) ⊢⁺ C(k+1).
theorem main_trans :
    (⟨1, 0, 0, 0, 4*k*k+3*k, 4*k+3⟩ : Q) [fm]⊢⁺
    ⟨1, 0, 0, 0, 4*(k+1)*(k+1)+3*(k+1), 4*(k+1)+3⟩ := by
  -- SR1: sr_b0_fodd j=2k+1: f=4k+3=2(2k+1)+1
  rw [show (4*k+3 : ℕ) = 2*(2*k+1)+1 from by ring]
  apply stepPlus_stepStar_stepPlus (sr_b0_fodd (j := 2*k+1) (4*k*k+3*k))
  -- → (1,0,0,0, 4k²+5k+1, 4k+4)
  -- SR2: sr_b0_feven j=2k+1: f=4k+4=2(2k+1)+2
  rw [show 4*k*k+3*k+(2*k+1) = 4*k*k+5*k+1 from by ring,
      show 2*(2*k+1)+2 = 2*(2*k+1)+2 from by ring]
  apply stepStar_trans (stepPlus_stepStar (sr_b0_feven (j := 2*k+1) (4*k*k+5*k+1)))
  -- → (0,1,0,0, 4k²+7k+4, 4k+5)
  -- SR3: sr_b1_fodd j=2k+2: f=4k+5=2(2k+2)+1
  rw [show 4*k*k+5*k+1+(2*k+1)+2 = (4*k*k+7*k+3)+1 from by ring,
      show 2*(2*k+1)+3 = 2*(2*k+2)+1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (sr_b1_fodd (j := 2*k+2) (4*k*k+7*k+3)))
  -- → (0,1,0,0, 4k²+9k+6, 4k+6)
  -- SR4: sr_b1_feven j=2k+2: f=4k+6=2(2k+2)+2
  rw [show 4*k*k+7*k+3+(2*k+2)+1 = (4*k*k+9*k+5)+1 from by ring,
      show 2*(2*k+2)+2 = 2*(2*k+2)+2 from by ring]
  apply stepStar_trans (stepPlus_stepStar (sr_b1_feven (j := 2*k+2) (4*k*k+9*k+5)))
  -- → (1,0,0,0, 4k²+11k+7, 4k+7) = C(k+1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 3⟩)
  · execute fm 27
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨1, 0, 0, 0, 4*k*k+3*k, 4*k+3⟩) 0
  intro k; exists k+1; exact main_trans

end Sz22_2003_unofficial_78
