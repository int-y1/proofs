import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #616: [35/6, 121/2, 8/55, 3/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 3  0 -1  0 -1
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_616

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 chain: (0,b,0,d+k,e) →* (0,b+k,0,d,e)
theorem r4_chain : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have h : ∀ k b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k ih <;> intro b d
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _); ring_nf; finish
  exact h k b d

-- Opening: (0, d+1, 0, 0, e+2) →⁺ (3, d, 0, 2, e)
theorem opening : ⟨0, d+1, 0, 0, e+2⟩ [fm]⊢⁺ ⟨3, d, 0, 2, e⟩ := by
  step fm; step fm; step fm; finish

-- R1R3 chain: k full rounds
-- (3, b+3k, c, D, e+k) →* (3, b, c+2k, D+3k, e)
theorem r1r3_chain : ⟨3, b+3*k, c, D, e+k⟩ [fm]⊢* ⟨3, b, c+2*k, D+3*k, e⟩ := by
  have h : ∀ k b c D e, ⟨3, b+3*k, c, D, e+k⟩ [fm]⊢* ⟨3, b, c+2*k, D+3*k, e⟩ := by
    intro k; induction' k with k ih <;> intro b c D e
    · exists 0
    rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih _ _ _ _); ring_nf; finish
  exact h k b c D e

-- R2 drain: (a, 0, c, D, e) →* (0, 0, c, D, e+2a)
theorem r2_drain : ⟨a, (0 : ℕ), c, D, e⟩ [fm]⊢* ⟨0, 0, c, D, e+2*a⟩ := by
  have h : ∀ a e, ⟨a, (0 : ℕ), c, D, e⟩ [fm]⊢* ⟨0, 0, c, D, e+2*a⟩ := by
    intro a; induction' a with a ih <;> intro e
    · exists 0
    step fm
    apply stepStar_trans (ih _); ring_nf; finish
  exact h a e

-- R3R2R2R2 chain: (0, 0, c+k, D, e+k) →* (0, 0, c, D, e+6k)
theorem r3r2_chain : ⟨0, (0 : ℕ), c+k, D, e+k⟩ [fm]⊢* ⟨0, 0, c, D, e+6*k⟩ := by
  have h : ∀ k c e, ⟨0, (0 : ℕ), c+k, D, e+k⟩ [fm]⊢* ⟨0, 0, c, D, e+6*k⟩ := by
    intro k; induction' k with k ih <;> intro c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show e + k + 2 + 2 + 2 = (e + 6) + k from by ring]
    apply stepStar_trans (ih _ _); ring_nf; finish
  exact h k c e

-- Full cycle: mod 0 case
-- (0,0,0,3q+1,f+3q+3) →⁺ (0,0,0,3q+2,f+12q+7)
theorem trans_mod0 (q f : ℕ) : ⟨0, 0, 0, 3*q+1, f+3*q+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*q+2, f+12*q+7⟩ := by
  -- Phase 1: R4 chain
  have h1 : ⟨0, 0, 0, 3*q+1, f+3*q+3⟩ [fm]⊢* ⟨0, 3*q+1, 0, 0, f+3*q+3⟩ := by
    have := r4_chain (b := 0) (d := 0) (k := 3*q+1) (e := f+3*q+3)
    simp only [Nat.zero_add] at this; exact this
  have h2 : ⟨0, 3*q+1, 0, 0, f+3*q+3⟩ [fm]⊢⁺ ⟨3, 3*q, 0, 2, f+3*q+1⟩ := by
    rw [show (3 : ℕ)*q + 1 = 3*q + 1 from rfl,
        show f + 3*q + 3 = (f + 3*q + 1) + 2 from by ring]; exact opening
  have h3 : ⟨3, 3*q, 0, 2, f+3*q+1⟩ [fm]⊢* ⟨3, 0, 2*q, 3*q+2, f+2*q+1⟩ := by
    have := r1r3_chain (b := 0) (k := q) (c := 0) (D := 2) (e := f+2*q+1)
    simp only [Nat.zero_add] at this
    rw [show f+2*q+1+q = f+3*q+1 from by ring,
        show (2 : ℕ)+3*q = 3*q+2 from by ring] at this; exact this
  have h4 : ⟨3, 0, 2*q, 3*q+2, f+2*q+1⟩ [fm]⊢* ⟨0, 0, 2*q, 3*q+2, f+2*q+7⟩ := by
    have := r2_drain (a := 3) (c := 2*q) (D := 3*q+2) (e := f+2*q+1)
    rw [show f+2*q+1+2*3 = f+2*q+7 from by ring] at this; exact this
  have h5 : ⟨0, 0, 2*q, 3*q+2, f+2*q+7⟩ [fm]⊢* ⟨0, 0, 0, 3*q+2, f+12*q+7⟩ := by
    have := r3r2_chain (c := 0) (k := 2*q) (D := 3*q+2) (e := f+7)
    simp only [Nat.zero_add] at this
    rw [show f+7+2*q = f+2*q+7 from by ring,
        show f+7+6*(2*q) = f+12*q+7 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2
    (stepStar_trans h3 (stepStar_trans h4 h5)))

-- Full cycle: mod 1 case
theorem trans_mod1 (q f : ℕ) : ⟨0, 0, 0, 3*q+2, f+3*q+4⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*q+3, f+12*q+11⟩ := by
  have h1 : ⟨0, 0, 0, 3*q+2, f+3*q+4⟩ [fm]⊢* ⟨0, 3*q+2, 0, 0, f+3*q+4⟩ := by
    have := r4_chain (b := 0) (d := 0) (k := 3*q+2) (e := f+3*q+4)
    simp only [Nat.zero_add] at this; exact this
  have h2 : ⟨0, 3*q+2, 0, 0, f+3*q+4⟩ [fm]⊢⁺ ⟨3, 3*q+1, 0, 2, f+3*q+2⟩ := by
    rw [show (3 : ℕ)*q+2 = (3*q+1)+1 from by ring,
        show f+3*q+4 = (f+3*q+2)+2 from by ring]; exact opening
  have h3 : ⟨3, 3*q+1, 0, 2, f+3*q+2⟩ [fm]⊢* ⟨3, 1, 2*q, 3*q+2, f+2*q+2⟩ := by
    have := r1r3_chain (b := 1) (k := q) (c := 0) (D := 2) (e := f+2*q+2)
    simp only [Nat.zero_add] at this
    rw [show f+2*q+2+q = f+3*q+2 from by ring,
        show (1 : ℕ)+3*q = 3*q+1 from by ring,
        show (2 : ℕ)+3*q = 3*q+2 from by ring] at this; exact this
  have h4a : ⟨3, 1, 2*q, 3*q+2, f+2*q+2⟩ [fm]⊢* ⟨2, 0, 2*q+1, 3*q+3, f+2*q+2⟩ := by
    step fm; finish
  have h4b : ⟨2, 0, 2*q+1, 3*q+3, f+2*q+2⟩ [fm]⊢* ⟨0, 0, 2*q+1, 3*q+3, f+2*q+6⟩ := by
    have := r2_drain (a := 2) (c := 2*q+1) (D := 3*q+3) (e := f+2*q+2)
    rw [show f+2*q+2+2*2 = f+2*q+6 from by ring] at this; exact this
  have h5 : ⟨0, 0, 2*q+1, 3*q+3, f+2*q+6⟩ [fm]⊢* ⟨0, 0, 0, 3*q+3, f+12*q+11⟩ := by
    have := r3r2_chain (c := 0) (k := 2*q+1) (D := 3*q+3) (e := f+5)
    simp only [Nat.zero_add] at this
    rw [show f+5+(2*q+1) = f+2*q+6 from by ring,
        show f+5+6*(2*q+1) = f+12*q+11 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2
    (stepStar_trans h3 (stepStar_trans h4a (stepStar_trans h4b h5))))

-- Full cycle: mod 2 case
theorem trans_mod2 (q f : ℕ) : ⟨0, 0, 0, 3*q+3, f+3*q+5⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*q+4, f+12*q+15⟩ := by
  have h1 : ⟨0, 0, 0, 3*q+3, f+3*q+5⟩ [fm]⊢* ⟨0, 3*q+3, 0, 0, f+3*q+5⟩ := by
    have := r4_chain (b := 0) (d := 0) (k := 3*q+3) (e := f+3*q+5)
    simp only [Nat.zero_add] at this; exact this
  have h2 : ⟨0, 3*q+3, 0, 0, f+3*q+5⟩ [fm]⊢⁺ ⟨3, 3*q+2, 0, 2, f+3*q+3⟩ := by
    rw [show (3 : ℕ)*q+3 = (3*q+2)+1 from by ring,
        show f+3*q+5 = (f+3*q+3)+2 from by ring]; exact opening
  have h3 : ⟨3, 3*q+2, 0, 2, f+3*q+3⟩ [fm]⊢* ⟨3, 2, 2*q, 3*q+2, f+2*q+3⟩ := by
    have := r1r3_chain (b := 2) (k := q) (c := 0) (D := 2) (e := f+2*q+3)
    simp only [Nat.zero_add] at this
    rw [show f+2*q+3+q = f+3*q+3 from by ring,
        show (2 : ℕ)+3*q = 3*q+2 from by ring] at this; exact this
  have h4a : ⟨3, 2, 2*q, 3*q+2, f+2*q+3⟩ [fm]⊢* ⟨1, 0, 2*q+2, 3*q+4, f+2*q+3⟩ := by
    step fm; step fm; finish
  have h4b : ⟨1, 0, 2*q+2, 3*q+4, f+2*q+3⟩ [fm]⊢* ⟨0, 0, 2*q+2, 3*q+4, f+2*q+5⟩ := by
    have := r2_drain (a := 1) (c := 2*q+2) (D := 3*q+4) (e := f+2*q+3)
    rw [show f+2*q+3+2*1 = f+2*q+5 from by ring] at this; exact this
  have h5 : ⟨0, 0, 2*q+2, 3*q+4, f+2*q+5⟩ [fm]⊢* ⟨0, 0, 0, 3*q+4, f+12*q+15⟩ := by
    have := r3r2_chain (c := 0) (k := 2*q+2) (D := 3*q+4) (e := f+3)
    simp only [Nat.zero_add] at this
    rw [show f+3+(2*q+2) = f+2*q+5 from by ring,
        show f+3+6*(2*q+2) = f+12*q+15 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2
    (stepStar_trans h3 (stepStar_trans h4a (stepStar_trans h4b h5))))

-- Full transition
theorem main_trans (d f : ℕ) :
    ∃ d' f', (⟨0, 0, 0, d+1, f+d+3⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, d'+1, f'+d'+3⟩ := by
  rcases (show d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 from by omega) with h | h | h
  · obtain ⟨q, rfl⟩ : ∃ q, d = 3 * q := ⟨d / 3, by omega⟩
    refine ⟨3*q+1, f+9*q+3, ?_⟩
    rw [show f + 3*q + 3 = f + 3*q + 3 from rfl,
        show (3 : ℕ)*q+1+1 = 3*q + 2 from by ring,
        show f + 9*q + 3 + (3*q+1) + 3 = f + 12*q + 7 from by ring]
    exact trans_mod0 q f
  · obtain ⟨q, rfl⟩ : ∃ q, d = 3 * q + 1 := ⟨d / 3, by omega⟩
    refine ⟨3*q+2, f+9*q+6, ?_⟩
    rw [show f + (3*q+1) + 3 = f + 3*q + 4 from by ring,
        show (3 : ℕ)*q+2+1 = 3*q + 3 from by ring,
        show f + 9*q + 6 + (3*q+2) + 3 = f + 12*q + 11 from by ring]
    exact trans_mod1 q f
  · obtain ⟨q, rfl⟩ : ∃ q, d = 3 * q + 2 := ⟨d / 3, by omega⟩
    refine ⟨3*q+3, f+9*q+9, ?_⟩
    rw [show f + (3*q+2) + 3 = f + 3*q + 5 from by ring,
        show (3 : ℕ)*q+3+1 = 3*q + 4 from by ring,
        show f + 9*q + 9 + (3*q+3) + 3 = f + 12*q + 15 from by ring]
    exact trans_mod2 q f

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0+1, 0+0+3⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, f⟩ ↦ ⟨0, 0, 0, d+1, f+d+3⟩) ⟨0, 0⟩
  intro ⟨d, f⟩
  obtain ⟨d', f', h⟩ := main_trans d f
  exact ⟨⟨d', f'⟩, h⟩

end Sz22_2003_unofficial_616
