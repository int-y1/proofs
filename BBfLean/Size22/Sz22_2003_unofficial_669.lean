import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #669: [35/6, 28/55, 121/2, 3/7, 5/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  1 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_669

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move d to b
theorem d_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b d; exists 0
  | succ k ih =>
    intro b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b + 1) d); ring_nf; finish

-- R3 repeated: drain a to e
theorem r3_chain : ∀ k, ∀ a e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a (e + 2)); ring_nf; finish

-- R2 repeated when b=0
theorem r2_chain : ∀ k, ∀ a c d₀ e₀,
    ⟨a, 0, c + k + 1, d₀, e₀ + k + 1⟩ [fm]⊢* ⟨a + 2 * k + 2, 0, c, d₀ + k + 1, e₀⟩ := by
  intro k; induction k with
  | zero => intro a c d₀ e₀; step fm; finish
  | succ k ih =>
    intro a c d₀ e₀
    rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring,
        show e₀ + (k + 1) + 1 = (e₀ + k + 1) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 2) c (d₀ + 1) e₀); ring_nf; finish

-- Interleaved R1-R1-R2 chain
theorem interleaved : ∀ k, ∀ b c d₀ e₀,
    ⟨2, b + 2 * k + 2, c, d₀, e₀ + k + 1⟩ [fm]⊢*
    ⟨2, b, c + k + 1, d₀ + 3 * k + 3, e₀⟩ := by
  intro k; induction k with
  | zero =>
    intro b c d₀ e₀
    rw [show b + 2 * 0 + 2 = b + 1 + 1 from by ring]
    step fm; step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from rfl]
    step fm; ring_nf; finish
  | succ k ih =>
    intro b c d₀ e₀
    rw [show b + 2 * (k + 1) + 2 = (b + 2 * k + 2) + 1 + 1 from by ring,
        show e₀ + (k + 1) + 1 = (e₀ + k + 1) + 1 from by ring]
    step fm
    rw [show (b + 2 * k + 2) + 1 = (b + 2 * k + 2) + 1 from rfl]
    step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from rfl]
    step fm
    apply stepStar_trans (ih b (c + 1) (d₀ + 3) e₀); ring_nf; finish

-- R5 then R2 as ⊢⁺
theorem r5_r2_plus (b : ℕ) : ⟨0, b, 0, 0, f + 2⟩ [fm]⊢⁺ ⟨2, b, 0, 1, f⟩ := by
  rw [show f + 2 = (f + 1) + 1 from by ring]
  step fm
  rw [show f + 1 = f + 1 from rfl]
  step fm; finish

-- d_to_b then R5 then R2
theorem setup_phase (d : ℕ) : ⟨0, 0, 0, d + 1, f + 3⟩ [fm]⊢⁺ ⟨2, d + 1, 0, 1, f + 1⟩ := by
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (d + 1) 0 0 (e := f + 3))
  rw [show (0 : ℕ) + (d + 1) = d + 1 from by ring,
      show f + 3 = (f + 1) + 2 from by ring]
  exact r5_r2_plus (d + 1) (f := f + 1)

-- d=0: (0,0,0,0,f+2) ⊢⁺ (0,0,0,1,f+4)
theorem trans_d0 (f : ℕ) : ⟨0, 0, 0, 0, f + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, f + 4⟩ := by
  apply stepPlus_stepStar_stepPlus (r5_r2_plus 0 (f := f))
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (r3_chain 2 0 f (d := 1))
  ring_nf; finish

-- Even d >= 2: (0,0,0,2m+2,2m+4+f) ⊢⁺ (0,0,0,4m+5,4m+8+f)
theorem main_even (m f : ℕ) :
    ⟨0, 0, 0, 2 * m + 2, 2 * m + 4 + f⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m + 5, 4 * m + 8 + f⟩ := by
  rw [show 2 * m + 4 + f = f + (2 * m + 1) + 3 from by ring,
      show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus
    (setup_phase (2 * m + 1) (f := f + (2 * m + 1)))
  rw [show (2 * m + 1) + 1 = 0 + 2 * m + 2 from by ring,
      show f + (2 * m + 1) + 1 = (f + m + 1) + m + 1 from by ring]
  apply stepStar_trans (interleaved m 0 0 1 (f + m + 1))
  rw [show 0 + m + 1 = 0 + m + 1 from by ring,
      show 1 + 3 * m + 3 = 3 * m + 4 from by ring]
  apply stepStar_trans (r2_chain m 2 0 (3 * m + 4) f)
  rw [show 2 + 2 * m + 2 = 0 + (2 * m + 4) from by ring,
      show 3 * m + 4 + m + 1 = 4 * m + 5 from by ring]
  apply stepStar_trans (r3_chain (2 * m + 4) 0 f (d := 4 * m + 5))
  ring_nf; finish

-- Odd d = 1: (0,0,0,1,f+3) ⊢⁺ (0,0,0,3,f+6)
theorem main_odd_0 (f : ℕ) :
    ⟨0, 0, 0, 1, f + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 3, f + 6⟩ := by
  apply stepPlus_stepStar_stepPlus (setup_phase 0 (f := f))
  rw [show (0 : ℕ) + 1 = 0 + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  rw [show f + 1 = f + 0 + 1 from by ring]
  step fm
  exact r3_chain 3 0 f (d := 3)

-- Odd d >= 3: (0,0,0,2m+3,2m+5+f) ⊢⁺ (0,0,0,4m+7,4m+10+f)
theorem main_odd_succ (m f : ℕ) :
    ⟨0, 0, 0, 2 * m + 3, 2 * m + 5 + f⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m + 7, 4 * m + 10 + f⟩ := by
  rw [show 2 * m + 5 + f = f + (2 * m + 2) + 3 from by ring,
      show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus
    (setup_phase (2 * m + 2) (f := f + (2 * m + 2)))
  rw [show (2 * m + 2) + 1 = 1 + 2 * m + 2 from by ring,
      show f + (2 * m + 2) + 1 = (f + m + 2) + m + 1 from by ring]
  apply stepStar_trans (interleaved m 1 0 1 (f + m + 2))
  rw [show 0 + m + 1 = m + 1 from by ring,
      show 1 + 3 * m + 3 = 3 * m + 4 from by ring,
      show (2 : ℕ) = 1 + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show m + 1 + 1 = 0 + (m + 1) + 1 from by ring,
      show 3 * m + 4 + 1 = 3 * m + 5 from by ring,
      show f + m + 2 = f + (m + 1) + 1 from by ring]
  apply stepStar_trans (r2_chain (m + 1) 1 0 (3 * m + 5) f)
  rw [show 1 + 2 * (m + 1) + 2 = 0 + (2 * m + 5) from by ring,
      show 3 * m + 5 + (m + 1) + 1 = 4 * m + 7 from by ring]
  apply stepStar_trans (r3_chain (2 * m + 5) 0 f (d := 4 * m + 7))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d f, q = ⟨0, 0, 0, d, d + 2 + f⟩)
  · intro c ⟨d, f, hq⟩; subst hq
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- d even: d = m + m
      subst hm
      rcases m with _ | m
      · -- d = 0
        refine ⟨⟨0, 0, 0, 1, f + 4⟩, ⟨1, f + 1, by ring_nf⟩, ?_⟩
        have := trans_d0 f
        rwa [show 0 = 0 + 0 from by omega,
             show f + 2 = 0 + 0 + 2 + f from by omega] at this
      · -- d = 2(m+1) = 2m+2
        refine ⟨⟨0, 0, 0, 4 * m + 5, 4 * m + 8 + f⟩,
          ⟨4 * m + 5, f + 1, by ring_nf⟩, ?_⟩
        have := main_even m f
        rwa [show 2 * m + 2 = (m + 1) + (m + 1) from by omega,
             show 2 * m + 4 + f = (m + 1) + (m + 1) + 2 + f from by omega] at this
    · -- d odd: d = 2 * m + 1
      subst hm
      rcases m with _ | m
      · -- d = 1
        refine ⟨⟨0, 0, 0, 3, f + 6⟩, ⟨3, f + 1, by ring_nf⟩, ?_⟩
        have := main_odd_0 f
        rwa [show 1 = 2 * 0 + 1 from by omega,
             show f + 3 = 2 * 0 + 1 + 2 + f from by omega] at this
      · -- d = 2(m+1) + 1 = 2m + 3
        refine ⟨⟨0, 0, 0, 4 * m + 7, 4 * m + 10 + f⟩,
          ⟨4 * m + 7, f + 1, by ring_nf⟩, ?_⟩
        have := main_odd_succ m f
        rwa [show 2 * m + 3 = 2 * (m + 1) + 1 from by omega,
             show 2 * m + 5 + f = 2 * (m + 1) + 1 + 2 + f from by omega] at this
  · exact ⟨0, 0, by ring_nf⟩
