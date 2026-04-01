import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1243: [5/6, 77/2, 4/35, 9/7, 98/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  1
 2  0 -1 -1  0
 0  2  0 -1  0
 1  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1243

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

private lemma fm_r5 (b c e : ℕ) :
    fm ⟨0, b, c, 0, e + 1⟩ = some ⟨1, b, c, 2, e⟩ := by
  cases c <;> rfl

theorem r4_drain : ∀ k, ∀ b d e,
    ⟨(0:ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

theorem full_round (b c e : ℕ) :
    ⟨(0:ℕ), b + 5, c, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 3, 0, e⟩ := by
  apply stepStar_trans (step_stepStar (fm_r5 (b + 5) c e))
  rw [show b + 5 = (b + 4) + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨1, (b+4)+1, c, 2, e⟩ : Q) [fm]⊢ ⟨0, b+4, c+1, 2, e⟩))
  rw [show c + 1 = (c) + 1 from rfl, show (2:ℕ) = (1:ℕ) + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨0, b+4, c+1, 1+1, e⟩ : Q) [fm]⊢ ⟨2, b+4, c, 1, e⟩))
  rw [show b + 4 = (b + 3) + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨2, (b+3)+1, c, 1, e⟩ : Q) [fm]⊢ ⟨1, b+3, c+1, 1, e⟩))
  rw [show b + 3 = (b + 2) + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨1, (b+2)+1, c+1, 1, e⟩ : Q) [fm]⊢ ⟨0, b+2, c+2, 1, e⟩))
  rw [show c + 2 = (c + 1) + 1 from by ring, show (1:ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨0, b+2, (c+1)+1, 0+1, e⟩ : Q) [fm]⊢ ⟨2, b+2, c+1, 0, e⟩))
  rw [show b + 2 = (b + 1) + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨2, (b+1)+1, c+1, 0, e⟩ : Q) [fm]⊢ ⟨1, b+1, c+2, 0, e⟩))
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨1, b+1, c+2, 0, e⟩ : Q) [fm]⊢ ⟨0, b, c+3, 0, e⟩))
  finish

theorem full_round_chain : ∀ k, ∀ b c e,
    ⟨(0:ℕ), b + 5 * k, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · simp; exists 0
  · rw [show b + 5 * (k + 1) = (b + 5) + 5 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 5) c (e + 1))
    apply stepStar_trans (full_round b (c + 3 * k) e)
    rw [show c + 3 * k + 3 = c + 3 * (k + 1) from by ring]; finish

theorem r3r2r2 : ∀ k, ∀ c d e,
    ⟨(0:ℕ), 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 1 + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring, show d + 1 = d + 1 from rfl]
    step fm; step fm; step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih c (d + 1) (e + 2))
    ring_nf; finish

theorem partial_0 (C F : ℕ) :
    ⟨(0:ℕ), 0, C, 0, F + 1⟩ [fm]⊢* ⟨0, 0, 0, C + 3, 2 * C + F + 1⟩ := by
  apply stepStar_trans (step_stepStar (fm_r5 0 C F))
  step fm
  rw [show C = 0 + C from by ring, show (3:ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2r2 C 0 2 (F + 1))
  ring_nf; finish

theorem partial_1 (C F : ℕ) :
    ⟨(0:ℕ), 1, C, 0, F + 1⟩ [fm]⊢* ⟨0, 0, 0, C + 3, 2 * C + F + 2⟩ := by
  apply stepStar_trans (step_stepStar (fm_r5 1 C F))
  step fm
  rw [show C + 1 = 0 + (C + 1) from by ring, show (2:ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2 (C + 1) 0 1 F)
  ring_nf; finish

theorem partial_2 (C F : ℕ) :
    ⟨(0:ℕ), 2, C, 0, F + 1⟩ [fm]⊢* ⟨0, 0, 0, C + 3, 2 * C + F + 3⟩ := by
  apply stepStar_trans (step_stepStar (fm_r5 2 C F))
  rw [show (2:ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨1, 1+1, C, 2, F⟩ : Q) [fm]⊢ ⟨0, 1, C+1, 2, F⟩))
  rw [show C + 1 = C + 1 from rfl, show (2:ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨0, 1, (C)+1, 1+1, F⟩ : Q) [fm]⊢ ⟨2, 1, C, 1, F⟩))
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨2, 1, C, 1, F⟩ : Q) [fm]⊢ ⟨1, 0, C+1, 1, F⟩))
  step fm
  rw [show C + 1 = 0 + (C + 1) from by ring, show (2:ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2 (C + 1) 0 1 (F + 1))
  ring_nf; finish

theorem partial_3 (C F : ℕ) :
    ⟨(0:ℕ), 3, C, 0, F + 1⟩ [fm]⊢* ⟨0, 0, 0, C + 3, 2 * C + F + 4⟩ := by
  apply stepStar_trans (step_stepStar (fm_r5 3 C F))
  rw [show (3:ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨1, 2+1, C, 2, F⟩ : Q) [fm]⊢ ⟨0, 2, C+1, 2, F⟩))
  rw [show C + 1 = C + 1 from rfl, show (2:ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨0, 2, (C)+1, 1+1, F⟩ : Q) [fm]⊢ ⟨2, 2, C, 1, F⟩))
  rw [show (2:ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨2, 1+1, C, 1, F⟩ : Q) [fm]⊢ ⟨1, 1, C+1, 1, F⟩))
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨1, 1, C+1, 1, F⟩ : Q) [fm]⊢ ⟨0, 0, C+2, 1, F⟩))
  rw [show C + 2 = (C + 1) + 1 from by ring, show (1:ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨0, 0, (C+1)+1, 0+1, F⟩ : Q) [fm]⊢ ⟨2, 0, C+1, 0, F⟩))
  step fm; step fm
  rw [show C + 1 = 0 + (C + 1) from by ring, show (2:ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2 (C + 1) 0 1 (F + 2))
  ring_nf; finish

theorem partial_4 (C F : ℕ) :
    ⟨(0:ℕ), 4, C, 0, F + 1⟩ [fm]⊢* ⟨0, 0, 0, C + 3, 2 * C + F + 5⟩ := by
  apply stepStar_trans (step_stepStar (fm_r5 4 C F))
  rw [show (4:ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨1, 3+1, C, 2, F⟩ : Q) [fm]⊢ ⟨0, 3, C+1, 2, F⟩))
  rw [show C + 1 = C + 1 from rfl, show (2:ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨0, 3, (C)+1, 1+1, F⟩ : Q) [fm]⊢ ⟨2, 3, C, 1, F⟩))
  rw [show (3:ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨2, 2+1, C, 1, F⟩ : Q) [fm]⊢ ⟨1, 2, C+1, 1, F⟩))
  rw [show (2:ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨1, 1+1, C+1, 1, F⟩ : Q) [fm]⊢ ⟨0, 1, C+2, 1, F⟩))
  rw [show C + 2 = (C + 1) + 1 from by ring, show (1:ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨0, 1, (C+1)+1, 0+1, F⟩ : Q) [fm]⊢ ⟨2, 1, C+1, 0, F⟩))
  apply stepStar_trans (step_stepStar
    (by rfl : (⟨2, 1, C+1, 0, F⟩ : Q) [fm]⊢ ⟨1, 0, C+2, 0, F⟩))
  step fm
  rw [show C + 2 = 0 + (C + 2) from by ring, show (1:ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2 (C + 2) 0 0 (F + 1))
  ring_nf; finish

-- d ≡ 0 (mod 5): d = 5(m+1), E = f + 2m + 3
theorem trans_mod0 (m f : ℕ) :
    ⟨(0:ℕ), 0, 0, 5 * (m + 1), f + 2 * m + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * m + 9, f + 12 * m + 13⟩ := by
  rw [show 5 * (m + 1) = (5 * m + 4) + 1 from by ring]
  step fm
  rw [show 5 * m + 4 = 0 + (5 * m + 4) from by ring]
  apply stepStar_trans (r4_drain (5 * m + 4) 2 0 (f + 2 * m + 3))
  rw [show 2 + 2 * (5 * m + 4) = 0 + 5 * (2 * m + 2) from by ring,
      show f + 2 * m + 3 = (f + 1) + (2 * m + 2) from by ring]
  apply stepStar_trans (full_round_chain (2 * m + 2) 0 0 (f + 1))
  rw [show 0 + 3 * (2 * m + 2) = 6 * m + 6 from by ring]
  apply stepStar_trans (partial_0 (6 * m + 6) f)
  rw [show 6 * m + 6 + 3 = 6 * m + 9 from by ring,
      show 2 * (6 * m + 6) + f + 1 = f + 12 * m + 13 from by ring]
  finish

-- d ≡ 1 (mod 5): d = 5m+1, E = f + 2m + 1
theorem trans_mod1 (m f : ℕ) :
    ⟨(0:ℕ), 0, 0, 5 * m + 1, f + 2 * m + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * m + 3, f + 12 * m + 3⟩ := by
  rw [show 5 * m + 1 = (5 * m) + 1 from by ring]
  step fm
  rw [show 5 * m = 0 + 5 * m from by ring]
  apply stepStar_trans (r4_drain (5 * m) 2 0 (f + 2 * m + 1))
  rw [show 2 + 2 * (5 * m) = 2 + 5 * (2 * m) from by ring,
      show f + 2 * m + 1 = (f + 1) + 2 * m from by ring]
  apply stepStar_trans (full_round_chain (2 * m) 2 0 (f + 1))
  rw [show 0 + 3 * (2 * m) = 6 * m from by ring]
  apply stepStar_trans (partial_2 (6 * m) f)
  rw [show 6 * m + 3 = 6 * m + 3 from rfl,
      show 2 * (6 * m) + f + 3 = f + 12 * m + 3 from by ring]
  finish

-- d ≡ 2 (mod 5): d = 5m+2, E = f + 2m + 1
theorem trans_mod2 (m f : ℕ) :
    ⟨(0:ℕ), 0, 0, 5 * m + 2, f + 2 * m + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * m + 3, f + 12 * m + 5⟩ := by
  rw [show 5 * m + 2 = (5 * m + 1) + 1 from by ring]
  step fm
  rw [show 5 * m + 1 = 0 + (5 * m + 1) from by ring]
  apply stepStar_trans (r4_drain (5 * m + 1) 2 0 (f + 2 * m + 1))
  rw [show 2 + 2 * (5 * m + 1) = 4 + 5 * (2 * m) from by ring,
      show f + 2 * m + 1 = (f + 1) + 2 * m from by ring]
  apply stepStar_trans (full_round_chain (2 * m) 4 0 (f + 1))
  rw [show 0 + 3 * (2 * m) = 6 * m from by ring]
  apply stepStar_trans (partial_4 (6 * m) f)
  rw [show 6 * m + 3 = 6 * m + 3 from rfl,
      show 2 * (6 * m) + f + 5 = f + 12 * m + 5 from by ring]
  finish

-- d ≡ 3 (mod 5): d = 5m+3, E = f + 2m + 2
theorem trans_mod3 (m f : ℕ) :
    ⟨(0:ℕ), 0, 0, 5 * m + 3, f + 2 * m + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * m + 6, f + 12 * m + 8⟩ := by
  rw [show 5 * m + 3 = (5 * m + 2) + 1 from by ring]
  step fm
  rw [show 5 * m + 2 = 0 + (5 * m + 2) from by ring]
  apply stepStar_trans (r4_drain (5 * m + 2) 2 0 (f + 2 * m + 2))
  rw [show 2 + 2 * (5 * m + 2) = 1 + 5 * (2 * m + 1) from by ring,
      show f + 2 * m + 2 = (f + 1) + (2 * m + 1) from by ring]
  apply stepStar_trans (full_round_chain (2 * m + 1) 1 0 (f + 1))
  rw [show 0 + 3 * (2 * m + 1) = 6 * m + 3 from by ring]
  apply stepStar_trans (partial_1 (6 * m + 3) f)
  rw [show 6 * m + 3 + 3 = 6 * m + 6 from by ring,
      show 2 * (6 * m + 3) + f + 2 = f + 12 * m + 8 from by ring]
  finish

-- d ≡ 4 (mod 5): d = 5m+4, E = f + 2m + 2
theorem trans_mod4 (m f : ℕ) :
    ⟨(0:ℕ), 0, 0, 5 * m + 4, f + 2 * m + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * m + 6, f + 12 * m + 10⟩ := by
  rw [show 5 * m + 4 = (5 * m + 3) + 1 from by ring]
  step fm
  rw [show 5 * m + 3 = 0 + (5 * m + 3) from by ring]
  apply stepStar_trans (r4_drain (5 * m + 3) 2 0 (f + 2 * m + 2))
  rw [show 2 + 2 * (5 * m + 3) = 3 + 5 * (2 * m + 1) from by ring,
      show f + 2 * m + 2 = (f + 1) + (2 * m + 1) from by ring]
  apply stepStar_trans (full_round_chain (2 * m + 1) 3 0 (f + 1))
  rw [show 0 + 3 * (2 * m + 1) = 6 * m + 3 from by ring]
  apply stepStar_trans (partial_3 (6 * m + 3) f)
  rw [show 6 * m + 3 + 3 = 6 * m + 6 from by ring,
      show 2 * (6 * m + 3) + f + 4 = f + 12 * m + 10 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d E, q = ⟨0, 0, 0, d, E⟩ ∧ d ≥ 1 ∧ E ≥ d)
  · intro c ⟨d, E, hq, hd, hE⟩; subst hq
    have h5 : d % 5 < 5 := Nat.mod_lt _ (by omega)
    obtain ⟨m, hm⟩ : ∃ m, d = 5 * m + d % 5 := ⟨d / 5, by omega⟩
    interval_cases (d % 5)
    · -- d ≡ 0 (mod 5): d = 5m, m ≥ 1
      subst hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨f, rfl⟩ : ∃ f, E = f + 2 * m' + 3 := ⟨E - 2 * m' - 3, by omega⟩
      refine ⟨⟨0, 0, 0, 6 * m' + 9, f + 12 * m' + 13⟩,
        ⟨6 * m' + 9, f + 12 * m' + 13, rfl, by omega, by omega⟩,
        trans_mod0 m' f⟩
    · -- d ≡ 1 (mod 5): d = 5m+1
      subst hm
      obtain ⟨f, rfl⟩ : ∃ f, E = f + 2 * m + 1 := ⟨E - 2 * m - 1, by omega⟩
      refine ⟨⟨0, 0, 0, 6 * m + 3, f + 12 * m + 3⟩,
        ⟨6 * m + 3, f + 12 * m + 3, rfl, by omega, by omega⟩,
        trans_mod1 m f⟩
    · -- d ≡ 2 (mod 5): d = 5m+2
      subst hm
      obtain ⟨f, rfl⟩ : ∃ f, E = f + 2 * m + 1 := ⟨E - 2 * m - 1, by omega⟩
      refine ⟨⟨0, 0, 0, 6 * m + 3, f + 12 * m + 5⟩,
        ⟨6 * m + 3, f + 12 * m + 5, rfl, by omega, by omega⟩,
        trans_mod2 m f⟩
    · -- d ≡ 3 (mod 5): d = 5m+3
      subst hm
      obtain ⟨f, rfl⟩ : ∃ f, E = f + 2 * m + 2 := ⟨E - 2 * m - 2, by omega⟩
      refine ⟨⟨0, 0, 0, 6 * m + 6, f + 12 * m + 8⟩,
        ⟨6 * m + 6, f + 12 * m + 8, rfl, by omega, by omega⟩,
        trans_mod3 m f⟩
    · -- d ≡ 4 (mod 5): d = 5m+4
      subst hm
      obtain ⟨f, rfl⟩ : ∃ f, E = f + 2 * m + 2 := ⟨E - 2 * m - 2, by omega⟩
      refine ⟨⟨0, 0, 0, 6 * m + 6, f + 12 * m + 10⟩,
        ⟨6 * m + 6, f + 12 * m + 10, rfl, by omega, by omega⟩,
        trans_mod4 m f⟩
  · exact ⟨1, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1243
