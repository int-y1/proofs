import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #43: [1/15, 49/3, 6/77, 5/49, 3993/2]

Vector representation:
```
 0 -1 -1  0  0
 0 -1  0  2  0
 1  1  0 -1 -1
 0  0  1 -2  0
-1  1  0  0  3
```

This Fractran program doesn't halt.

Author: Claude (claude-opus-4-6)
-/

namespace Sz22_2003_unofficial_43

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+3⟩
  | _ => none

theorem r3r2_chain : ∀ E, ∀ A D, ⟨A, 0, 0, D+1, E+1⟩ [fm]⊢* ⟨A+E+1, 0, 0, D+E+2, 0⟩ := by
  intro E; induction' E with E ih <;> intro A D
  · step fm; step fm; ring_nf; finish
  · step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

theorem r4_even : ∀ K, ∀ A C, ⟨A, 0, C, 2*K, 0⟩ [fm]⊢* ⟨A, 0, C+K, 0, 0⟩ := by
  intro K; induction' K with K ih <;> intro A C
  · exists 0
  · rw [show 2 * (K + 1) = 2 * K + 2 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

theorem r4_odd : ∀ K, ∀ A C, ⟨A, 0, C, 2*K+1, 0⟩ [fm]⊢* ⟨A, 0, C+K, 1, 0⟩ := by
  intro K; induction' K with K ih <;> intro A C
  · exists 0
  · rw [show 2 * (K + 1) + 1 = (2 * K + 1) + 2 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

theorem r5r1_drain : ∀ K, ∀ A E, ⟨A+K, 0, K, 0, E⟩ [fm]⊢* ⟨A, 0, 0, 0, E+3*K⟩ := by
  intro K; induction' K with K ih <;> intro A E
  · exists 0
  · rw [show A + (K + 1) = (A + K) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

theorem to_peak (a e : ℕ) :
    ⟨a+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a+e+3, 0, 0, e+5, 0⟩ := by
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl, show e + 3 = (e + 2) + 1 from by ring]
  have h := r3r2_chain (e + 2) a 1
  rw [show a + (e + 2) + 1 = a + e + 3 from by ring,
      show 1 + (e + 2) + 2 = e + 5 from by ring] at h
  exact h

theorem from_peak_odd (a m : ℕ) :
    ⟨a+2*m+3, 0, 0, 2*m+5, 0⟩ [fm]⊢* ⟨a+m+3, 0, 0, 0, 3*m+2⟩ := by
  rw [show 2 * m + 5 = 2 * (m + 2) + 1 from by ring]
  apply stepStar_trans (r4_odd (m+2) (a+2*m+3) 0)
  rw [show 0 + (m + 2) = m + 2 from by ring]
  step fm; step fm; step fm; step fm
  rw [show a + 2 * m + 3 = (a + m + 3) + m from by ring]
  apply stepStar_trans (r5r1_drain m (a+m+3) 2)
  rw [show 2 + 3 * m = 3 * m + 2 from by ring]
  finish

theorem from_peak_even (a m : ℕ) :
    ⟨a+2*m+4, 0, 0, 2*(m+3), 0⟩ [fm]⊢* ⟨a+m+1, 0, 0, 0, 3*m+9⟩ := by
  apply stepStar_trans (r4_even (m+3) (a+2*m+4) 0)
  rw [show 0 + (m + 3) = m + 3 from by ring,
      show a + 2 * m + 4 = (a + m + 1) + (m + 3) from by ring]
  apply stepStar_trans (r5r1_drain (m+3) (a+m+1) 0)
  rw [show 0 + 3 * (m + 3) = 3 * m + 9 from by ring]
  finish

theorem main_even (a m : ℕ) :
    ⟨a+1, 0, 0, 0, 2*m⟩ [fm]⊢⁺ ⟨a+m+3, 0, 0, 0, 3*m+2⟩ :=
  stepPlus_stepStar_stepPlus (to_peak a (2*m)) (from_peak_odd a m)

theorem main_odd (a m : ℕ) :
    ⟨a+1, 0, 0, 0, 2*m+1⟩ [fm]⊢⁺ ⟨a+m+1, 0, 0, 0, 3*m+9⟩ := by
  have h1 := to_peak a (2*m+1)
  rw [show a + (2 * m + 1) + 3 = a + 2 * m + 4 from by ring,
      show 2 * m + 1 + 5 = 2 * (m + 3) from by ring] at h1
  exact stepPlus_stepStar_stepPlus h1 (from_peak_even a m)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a+1, 0, 0, 0, e⟩)
  · intro c ⟨a, e, hq⟩; subst hq
    rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm; rw [show m + m = 2 * m from by ring]
      exact ⟨⟨a+m+3, 0, 0, 0, 3*m+2⟩, ⟨a+m+2, 3*m+2, by ring_nf⟩, main_even a m⟩
    · subst hm
      exact ⟨⟨a+m+1, 0, 0, 0, 3*m+9⟩, ⟨a+m, 3*m+9, by ring_nf⟩, main_odd a m⟩
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_43
