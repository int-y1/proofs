import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #673: [35/6, 28/55, 847/2, 3/7, 2/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  1 -1
-1  0  0  1  2
 0  1  0 -1  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_673

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

theorem r3_drain : ∀ a, ∀ d e, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + a, e + 2 * a⟩ := by
  intro a; induction' a with a ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1) (e + 2))
    ring_nf; finish

theorem triple_chain : ∀ k, ∀ c d e, ⟨2, 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, 0, c + k, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = e + 1 + k from by ring]
    step fm; step fm
    rw [show e + 1 + k = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) (d + 3) e)
    ring_nf; finish

theorem odd_triple_chain : ∀ k, ∀ c d e, ⟨1, 2 * k, c, d, e + k⟩ [fm]⊢* ⟨1, 0, c + k, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show (e + k) + 1 = (e + k + 1 - 1) + 1 from by omega]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) (d + 3) e)
    ring_nf; finish

theorem combined : ∀ c, ∀ a d e,
    ⟨a + 1, 0, c, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + a + 1 + 3 * c, 2 * a + e + 2 + 3 * c⟩ := by
  intro c; induction' c with c ih <;> intro a d e
  · apply stepStar_trans (r3_drain (a + 1) d e)
    ring_nf; finish
  · rcases e with _ | e
    · step fm; step fm
      apply stepStar_trans (ih (a + 1) (d + 2) 1)
      ring_nf; finish
    · rw [show (e + 1 : ℕ) = (e : ℕ) + 1 from by ring]
      step fm
      apply stepStar_trans (ih (a + 2) (d + 1) e)
      ring_nf; finish

theorem opening : ⟨0, b + 1, 0, 0, e + 2⟩ [fm]⊢⁺ ⟨2, b, 0, 2, e⟩ := by
  step fm; step fm; step fm; finish

theorem phase_even' (n e' : ℕ) :
    ⟨2, 2 * n, 0, 2, e' + n⟩ [fm]⊢* ⟨0, 0, 0, 6 * n + 4, 2 * n + e' + n + 4⟩ := by
  apply stepStar_trans (triple_chain n 0 2 e')
  show ⟨2, 0, 0 + n, 2 + 3 * n, e'⟩ [fm]⊢* _
  rw [show (0 : ℕ) + n = n from by ring]
  apply stepStar_trans (combined n 1 (2 + 3 * n) e')
  ring_nf; finish

theorem phase_even (n : ℕ) (h : e ≥ n) :
    ⟨2, 2 * n, 0, 2, e⟩ [fm]⊢* ⟨0, 0, 0, 6 * n + 4, 2 * n + e + 4⟩ := by
  have he : e = (e - n) + n := by omega
  rw [he]
  have := phase_even' n (e - n)
  rw [show 2 * n + (e - n) + n + 4 = 2 * n + ((e - n) + n) + 4 from by ring] at this
  exact this

theorem phase_odd' (n e' : ℕ) :
    ⟨2, 2 * n + 1, 0, 2, e' + n⟩ [fm]⊢* ⟨0, 0, 0, 6 * n + 7, 2 * n + e' + n + 5⟩ := by
  rw [show 2 * n + 1 = (2 * n) + 1 from by ring]
  step fm
  show ⟨1, 2 * n, 1, 3, e' + n⟩ [fm]⊢* _
  apply stepStar_trans (odd_triple_chain n 1 3 e')
  show ⟨1, 0, 1 + n, 3 + 3 * n, e'⟩ [fm]⊢* _
  apply stepStar_trans (combined (1 + n) 0 (3 + 3 * n) e')
  ring_nf; finish

theorem phase_odd (n : ℕ) (h : e ≥ n) :
    ⟨2, 2 * n + 1, 0, 2, e⟩ [fm]⊢* ⟨0, 0, 0, 6 * n + 7, 2 * n + e + 5⟩ := by
  have he : e = (e - n) + n := by omega
  rw [he]
  have := phase_odd' n (e - n)
  rw [show 2 * n + (e - n) + n + 5 = 2 * n + ((e - n) + n) + 5 from by ring] at this
  exact this

theorem main_even (n : ℕ) (h : e ≥ n) :
    ⟨0, 0, 0, 2 * n + 1, e + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * n + 4, 2 * n + e + 4⟩ := by
  rw [show 2 * n + 1 = 0 + (2 * n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * n + 1) 0 0)
  rw [show 0 + (2 * n + 1) = (2 * n) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (b := 2 * n) (e := e))
  exact phase_even n h

theorem main_odd (n : ℕ) (h : e ≥ n) :
    ⟨0, 0, 0, 2 * n + 2, e + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * n + 7, 2 * n + e + 5⟩ := by
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * n + 2) 0 0)
  rw [show 0 + (2 * n + 2) = (2 * n + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (b := 2 * n + 1) (e := e))
  exact phase_odd n h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e + 2⟩ ∧ 2 * e + 2 ≥ d + 1)
  · intro q ⟨d, e, hq, hinv⟩; subst hq
    rcases Nat.even_or_odd d with ⟨n, hn⟩ | ⟨n, hn⟩
    · rw [show n + n = 2 * n from by ring] at hn; subst hn
      refine ⟨⟨0, 0, 0, 6 * n + 4, 2 * n + e + 4⟩,
        ⟨6 * n + 3, 2 * n + e + 2, by ring_nf, by omega⟩,
        main_even n (by omega)⟩
    · subst hn
      refine ⟨⟨0, 0, 0, 6 * n + 7, 2 * n + e + 5⟩,
        ⟨6 * n + 6, 2 * n + e + 3, by ring_nf, by omega⟩,
        main_odd n (by omega)⟩
  · exact ⟨0, 0, rfl, by omega⟩
