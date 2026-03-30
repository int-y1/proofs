import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #755: [35/6, 4/55, 847/2, 3/7, 25/3]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 0 -1  2  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_755

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 2))
    ring_nf; finish

theorem r1r1r2_even : ∀ K, ∀ c d e, ⟨2, 2 * K, c, d, e + K⟩ [fm]⊢* ⟨2, 0, c + K, d + 2 * K, e⟩ := by
  intro K; induction' K with K ih <;> intro c d e
  · exists 0
  · rw [show 2 * (K + 1) = (2 * K + 1) + 1 from by ring,
        show e + (K + 1) = (e + K) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem r1r1r2_odd : ∀ K, ∀ c d e, ⟨2, 2 * K + 1, c, d, e + K⟩ [fm]⊢* ⟨1, 0, c + K + 1, d + 2 * K + 1, e⟩ := by
  intro K; induction' K with K ih <;> intro c d e
  · step fm; finish
  · rw [show 2 * (K + 1) + 1 = (2 * K + 2) + 1 from by ring,
        show e + (K + 1) = (e + K) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem main_odd (m f : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, f + 2 * m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m + 4, f + 4 * m + 8⟩ := by
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 0 + (2 * m + 1), f + 2 * m + 2⟩ = some ⟨0, 1, 0, 0 + 2 * m, f + 2 * m + 2⟩
    simp [fm]
  apply stepStar_trans (r4_chain (2 * m) 1 0 (f + 2 * m + 2))
  rw [show 1 + 2 * m = (2 * m) + 1 from by ring]
  step fm
  rw [show f + 2 * m + 2 = (f + 2 * m + 1) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show f + 2 * m + 1 = (f + m + 1) + m from by ring]
  apply stepStar_trans (r1r1r2_even m 1 0 (f + m + 1))
  rw [show 1 + m = m + 1 from by ring,
      show 0 + 2 * m = 2 * m from by ring,
      show f + m + 1 = f + (m + 1) from by ring,
      show m + 1 = m + 1 from rfl]
  apply stepStar_trans (r2_chain (m + 1) 2 (2 * m) f)
  rw [show 2 + 2 * (m + 1) = 0 + (2 * m + 4) from by ring]
  apply stepStar_trans (r3_chain (2 * m + 4) 0 (2 * m) f)
  ring_nf; finish

theorem main_even (m' f : ℕ) :
    ⟨0, 0, 0, 2 * m' + 2, f + 2 * m' + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m' + 6, f + 4 * m' + 10⟩ := by
  rw [show 2 * m' + 2 = 0 + (2 * m' + 2) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 0 + (2 * m' + 2), f + 2 * m' + 3⟩ =
         some ⟨0, 1, 0, 0 + (2 * m' + 1), f + 2 * m' + 3⟩
    simp [fm]
  apply stepStar_trans (r4_chain (2 * m' + 1) 1 0 (f + 2 * m' + 3))
  rw [show 1 + (2 * m' + 1) = (2 * m') + 1 + 1 from by ring]
  step fm
  rw [show f + 2 * m' + 3 = (f + 2 * m' + 2) + 1 from by ring,
      show 2 * m' + 1 = 2 * m' + 1 from rfl]
  step fm
  rw [show f + 2 * m' + 2 = (f + m' + 2) + m' from by ring]
  apply stepStar_trans (r1r1r2_odd m' 1 0 (f + m' + 2))
  rw [show 1 + m' + 1 = m' + 2 from by ring,
      show 0 + 2 * m' + 1 = 2 * m' + 1 from by ring,
      show f + m' + 2 = f + (m' + 2) from by ring,
      show m' + 2 = m' + 2 from rfl]
  apply stepStar_trans (r2_chain (m' + 2) 1 (2 * m' + 1) f)
  rw [show 1 + 2 * (m' + 2) = 0 + (2 * m' + 5) from by ring]
  apply stepStar_trans (r3_chain (2 * m' + 5) 0 (2 * m' + 1) f)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 1 ∧ e ≥ d + 1)
  · intro c ⟨d, e, hq, hd, he⟩; subst hq
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      have hm1 : m ≥ 1 := by omega
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      refine ⟨⟨0, 0, 0, 4 * m' + 6, e + 2 * m' + 7⟩,
        ⟨4 * m' + 6, e + 2 * m' + 7, rfl, by omega, by omega⟩, ?_⟩
      rw [show e = (e - 2 * m' - 3) + 2 * m' + 3 from by omega]
      have key := main_even m' (e - 2 * m' - 3)
      convert key using 2; ring_nf
    · subst hm
      refine ⟨⟨0, 0, 0, 4 * m + 4, e + 2 * m + 6⟩,
        ⟨4 * m + 4, e + 2 * m + 6, rfl, by omega, by omega⟩, ?_⟩
      rw [show e = (e - 2 * m - 2) + 2 * m + 2 from by omega]
      have key := main_odd m (e - 2 * m - 2)
      convert key using 2; ring_nf
  · exact ⟨1, 2, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_755
