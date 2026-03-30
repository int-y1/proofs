import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #752: [35/6, 4/55, 847/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_752

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 2))
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem interleaved_r1r1r2 : ∀ j, ∀ c d e,
    ⟨2, 2 * j + 1, c, d, e + j⟩ [fm]⊢* ⟨1, 0, c + j + 1, d + 2 * j + 1, e⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · step fm; finish
  · rw [show 2 * (j + 1) + 1 = (2 * j + 2) + 1 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    step fm
    rw [show 2 * j + 2 = (2 * j + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem r3r2r2_chain : ∀ k, ∀ a d,
    ⟨a + 1, 0, 2 * k, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 3) (d + 1))
    ring_nf; finish

theorem r3r2r2_odd : ∀ k, ∀ a d,
    ⟨a + 1, 0, 2 * k + 1, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 2, 0, 0, d + k + 1, 1⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 3) (d + 1))
    ring_nf; finish

theorem opening_steps (m e : ℕ) :
    ⟨0, 2 * m + 4, 0, 0, e + m + 3⟩ [fm]⊢⁺ ⟨2, 2 * m + 3, 0, 2, e + m + 1⟩ := by
  rw [show e + m + 3 = (e + m + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * m + 4, 0, 0, (e + m + 2) + 1⟩ = some ⟨0 + 1, 2 * m + 4, 0, 0 + 1, e + m + 2⟩
    simp [fm]
  rw [show 2 * m + 4 = (2 * m + 3) + 1 from by ring]
  step fm
  rw [show e + m + 2 = (e + m + 1) + 1 from by ring]
  step fm
  ring_nf; finish

theorem phase1 (m e : ℕ) :
    ⟨0, 2 * m + 4, 0, 0, e + m + 3⟩ [fm]⊢⁺ ⟨1, 0, m + 2, 2 * m + 5, e⟩ := by
  apply stepPlus_stepStar_stepPlus (opening_steps m e)
  rw [show 2 * m + 3 = 2 * (m + 1) + 1 from by ring,
      show e + m + 1 = e + (m + 1) from by ring]
  apply stepStar_trans (interleaved_r1r1r2 (m + 1) 0 2 e)
  ring_nf; finish

theorem phase2_small_even (m e K : ℕ) (hm2 : m + 2 = 2 * K + e) :
    ⟨1, 0, m + 2, 2 * m + 5, e⟩ [fm]⊢* ⟨0, 0, 0, 4 * m + 10, 3 * m + e + 8⟩ := by
  rw [hm2]
  have h1 := r2_chain e 1 (2 * K) (2 * m + 5) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 1 + 2 * e = 2 * e + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain K (2 * e) (2 * m + 5))
  rw [show 2 * e + 3 * K + 1 = 0 + (2 * e + 3 * K + 1) from by ring]
  apply stepStar_trans (r3_drain (2 * e + 3 * K + 1) 0 (2 * m + 5 + K) 0)
  rw [show 2 * m + 5 + K + (2 * e + 3 * K + 1) = 4 * m + 10 from by omega,
      show 0 + 2 * (2 * e + 3 * K + 1) = 3 * m + e + 8 from by omega]
  finish

theorem phase2_small_odd (m e K : ℕ) (hm2 : m + 2 = 2 * K + 1 + e) :
    ⟨1, 0, m + 2, 2 * m + 5, e⟩ [fm]⊢* ⟨0, 0, 0, 4 * m + 10, 3 * m + e + 8⟩ := by
  rw [hm2]
  have h1 := r2_chain e 1 (2 * K + 1) (2 * m + 5) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 1 + 2 * e = 2 * e + 1 from by ring]
  apply stepStar_trans (r3r2r2_odd K (2 * e) (2 * m + 5))
  rw [show 2 * e + 3 * K + 2 = 0 + (2 * e + 3 * K + 2) from by ring]
  apply stepStar_trans (r3_drain (2 * e + 3 * K + 2) 0 (2 * m + 5 + K + 1) 1)
  rw [show 2 * m + 5 + K + 1 + (2 * e + 3 * K + 2) = 4 * m + 10 from by omega,
      show 1 + 2 * (2 * e + 3 * K + 2) = 3 * m + e + 8 from by omega]
  finish

theorem phase2_large (m e : ℕ) (h : m + 2 < e) :
    ⟨1, 0, m + 2, 2 * m + 5, e⟩ [fm]⊢* ⟨0, 0, 0, 4 * m + 10, 3 * m + e + 8⟩ := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 + (m + 2) := ⟨e - m - 3, by omega⟩
  have h1 := r2_chain (m + 2) 1 0 (2 * m + 5) (f + 1)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 1 + 2 * (m + 2) = 0 + (2 * m + 5) from by ring]
  apply stepStar_trans (r3_drain (2 * m + 5) 0 (2 * m + 5) (f + 1))
  rw [show 2 * m + 5 + (2 * m + 5) = 4 * m + 10 from by omega,
      show f + 1 + 2 * (2 * m + 5) = 3 * m + (f + 1 + (m + 2)) + 8 from by omega]
  finish

theorem main_transition (m e : ℕ) :
    ⟨0, 0, 0, 2 * m + 4, e + m + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m + 10, 3 * m + e + 8⟩ := by
  rw [show 2 * m + 4 = 0 + (2 * m + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * m + 4) 0 0 (e + m + 3))
  rw [show 0 + (2 * m + 4) = 2 * m + 4 from by ring]
  rcases (show e ≤ m + 2 ∨ m + 2 < e from by omega) with h | h
  · apply stepPlus_stepStar_stepPlus (phase1 m e)
    rcases Nat.even_or_odd (m + 2 - e) with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK
      exact phase2_small_even m e K (by omega)
    · exact phase2_small_odd m e K (by omega)
  · exact stepPlus_stepStar_stepPlus (phase1 m e) (phase2_large m e h)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 4⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, e⟩ ↦ ⟨0, 0, 0, 2 * m + 4, e + m + 3⟩) ⟨0, 1⟩
  intro ⟨m, e⟩
  refine ⟨⟨2 * m + 3, m + e + 2⟩, ?_⟩
  have := main_transition m e
  convert this using 2
  ring_nf

end Sz22_2003_unofficial_752
