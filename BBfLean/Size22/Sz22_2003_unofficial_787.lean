import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #787: [35/6, 56/55, 77/2, 3/7, 5/3]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  1 -1
-1  0  0  1  1
 0  1  0 -1  0
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_787

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1) (e + 1))
    ring_nf; finish

theorem d_to_b : ∀ k b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

theorem drain : ∀ c a d e, ⟨a, 0, c, d, e + 1⟩ [fm]⊢* ⟨0, 0, 0, d + a + 4 * c, e + 1 + a + 2 * c⟩ := by
  intro c; induction' c with c ih <;> intro a d e
  · exact r3_chain a d (e + 1)
  · step fm
    rcases e with _ | e'
    · step fm
      apply stepStar_trans (ih (a + 2) (d + 2) 0)
      ring_nf; finish
    · apply stepStar_trans (ih (a + 3) (d + 1) e')
      ring_nf; finish

theorem grind : ∀ b, ∀ c d e, 3 * (e + 1) ≥ b + 1 →
    ⟨0, b, c + 1, d, e + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 4 * b + 4 * c + 4, e + b + 2 * c + 3⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih
  intro c d e hcond
  rcases b with _ | _ | _ | b
  · -- b = 0
    show ⟨0, 0, c + 1, d, e + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 4 * 0 + 4 * c + 4, e + 0 + 2 * c + 3⟩
    rw [show d + 4 * 0 + 4 * c + 4 = d + 0 + 4 * (c + 1) from by ring,
        show e + 0 + 2 * c + 3 = e + 1 + 0 + 2 * (c + 1) from by ring]
    exact drain (c + 1) 0 d e
  · -- b = 1
    show ⟨0, 0 + 1, c + 1, d, e + 1⟩ [fm]⊢*
      ⟨0, 0, 0, d + 4 * (0 + 1) + 4 * c + 4, e + (0 + 1) + 2 * c + 3⟩
    step fm; step fm
    rcases e with _ | e'
    · step fm
      apply stepStar_trans (drain (c + 1) 1 (d + 3) 0)
      ring_nf; finish
    · apply stepStar_trans (drain (c + 1) 2 (d + 2) e')
      ring_nf; finish
  · -- b = 2
    show ⟨0, 0 + 1 + 1, c + 1, d, e + 1⟩ [fm]⊢*
      ⟨0, 0, 0, d + 4 * (0 + 1 + 1) + 4 * c + 4, e + (0 + 1 + 1) + 2 * c + 3⟩
    step fm; step fm; step fm
    rcases e with _ | e'
    · step fm
      apply stepStar_trans (drain (c + 2) 0 (d + 4) 0)
      ring_nf; finish
    · apply stepStar_trans (drain (c + 2) 1 (d + 3) e')
      ring_nf; finish
  · -- b + 3
    show ⟨0, b + 1 + 1 + 1, c + 1, d, e + 1⟩ [fm]⊢*
      ⟨0, 0, 0, d + 4 * (b + 1 + 1 + 1) + 4 * c + 4, e + (b + 1 + 1 + 1) + 2 * c + 3⟩
    have he : e ≥ 1 := by omega
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih b (by omega) (c + 2) (d + 4) e' (by omega))
    ring_nf; finish

theorem full_cycle : ∀ d e, 3 * (e + 1) ≥ d + 3 →
    ⟨3, d, 0, 1, e⟩ [fm]⊢* ⟨0, 0, 0, 4 * d + 4, d + e + 3⟩ := by
  intro d e hcond
  rcases d with _ | _ | _ | d
  · -- d = 0
    show ⟨3, 0, 0, 1, e⟩ [fm]⊢* ⟨0, 0, 0, 4 * 0 + 4, 0 + e + 3⟩
    rw [show 4 * 0 + 4 = 1 + 3 from by ring, show 0 + e + 3 = e + 3 from by ring]
    exact r3_chain 3 1 e
  · -- d = 1
    show ⟨3, 0 + 1, 0, 1, e⟩ [fm]⊢* ⟨0, 0, 0, 4 * (0 + 1) + 4, 0 + 1 + e + 3⟩
    step fm
    rcases e with _ | e'
    · step fm
      apply stepStar_trans (drain 1 1 3 0)
      ring_nf; finish
    · apply stepStar_trans (drain 1 2 2 e')
      ring_nf; finish
  · -- d = 2
    show ⟨3, 0 + 1 + 1, 0, 1, e⟩ [fm]⊢* ⟨0, 0, 0, 4 * (0 + 1 + 1) + 4, 0 + 1 + 1 + e + 3⟩
    step fm; step fm
    rcases e with _ | e'
    · step fm
      apply stepStar_trans (drain 2 0 4 0)
      ring_nf; finish
    · apply stepStar_trans (drain 2 1 3 e')
      ring_nf; finish
  · -- d + 3
    show ⟨3, d + 1 + 1 + 1, 0, 1, e⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * (d + 1 + 1 + 1) + 4, d + 1 + 1 + 1 + e + 3⟩
    have he : e ≥ 1 := by omega
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    step fm; step fm; step fm
    apply stepStar_trans (grind d 2 4 e' (by omega))
    ring_nf; finish

theorem main_trans (hcond : 3 * (e + 1) ≥ d + 3) :
    ⟨0, 0, 0, d + 1, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * d + 4, d + e + 3⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_b (d + 1) 0 (e + 1))
  rw [show (0 : ℕ) + (d + 1) = d + 1 from by omega]
  apply step_stepStar_stepPlus
  · show fm ⟨0, d + 1, 0, 0, e + 1⟩ = some ⟨0, d, 1, 0, e + 1⟩
    simp [fm]
  step fm
  exact full_cycle d e hcond

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 3⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e + 1⟩ ∧ 3 * (e + 1) ≥ d + 3)
  · intro c ⟨d, e, hq, hcond⟩; subst hq
    refine ⟨⟨0, 0, 0, 4 * d + 4, d + e + 3⟩,
      ⟨4 * d + 3, d + e + 2, ?_, ?_⟩, main_trans hcond⟩
    · rw [show 4 * d + 4 = 4 * d + 3 + 1 from by omega,
          show d + e + 3 = d + e + 2 + 1 from by omega]
    · show 3 * (d + e + 2 + 1) ≥ 4 * d + 3 + 3
      have : 3 * e ≥ d := by omega
      have : 3 * (d + e + 2 + 1) = 3 * e + 3 * d + 9 := by ring
      have : 4 * d + 3 + 3 = d + 3 * d + 6 := by ring
      omega
  · exact ⟨3, 2, rfl, by omega⟩
