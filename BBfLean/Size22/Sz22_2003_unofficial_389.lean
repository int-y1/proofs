import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #389: [2/15, 99/14, 25/2, 7/11, 99/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 0  2 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_389

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + k, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c _ e)
    ring_nf; finish

theorem a_to_c : ∀ k c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + 2 * k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e
    step fm
    apply stepStar_trans (ih _ e)
    ring_nf; finish

theorem a_d_to_b_e : ∀ k a b d e, ⟨a + k, b, 0, d + k, e⟩ [fm]⊢* ⟨a, b + 2 * k, (0 : ℕ), d, e + k⟩ := by
  intro k; induction k with
  | zero => intro a b d e; exists 0
  | succ k ih =>
    intro a b d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a _ d _)
    ring_nf; finish

theorem triangle_step (a c d e : ℕ) :
    ⟨a, 2, c + 2, d + 1, e⟩ [fm]⊢⁺ ⟨a + 1, 2, c, d, e + 1⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨a, 2, c + 2, d + 1, e⟩ = some ⟨a + 1, 1, c + 1, d + 1, e⟩
    simp [fm]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨a + 1, 1, c + 1, d + 1, e⟩ = some ⟨a + 2, 0, c, d + 1, e⟩
    simp [fm]
  apply step_stepStar
  show fm ⟨a + 2, 0, c, d + 1, e⟩ = some ⟨a + 1, 2, c, d, e + 1⟩
  simp [fm]

theorem triangle_chain : ∀ k a c d e,
    ⟨a, 2, c + 2 * k, d + k, e⟩ [fm]⊢* ⟨a + k, 2, c, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c d e; exists 0
  | succ k ih =>
    intro a c d e
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans
    · exact stepPlus_stepStar (triangle_step a (c + 2 * k) (d + k) e)
    apply stepStar_trans (ih _ c d _)
    ring_nf; finish

theorem drain_pair (a b e : ℕ) :
    ⟨a, b + 2, 2, 0, e⟩ [fm]⊢⁺ ⟨a + 1, b, 2, 0, e⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨a, b + 2, 2, 0, e⟩ = some ⟨a + 1, b + 1, 1, 0, e⟩
    simp [fm]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨a + 1, b + 1, 1, 0, e⟩ = some ⟨a + 2, b, 0, 0, e⟩
    simp [fm]
  apply step_stepStar
  show fm ⟨a + 2, b, 0, 0, e⟩ = some ⟨a + 1, b, 2, 0, e⟩
  simp [fm]

theorem drain_chain : ∀ k a b e,
    ⟨a, b + 2 * k, 2, 0, e⟩ [fm]⊢* ⟨a + k, b, 2, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    apply stepStar_trans
    · exact stepPlus_stepStar (drain_pair a (b + 2 * k) e)
    apply stepStar_trans (ih _ b e)
    ring_nf; finish

theorem main_trans_even (m : ℕ) :
    ⟨0, 0, 2 * m + 2, 0, 2 * m⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 2 * m + 3, 0, 2 * m + 1⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2 * m + 2, 2 * m, 0⟩)
  · have h := e_to_d (2 * m) (2 * m + 2) 0 0
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2, 2 * m + 1, 2 * m, 1⟩)
  · rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]; simp [fm]
  apply stepStar_trans (c₂ := ⟨m, 2, 1, m, m + 1⟩)
  · have h := triangle_chain m 0 1 m 1
    rw [show 1 + 2 * m = 2 * m + 1 from by ring,
        show m + m = 2 * m from by ring,
        show 0 + m = m from by ring,
        show 1 + m = m + 1 from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨m + 1, 1, 0, m, m + 1⟩)
  · apply step_stepStar
    show fm ⟨m, 2, 1, m, m + 1⟩ = some ⟨m + 1, 1, 0, m, m + 1⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨1, 2 * m + 1, 0, 0, 2 * m + 1⟩)
  · have h := a_d_to_b_e m 1 1 0 (m + 1)
    simp only [Nat.zero_add] at h
    rw [show 1 + m = m + 1 from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring,
        show m + 1 + m = 2 * m + 1 from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨0, 2 * m + 1, 2, 0, 2 * m + 1⟩)
  · apply step_stepStar
    show fm ⟨1, 2 * m + 1, 0, 0, 2 * m + 1⟩ = some ⟨0, 2 * m + 1, 2, 0, 2 * m + 1⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨m, 1, 2, 0, 2 * m + 1⟩)
  · have h := drain_chain m 0 1 (2 * m + 1)
    rw [show 1 + 2 * m = 2 * m + 1 from by ring,
        show 0 + m = m from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨m + 1, 0, 1, 0, 2 * m + 1⟩)
  · apply step_stepStar
    show fm ⟨m, 1, 2, 0, 2 * m + 1⟩ = some ⟨m + 1, 0, 1, 0, 2 * m + 1⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨m, 0, 3, 0, 2 * m + 1⟩)
  · apply step_stepStar
    show fm ⟨m + 1, 0, 1, 0, 2 * m + 1⟩ = some ⟨m, 0, 3, 0, 2 * m + 1⟩
    simp [fm]
  · have h := a_to_c m 3 (2 * m + 1)
    rw [show 3 + 2 * m = 2 * m + 3 from by ring] at h
    exact h

theorem main_trans_odd (m : ℕ) :
    ⟨0, 0, 2 * m + 3, 0, 2 * m + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 2 * m + 4, 0, 2 * m + 2⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2 * m + 3, 2 * m + 1, 0⟩)
  · have h := e_to_d (2 * m + 1) (2 * m + 3) 0 0
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2, 2 * m + 2, 2 * m + 1, 1⟩)
  · rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]; simp [fm]
  apply stepStar_trans (c₂ := ⟨m + 1, 2, 0, m, m + 2⟩)
  · have h := triangle_chain (m + 1) 0 0 m 1
    rw [show 0 + 2 * (m + 1) = 2 * m + 2 from by ring,
        show m + (m + 1) = 2 * m + 1 from by ring,
        show 0 + (m + 1) = m + 1 from by ring,
        show 1 + (m + 1) = m + 2 from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨1, 2 * m + 2, 0, 0, 2 * m + 2⟩)
  · have h := a_d_to_b_e m 1 2 0 (m + 2)
    simp only [Nat.zero_add] at h
    rw [show 1 + m = m + 1 from by ring,
        show 2 + 2 * m = 2 * m + 2 from by ring,
        show m + 2 + m = 2 * m + 2 from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨0, 2 * m + 2, 2, 0, 2 * m + 2⟩)
  · apply step_stepStar
    show fm ⟨1, 2 * m + 2, 0, 0, 2 * m + 2⟩ = some ⟨0, 2 * m + 2, 2, 0, 2 * m + 2⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨m + 1, 0, 2, 0, 2 * m + 2⟩)
  · have h := drain_chain (m + 1) 0 0 (2 * m + 2)
    rw [show 0 + 2 * (m + 1) = 2 * m + 2 from by ring,
        show 0 + (m + 1) = m + 1 from by ring] at h
    exact h
  · have h := a_to_c (m + 1) 2 (2 * m + 2)
    rw [show 2 + 2 * (m + 1) = 2 * m + 4 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 0, n⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨0, 0, n + 2, 0, n⟩ [fm]⊢⁺ ⟨0, 0, n + 1 + 2, 0, n + 1⟩
  rw [show n + 1 + 2 = n + 3 from by ring]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n even
    subst hm
    convert main_trans_even m using 2; ring_nf
  · -- n odd
    subst hm
    exact main_trans_odd m

end Sz22_2003_unofficial_389
