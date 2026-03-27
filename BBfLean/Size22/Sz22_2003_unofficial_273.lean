import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #273: [14/15, 27/22, 125/2, 11/7, 3/5]

Vector representation:
```
 1 -1 -1  1  0
-1  3  0  0 -1
-1  0  3  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_273

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, e+k⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    have h := ih c d (e + 1)
    rw [show e + 1 + k = e + (k + 1) from by ring] at h
    exact h

theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, (0 : ℕ), c+3*k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

theorem r1_chain : ∀ k a b c d e, ⟨a, b+k, c+k, d, e⟩ [fm]⊢* ⟨a+k, b, c, d+k, e⟩ := by
  intro k; induction k with
  | zero => intro a b c d e; exists 0
  | succ k ih =>
    intro a b c d e
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _ _)
    ring_nf; finish

theorem r2_chain : ∀ k a b d e, ⟨a+k, b, 0, d, e+k⟩ [fm]⊢* ⟨a, b+3*k, (0 : ℕ), d, e⟩ := by
  intro k; induction k with
  | zero => intro a b d e; exists 0
  | succ k ih =>
    intro a b d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

theorem mix_round : ∀ k A c d e, ⟨A+1, 0, c+3*k, d, e+k⟩ [fm]⊢* ⟨A+2*k+1, (0 : ℕ), c, d+3*k, e⟩ := by
  intro k; induction k with
  | zero => intro A c d e; simp; exists 0
  | succ k ih =>
    intro A c d e
    rw [show c + 3 * (k + 1) = (c + 3 * k) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show (3 : ℕ) = 0 + 3 from by ring,
        show c + 3 * k + 3 = (c + 3 * k) + 3 from by ring]
    apply stepStar_trans (r1_chain 3 _ _ _ _ _)
    rw [show A + 3 = (A + 2) + 1 from by ring]
    have h := ih (A + 2) c (d + 3) e
    rw [show A + 2 + 2 * k + 1 = A + 2 * (k + 1) + 1 from by ring,
        show d + 3 + 3 * k = d + 3 * (k + 1) from by ring] at h
    exact h

theorem drain : ∀ k A b d, ⟨A+1, b+3*k, 0, d, 0⟩ [fm]⊢* ⟨A+2*k+1, b, (0 : ℕ), d+3*k, 0⟩ := by
  intro k; induction k with
  | zero => intro A b d; simp; exists 0
  | succ k ih =>
    intro A b d
    rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring]
    step fm
    rw [show b + 3 * k + 3 = (b + 3 * k) + 3 from by ring,
        show (3 : ℕ) = 0 + 3 from by ring]
    apply stepStar_trans (r1_chain 3 _ _ _ _ _)
    rw [show A + 3 = (A + 2) + 1 from by ring]
    have h := ih (A + 2) b (d + 3)
    rw [show A + 2 + 2 * k + 1 = A + 2 * (k + 1) + 1 from by ring,
        show d + 3 + 3 * k = d + 3 * (k + 1) from by ring] at h
    exact h

theorem full_drain_0 (M A d : ℕ) : ⟨A+1, 3*M, 0, d, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, 3*A+6*M+3, d+3*M, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨A+2*M+1, 0, 0, d+3*M, 0⟩)
  · have h := drain M A 0 d
    simp only [Nat.zero_add] at h
    exact h
  have h := a_to_c (A+2*M+1) 0 0 (d+3*M)
  simp only [Nat.zero_add] at h
  rw [show 3 * (A + 2 * M + 1) = 3*A+6*M+3 from by ring] at h
  exact h

theorem full_drain_1 (M A d : ℕ) : ⟨A+1, 3*M+1, 0, d, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, 3*A+6*M+5, d+3*M+1, 0⟩ := by
  rw [show (3*M+1 : ℕ) = 1 + 3*M from by ring]
  apply stepStar_trans (c₂ := ⟨A+2*M+1, 1, 0, d+3*M, 0⟩)
  · exact drain M A 1 d
  rw [show A+2*M+1 = (A+2*M) + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r1_chain 1 (A+2*M) 0 2 (d+3*M) 0)
  have h := a_to_c (A+2*M+1) 0 2 (d+3*M+1)
  simp only [Nat.zero_add] at h
  rw [show 2 + 3 * (A + 2 * M + 1) = 3*A+6*M+5 from by ring] at h
  exact h

theorem full_drain_2 (M A d : ℕ) : ⟨A+1, 3*M+2, 0, d, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, 3*A+6*M+7, d+3*M+2, 0⟩ := by
  rw [show (3*M+2 : ℕ) = 2 + 3*M from by ring]
  apply stepStar_trans (c₂ := ⟨A+2*M+1, 2, 0, d+3*M, 0⟩)
  · exact drain M A 2 d
  rw [show A+2*M+1 = (A+2*M) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 0 + 2 from by ring, show (3 : ℕ) = 1 + 2 from by ring]
  apply stepStar_trans (r1_chain 2 (A+2*M) 0 1 (d+3*M) 0)
  have h := a_to_c (A+2*M+2) 0 1 (d+3*M+2)
  simp only [Nat.zero_add] at h
  rw [show 1 + 3 * (A + 2 * M + 2) = 3*A+6*M+7 from by ring] at h
  exact h

theorem endgame_r0 (q E : ℕ) (hAE : 2*q ≥ E) :
    ⟨2*q+1, 0, 0, 3*q+1, E⟩ [fm]⊢* ⟨(0 : ℕ), 0, 6*q+3*E+3, 3*q+3*E+1, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨2*q+1-E, 3*E, 0, 3*q+1, 0⟩)
  · have h := r2_chain E (2*q+1-E) 0 (3*q+1) 0
    rw [show 2*q+1-E+E = 2*q+1 from by omega,
        show 0 + E = E from by ring,
        show 0 + 3 * E = 3 * E from by ring] at h
    exact h
  rw [show (2*q+1-E : ℕ) = (2*q-E) + 1 from by omega]
  apply stepStar_trans (full_drain_0 E (2*q-E) (3*q+1))
  rw [show 3*(2*q-E)+6*E+3 = 6*q+3*E+3 from by omega,
      show 3*q+1+3*E = 3*q+3*E+1 from by ring]
  finish

theorem endgame_r1 (q E' : ℕ) (hAE : 2*q ≥ E') :
    ⟨2*q+1, 0, 1, 3*q+1, E'+1⟩ [fm]⊢* ⟨(0 : ℕ), 0, 6*q+3*E'+7, 3*q+3*E'+4, 0⟩ := by
  rw [show (2*q+1 : ℕ) = 2*q + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨2*q, 3, 1, 3*q+1, E'⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨2*q+1, 2, 0, 3*q+2, E'⟩)
  · rw [show (3 : ℕ) = 2 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (r1_chain 1 (2*q) 2 0 (3*q+1) E')
    ring_nf; finish
  apply stepStar_trans (c₂ := ⟨2*q+1-E', 3*E'+2, 0, 3*q+2, 0⟩)
  · have h := r2_chain E' (2*q+1-E') 2 (3*q+2) 0
    rw [show 2*q+1-E'+E' = 2*q+1 from by omega,
        show 0 + E' = E' from by ring,
        show 2 + 3 * E' = 3*E'+2 from by ring] at h
    exact h
  rw [show (2*q+1-E' : ℕ) = (2*q-E') + 1 from by omega]
  apply stepStar_trans (full_drain_2 E' (2*q-E') (3*q+2))
  rw [show 3*(2*q-E')+6*E'+7 = 6*q+3*E'+7 from by omega,
      show 3*q+2+3*E'+2 = 3*q+3*E'+4 from by ring]
  finish

theorem endgame_r2 (q E' : ℕ) (hAE : 2*q+1 ≥ E') :
    ⟨2*q+1, 0, 2, 3*q+1, E'+1⟩ [fm]⊢* ⟨(0 : ℕ), 0, 6*q+3*E'+8, 3*q+3*E'+4, 0⟩ := by
  rw [show (2*q+1 : ℕ) = 2*q + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨2*q, 3, 2, 3*q+1, E'⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨2*q+2, 1, 0, 3*q+3, E'⟩)
  · rw [show (3 : ℕ) = 1 + 2 from by ring, show (2 : ℕ) = 0 + 2 from by ring]
    apply stepStar_trans (r1_chain 2 (2*q) 1 0 (3*q+1) E')
    ring_nf; finish
  apply stepStar_trans (c₂ := ⟨2*q+2-E', 3*E'+1, 0, 3*q+3, 0⟩)
  · have h := r2_chain E' (2*q+2-E') 1 (3*q+3) 0
    rw [show 2*q+2-E'+E' = 2*q+2 from by omega,
        show 0 + E' = E' from by ring,
        show 1 + 3 * E' = 3*E'+1 from by ring] at h
    exact h
  rw [show (2*q+2-E' : ℕ) = (2*q+1-E') + 1 from by omega]
  apply stepStar_trans (full_drain_1 E' (2*q+1-E') (3*q+3))
  rw [show 3*(2*q+1-E')+6*E'+5 = 6*q+3*E'+8 from by omega,
      show 3*q+3+3*E'+1 = 3*q+3*E'+4 from by ring]
  finish

theorem main_trans (C D : ℕ) (_ : D ≥ 1) (hClo : C ≥ D + 2) (hChi : C ≤ 3*D + 2) :
    ⟨0, 0, C, D, 0⟩ [fm]⊢⁺ ⟨0, 0, C + 3*D + 1, 3*D + 1, 0⟩ := by
  set q := (C - 2) / 3
  set r := (C - 2) % 3
  have hCqr : C = 3*q + r + 2 := by omega
  have hr3 : r < 3 := Nat.mod_lt _ (by omega)
  have hqD : q ≤ D := by omega
  set E := D - q
  have hDE : D = q + E := by omega
  -- Phase 1: d_to_e
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, C, 0, D⟩)
  · have h := d_to_e D C 0 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 2: R5 + R1
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, C-1, 0, D⟩)
  · rw [show C = (C - 1) + 1 from by omega]; simp [fm]
  apply stepStar_trans (c₂ := ⟨1, 0, C-2, 1, D⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring, show C - 1 = (C - 2) + 1 from by omega]
    step fm; finish
  -- Phase 3: mix_round
  apply stepStar_trans (c₂ := ⟨2*q+1, 0, r, 3*q+1, E⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show C - 2 = r + 3 * q from by omega,
        show D = E + q from by omega]
    have h := mix_round q 0 r 1 E
    rw [show 0 + 2 * q + 1 = 2 * q + 1 from by ring,
        show 1 + 3 * q = 3 * q + 1 from by ring] at h
    exact h
  -- Phase 4: Endgame based on r ∈ {0, 1, 2}
  have hr0 : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hr0 with hr | hr | hr <;> simp only [hr] at *
  · -- r = 0: C = 3q+2, D ≤ 3q, E ≤ 2q
    apply stepStar_trans (endgame_r0 q E (by omega))
    rw [show C + 3*D + 1 = 6*q+3*E+3 from by omega,
        show 3*D + 1 = 3*q+3*E+1 from by omega]; finish
  · -- r = 1: C = 3q+3, D ≤ 3q+1, E ≤ 2q+1, E ≥ 1
    have hE1 : E ≥ 1 := by omega
    rw [show E = (E - 1) + 1 from by omega]
    apply stepStar_trans (endgame_r1 q (E - 1) (by omega))
    rw [show C + 3*D + 1 = 6*q+3*(E-1)+7 from by omega,
        show 3*D + 1 = 3*q+3*(E-1)+4 from by omega]; finish
  · -- r = 2: C = 3q+4, D ≤ 3q+2, E ≤ 2q+2, E ≥ 1
    have hE1 : E ≥ 1 := by omega
    rw [show E = (E - 1) + 1 from by omega]
    apply stepStar_trans (endgame_r2 q (E - 1) (by omega))
    rw [show C + 3*D + 1 = 6*q+3*(E-1)+8 from by omega,
        show 3*D + 1 = 3*q+3*(E-1)+4 from by omega]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c, d, 0⟩ ∧ c ≥ d + 2 ∧ c ≤ 3*d + 2 ∧ d ≥ 1)
  · intro q ⟨c, d, hq, hlo, hhi, hd⟩
    subst hq
    exact ⟨⟨0, 0, c + 3*d + 1, 3*d + 1, 0⟩,
           ⟨c + 3*d + 1, 3*d + 1, rfl, by omega, by omega, by omega⟩,
           main_trans c d hd hlo hhi⟩
  · exact ⟨4, 1, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_273
