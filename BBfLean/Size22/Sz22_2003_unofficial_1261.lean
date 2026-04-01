import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1261: [5/6, 8/35, 539/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
 3  0 -1 -1  0
-1  0  0  2  1
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1261

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem a_drain : ∀ k : ℕ, ∀ d e, ⟨k, (0 : ℕ), (0 : ℕ), d, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

theorem d_to_b : ∀ k : ℕ, ∀ b e, ⟨(0 : ℕ), b, (0 : ℕ), k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + k, (0 : ℕ), (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

theorem main_loop : ∀ k : ℕ, ∀ b c e, ⟨(0 : ℕ), b + 4 * k, c, (0 : ℕ), e + k⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 3 * k, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + 4 * (k + 1) = (b + 4 * k) + 4 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 3) e)
    ring_nf; finish

theorem c_drain :
    ∀ c : ℕ, ∀ a e, ⟨a + 1, (0 : ℕ), c, (0 : ℕ), e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 2 * a + 5 * c + 2, e + a + 3 * c + 1⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih; intro a e
  rcases c with _ | _ | c
  · apply stepStar_trans (a_drain (a + 1) 0 e)
    ring_nf; finish
  · step fm; step fm
    apply stepStar_trans (a_drain (a + 3) 1 (e + 1))
    ring_nf; finish
  · step fm; step fm; step fm
    rw [show a + 6 = (a + 5) + 1 from by ring]
    apply stepStar_trans (ih c (by omega) (a + 5) (e + 1))
    ring_nf; finish

theorem trans_r0 (q e : ℕ) (he : e ≥ q + 2) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * q + 4, e⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 15 * q + 18, e + 8 * q + 8⟩ := by
  obtain ⟨E, hE⟩ : ∃ E, e = E + q + 2 := ⟨e - q - 2, by omega⟩
  subst hE
  apply stepStar_stepPlus
  · apply stepStar_trans (d_to_b (4 * q + 4) 0 (E + q + 2))
    rw [show (0 : ℕ) + (4 * q + 4) = 0 + 4 * (q + 1) from by ring,
        show E + q + 2 = (E + 1) + (q + 1) from by ring]
    apply stepStar_trans (main_loop (q + 1) 0 0 (E + 1))
    rw [show 0 + 3 * (q + 1) = (3 * q + 2) + 1 from by ring]
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨0, 0, (3 * q + 2) + 1, 0, E + 1⟩ : Q) [fm]⊢ ⟨1, 0, (3 * q + 2) + 1, 1, E⟩))
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨1, 0, (3 * q + 2) + 1, 1, E⟩ : Q) [fm]⊢ ⟨4, 0, 3 * q + 2, 0, E⟩))
    rw [show (4 : ℕ) = 3 + 1 from by ring]
    apply stepStar_trans (c_drain (3 * q + 2) 3 E)
    ring_nf; finish
  · simp [Q]; omega

theorem trans_r1 (q e : ℕ) (he : e ≥ q + 1) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * q + 1, e⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 15 * q + 6, e + 8 * q + 2⟩ := by
  obtain ⟨E, hE⟩ : ∃ E, e = E + q + 1 := ⟨e - q - 1, by omega⟩
  subst hE
  apply stepStar_stepPlus
  · apply stepStar_trans (d_to_b (4 * q + 1) 0 (E + q + 1))
    rw [show (0 : ℕ) + (4 * q + 1) = 1 + 4 * q from by ring,
        show E + q + 1 = (E + 1) + q from by ring]
    apply stepStar_trans (main_loop q 1 0 (E + 1))
    rw [show 0 + 3 * q = 3 * q from by ring]
    rcases q with _ | q
    · apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 1, 0, 0, E + 1⟩ : Q) [fm]⊢ ⟨1, 1, 0, 1, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨1, 1, 0, 1, E⟩ : Q) [fm]⊢ ⟨0, 0, 1, 1, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 0, 1, 1, E⟩ : Q) [fm]⊢ ⟨3, 0, 0, 0, E⟩))
      apply stepStar_trans (a_drain 3 0 E)
      ring_nf; finish
    · rw [show 3 * (q + 1) = (3 * q + 2) + 1 from by ring]
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 1, (3 * q + 2) + 1, 0, E + 1⟩ : Q) [fm]⊢ ⟨1, 1, (3 * q + 2) + 1, 1, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨1, 1, (3 * q + 2) + 1, 1, E⟩ : Q) [fm]⊢ ⟨0, 0, (3 * q + 2) + 2, 1, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 0, (3 * q + 2) + 2, 1, E⟩ : Q) [fm]⊢ ⟨3, 0, (3 * q + 2) + 1, 0, E⟩))
      rw [show (3 : ℕ) = 2 + 1 from by ring, show (3 * q + 2) + 1 = 3 * q + 3 from by ring]
      apply stepStar_trans (c_drain (3 * q + 3) 2 E)
      ring_nf; finish
  · simp [Q]; omega

theorem trans_r2 (q e : ℕ) (he : e ≥ q + 1) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * q + 2, e⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 15 * q + 9, e + 8 * q + 4⟩ := by
  obtain ⟨E, hE⟩ : ∃ E, e = E + q + 1 := ⟨e - q - 1, by omega⟩
  subst hE
  apply stepStar_stepPlus
  · apply stepStar_trans (d_to_b (4 * q + 2) 0 (E + q + 1))
    rw [show (0 : ℕ) + (4 * q + 2) = 2 + 4 * q from by ring,
        show E + q + 1 = (E + 1) + q from by ring]
    apply stepStar_trans (main_loop q 2 0 (E + 1))
    rw [show 0 + 3 * q = 3 * q from by ring]
    rcases q with _ | q
    · apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 2, 0, 0, E + 1⟩ : Q) [fm]⊢ ⟨1, 2, 0, 1, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨1, 2, 0, 1, E⟩ : Q) [fm]⊢ ⟨0, 1, 1, 1, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 1, 1, 1, E⟩ : Q) [fm]⊢ ⟨3, 1, 0, 0, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨3, 1, 0, 0, E⟩ : Q) [fm]⊢ ⟨2, 0, 1, 0, E⟩))
      rw [show (2 : ℕ) = 1 + 1 from by ring]
      apply stepStar_trans (c_drain 1 1 E)
      ring_nf; finish
    · rw [show 3 * (q + 1) = (3 * q + 2) + 1 from by ring]
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 2, (3 * q + 2) + 1, 0, E + 1⟩ : Q) [fm]⊢ ⟨1, 2, (3 * q + 2) + 1, 1, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨1, 2, (3 * q + 2) + 1, 1, E⟩ : Q) [fm]⊢ ⟨0, 1, (3 * q + 2) + 2, 1, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 1, (3 * q + 2) + 2, 1, E⟩ : Q) [fm]⊢ ⟨3, 1, (3 * q + 2) + 1, 0, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨3, 1, (3 * q + 2) + 1, 0, E⟩ : Q) [fm]⊢ ⟨2, 0, (3 * q + 2) + 2, 0, E⟩))
      rw [show (2 : ℕ) = 1 + 1 from by ring, show (3 * q + 2) + 2 = 3 * q + 4 from by ring]
      apply stepStar_trans (c_drain (3 * q + 4) 1 E)
      ring_nf; finish
  · simp [Q]; omega

theorem trans_r3 (q e : ℕ) (he : e ≥ q + 1) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * q + 3, e⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 15 * q + 12, e + 8 * q + 6⟩ := by
  obtain ⟨E, hE⟩ : ∃ E, e = E + q + 1 := ⟨e - q - 1, by omega⟩
  subst hE
  apply stepStar_stepPlus
  · apply stepStar_trans (d_to_b (4 * q + 3) 0 (E + q + 1))
    rw [show (0 : ℕ) + (4 * q + 3) = 3 + 4 * q from by ring,
        show E + q + 1 = (E + 1) + q from by ring]
    apply stepStar_trans (main_loop q 3 0 (E + 1))
    rw [show 0 + 3 * q = 3 * q from by ring]
    rcases q with _ | q
    · apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 3, 0, 0, E + 1⟩ : Q) [fm]⊢ ⟨1, 3, 0, 1, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨1, 3, 0, 1, E⟩ : Q) [fm]⊢ ⟨0, 2, 1, 1, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 2, 1, 1, E⟩ : Q) [fm]⊢ ⟨3, 2, 0, 0, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨3, 2, 0, 0, E⟩ : Q) [fm]⊢ ⟨2, 1, 1, 0, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨2, 1, 1, 0, E⟩ : Q) [fm]⊢ ⟨1, 0, 2, 0, E⟩))
      rw [show (1 : ℕ) = 0 + 1 from by ring]
      apply stepStar_trans (c_drain 2 0 E)
      ring_nf; finish
    · rw [show 3 * (q + 1) = (3 * q + 2) + 1 from by ring]
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 3, (3 * q + 2) + 1, 0, E + 1⟩ : Q) [fm]⊢ ⟨1, 3, (3 * q + 2) + 1, 1, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨1, 3, (3 * q + 2) + 1, 1, E⟩ : Q) [fm]⊢ ⟨0, 2, (3 * q + 2) + 2, 1, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 2, (3 * q + 2) + 2, 1, E⟩ : Q) [fm]⊢ ⟨3, 2, (3 * q + 2) + 1, 0, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨3, 2, (3 * q + 2) + 1, 0, E⟩ : Q) [fm]⊢ ⟨2, 1, (3 * q + 2) + 2, 0, E⟩))
      apply stepStar_trans (step_stepStar (by simp [fm] : (⟨2, 1, (3 * q + 2) + 2, 0, E⟩ : Q) [fm]⊢ ⟨1, 0, (3 * q + 2) + 3, 0, E⟩))
      rw [show (1 : ℕ) = 0 + 1 from by ring, show (3 * q + 2) + 3 = 3 * q + 5 from by ring]
      apply stepStar_trans (c_drain (3 * q + 5) 0 E)
      ring_nf; finish
  · simp [Q]; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 1 ∧ e ≥ 1 ∧ 4 * e ≥ d + 1)
  · intro c ⟨d, e, hq, hd, he, hinv⟩
    subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · rcases Nat.even_or_odd K with ⟨q, hq⟩ | ⟨q, hq⟩
      · -- d = K + K = (q+q) + (q+q) = 4q
        rcases q with _ | q
        · omega
        · have hd_eq : d = 4 * q + 4 := by omega
          rw [hd_eq]
          exact ⟨_, ⟨15 * q + 18, e + 8 * q + 8, rfl, by omega, by omega, by omega⟩,
            trans_r0 q e (by omega)⟩
      · -- d = K + K = (2q+1) + (2q+1) = 4q+2
        have hd_eq : d = 4 * q + 2 := by omega
        rw [hd_eq]
        exact ⟨_, ⟨15 * q + 9, e + 8 * q + 4, rfl, by omega, by omega, by omega⟩,
          trans_r2 q e (by omega)⟩
    · rcases Nat.even_or_odd K with ⟨q, hq⟩ | ⟨q, hq⟩
      · -- d = 2K + 1 = 4q + 1
        have hd_eq : d = 4 * q + 1 := by omega
        rw [hd_eq]
        exact ⟨_, ⟨15 * q + 6, e + 8 * q + 2, rfl, by omega, by omega, by omega⟩,
          trans_r1 q e (by omega)⟩
      · -- d = 2K + 1 = 2(2q+1) + 1 = 4q + 3
        have hd_eq : d = 4 * q + 3 := by omega
        rw [hd_eq]
        exact ⟨_, ⟨15 * q + 12, e + 8 * q + 6, rfl, by omega, by omega, by omega⟩,
          trans_r3 q e (by omega)⟩
  · exact ⟨2, 1, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_1261
