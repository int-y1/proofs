import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #827: [35/6, 8/55, 77/2, 3/7, 25/3]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  0 -1
-1  0  0  1  1
 0  1  0 -1  0
 0 -1  2  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_827

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

theorem d_to_b : ∀ k b d, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b + 1) d); ring_nf; finish

theorem r3_drain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a (d + 1) (e + 1)); ring_nf; finish

theorem r2_drain : ∀ k a c d, ⟨a, 0, c + k, d, k⟩ [fm]⊢* ⟨a + 3 * k, 0, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 3) c d); ring_nf; finish

theorem r3r2_chain : ∀ c a d,
    ⟨a + 1, 0, c + 1, d, 0⟩ [fm]⊢* ⟨a + 2 * c + 3, 0, 0, d + c + 1, 0⟩ := by
  intro c; induction' c with c ih <;> intro a d
  · step fm; step fm; ring_nf; finish
  · rw [show (c : ℕ) + 1 + 1 = (c + 1) + 1 from by ring]
    step fm; step fm; rw [show a + 1 + 2 = (a + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) (d + 1)); ring_nf; finish

theorem chain_r2r1 : ∀ k b c d e,
    ⟨0, b + 3 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, b, c + 1 + 2 * k, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3 * k) + 1 + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show c + 3 = (c + 2) + 1 from by ring]
    apply stepStar_trans (ih b (c + 2) (d + 3) e); ring_nf; finish

theorem drain_and_peak : ∀ F a G d,
    ⟨a + 1, 0, G + 1 + F, d, F⟩ [fm]⊢*
    ⟨0, 0, 0, d + a + 3 * F + 3 * G + 4, a + 3 * F + 2 * G + 3⟩ := by
  intro F; induction' F with F ihF <;> intro a G d
  · rw [show G + 1 + 0 = G + 1 from by ring]
    apply stepStar_trans (r3r2_chain G a d)
    rw [show a + 2 * G + 3 = 0 + (a + 2 * G + 3) from by ring]
    apply stepStar_trans (r3_drain (a + 2 * G + 3) 0 (d + G + 1) 0)
    ring_nf; finish
  · rw [show G + 1 + (F + 1) = (G + 1 + F) + 1 from by ring,
        show (F : ℕ) + 1 = F + 1 from by ring]
    step fm
    rw [show a + 1 + 3 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ihF (a + 3) G d)
    ring_nf; finish

theorem middle_r0_param (K F G : ℕ) (hFG : F + G = 2 * K) :
    ⟨0, 3 * K, 2, 0, K + 1 + F⟩ [fm]⊢⁺ ⟨0, 0, 0, 9 * K + 6, 4 * K + F + 5⟩ := by
  rw [show (3 * K : ℕ) = 0 + 3 * K from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show K + 1 + F = (1 + F) + K from by ring]
  apply stepStar_stepPlus_stepPlus (chain_r2r1 K 0 1 0 (1 + F))
  rw [show 1 + 1 + 2 * K = (2 * K + 1) + 1 from by ring,
      show (1 + F : ℕ) = F + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (2 * K + 1) + 1, 0 + 3 * K, F + 1⟩ = some ⟨3, 0, 2 * K + 1, 0 + 3 * K, F⟩
    simp [fm]
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 2 * K + 1 = G + 1 + F from by omega]
  apply stepStar_trans (drain_and_peak F 2 G (0 + 3 * K))
  rw [show 0 + 3 * K + 2 + 3 * F + 3 * G + 4 = 9 * K + 6 from by omega,
      show 2 + 3 * F + 2 * G + 3 = 4 * K + F + 5 from by omega]
  finish

theorem middle_r1_param (K F G : ℕ) (hFG : F + G = 2 * K + 1) :
    ⟨0, 3 * K + 1, 2, 0, K + 1 + F⟩ [fm]⊢⁺ ⟨0, 0, 0, 9 * K + 9, 4 * K + F + 6⟩ := by
  rw [show (3 * K + 1 : ℕ) = 1 + 3 * K from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show K + 1 + F = (1 + F) + K from by ring]
  apply stepStar_stepPlus_stepPlus (chain_r2r1 K 1 1 0 (1 + F))
  rw [show 1 + 1 + 2 * K = (2 * K + 1) + 1 from by ring,
      show (1 + F : ℕ) = F + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 1, (2 * K + 1) + 1, 0 + 3 * K, F + 1⟩ = some ⟨3, 1, 2 * K + 1, 0 + 3 * K, F⟩
    simp [fm]
  -- R1 step: (3, 1, 2K+1, 0+3K, F) -> (2, 0, 2K+2, 0+3K+1, F)
  step fm
  -- Now goal: (2, 0, 2K+1+1, (0+3K)+1, F) ⊢* target
  rw [show 2 * K + 1 + 1 = G + 1 + F from by omega,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain_and_peak F 1 G ((0 + 3 * K) + 1))
  rw [show (0 + 3 * K) + 1 + 1 + 3 * F + 3 * G + 4 = 9 * K + 9 from by omega,
      show 1 + 3 * F + 2 * G + 3 = 4 * K + F + 6 from by omega]
  finish

theorem middle_r2_param (K F G : ℕ) (hFG : F + G = 2 * K + 2) :
    ⟨0, 3 * K + 2, 2, 0, K + 1 + F⟩ [fm]⊢⁺ ⟨0, 0, 0, 9 * K + 12, 4 * K + F + 7⟩ := by
  rw [show (3 * K + 2 : ℕ) = 2 + 3 * K from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show K + 1 + F = (1 + F) + K from by ring]
  apply stepStar_stepPlus_stepPlus (chain_r2r1 K 2 1 0 (1 + F))
  rw [show 1 + 1 + 2 * K = (2 * K + 1) + 1 from by ring,
      show (1 + F : ℕ) = F + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2, (2 * K + 1) + 1, 0 + 3 * K, F + 1⟩ = some ⟨3, 2, 2 * K + 1, 0 + 3 * K, F⟩
    simp [fm]
  -- R1 step: (3, 2, 2K+1, 0+3K, F) -> (2, 1, 2K+2, (0+3K)+1, F)
  step fm
  -- R1 step: (2, 1, 2K+1+1, (0+3K)+1, F) -> (1, 0, 2K+1+1+1, (0+3K)+1+1, F)
  step fm
  -- Now: (1, 0, 2K+1+1+1, (0+3K)+1+1, F) ⊢* target
  rw [show 2 * K + 1 + 1 + 1 = G + 1 + F from by omega,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (drain_and_peak F 0 G ((0 + 3 * K) + 1 + 1))
  rw [show (0 + 3 * K) + 1 + 1 + 0 + 3 * F + 3 * G + 4 = 9 * K + 12 from by omega,
      show 0 + 3 * F + 2 * G + 3 = 4 * K + F + 7 from by omega]
  finish

theorem r4_r5 (D : ℕ) : ⟨0, 0, 0, D + 1, E⟩ [fm]⊢* ⟨0, D, 2, 0, E⟩ := by
  rw [show D + 1 = 0 + (D + 1) from by ring]
  apply stepStar_trans (d_to_b (D + 1) 0 0)
  rw [show (0 : ℕ) + (D + 1) = D + 1 from by ring]
  step fm; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 6, 5⟩)
  · execute fm 11
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ D ≥ E ∧ E ≥ 2 ∧ D ≤ 3 * E)
  · intro c ⟨D, E, hq, hDE, hE, hD3E⟩; subst hq
    refine ⟨⟨0, 0, 0, 3 * D + 3, D + E + 3⟩,
      ⟨3 * D + 3, D + E + 3, rfl, by omega, by omega, by omega⟩, ?_⟩
    obtain ⟨K, rfl | rfl | rfl⟩ : ∃ K, D = 3 * K + 1 ∨ D = 3 * K + 2 ∨ D = 3 * K + 3 :=
      ⟨(D - 1) / 3, by omega⟩
    · apply stepStar_stepPlus_stepPlus (r4_r5 (3 * K))
      rw [show (E : ℕ) = K + 1 + (E - K - 1) from by omega,
          show 3 * (3 * K + 1) + 3 = 9 * K + 6 from by ring,
          show 3 * K + 1 + (K + 1 + (E - K - 1)) + 3 = 4 * K + (E - K - 1) + 5 from by omega]
      exact middle_r0_param K (E - K - 1) (2 * K - (E - K - 1)) (by omega)
    · apply stepStar_stepPlus_stepPlus (r4_r5 (3 * K + 1))
      rw [show (E : ℕ) = K + 1 + (E - K - 1) from by omega,
          show 3 * (3 * K + 2) + 3 = 9 * K + 9 from by ring,
          show 3 * K + 2 + (K + 1 + (E - K - 1)) + 3 = 4 * K + (E - K - 1) + 6 from by omega]
      exact middle_r1_param K (E - K - 1) (2 * K + 1 - (E - K - 1)) (by omega)
    · apply stepStar_stepPlus_stepPlus (r4_r5 (3 * K + 2))
      rw [show (E : ℕ) = K + 1 + (E - K - 1) from by omega,
          show 3 * (3 * K + 3) + 3 = 9 * K + 12 from by ring,
          show 3 * K + 3 + (K + 1 + (E - K - 1)) + 3 = 4 * K + (E - K - 1) + 7 from by omega]
      exact middle_r2_param K (E - K - 1) (2 * K + 2 - (E - K - 1)) (by omega)
  · exact ⟨6, 5, rfl, by omega, by omega, by omega⟩
