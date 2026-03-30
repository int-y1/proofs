import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #816: [35/6, 8/55, 11/2, 3/7, 12/11]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 2  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_816

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | _ => none

theorem d_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b d; exists 0
  | succ k ih =>
    intro b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b + 1) d); ring_nf; finish

theorem a_to_e : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a d (e + 1)); ring_nf; finish

theorem r2_drain : ∀ k, ∀ a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; apply stepStar_trans (ih (a + 3) d e); ring_nf; finish

theorem loop : ∀ B, ∀ C D e, ⟨3, B, C, D, e + C + B⟩ [fm]⊢* ⟨3 + 3 * C + 2 * B, 0, 0, D + B, e⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih
  intro C D e
  rcases (show B = 0 ∨ B = 1 ∨ B = 2 ∨ B ≥ 3 from by omega) with rfl | rfl | rfl | hB
  · -- B = 0
    rw [show e + C + 0 = e + C from by ring,
        show 3 + 3 * C + 2 * 0 = 3 + 3 * C from by ring,
        show D + 0 = D from by ring]
    exact r2_drain C 3 D e
  · -- B = 1
    rw [show e + C + 1 = e + (C + 1) from by ring,
        show (1 : ℕ) = 0 + 1 from by ring,
        show 3 + 3 * C + 2 * 1 = 2 + 3 * (C + 1) from by ring]
    step fm
    exact r2_drain (C + 1) 2 (D + 1) e
  · -- B = 2
    rw [show e + C + 2 = e + (C + 2) from by ring,
        show (2 : ℕ) = 1 + 1 from by ring,
        show 3 + 3 * C + 2 * 2 = 1 + 3 * (C + 2) from by ring]
    step fm; step fm
    rw [show (C + 1 + 1 : ℕ) = C + 2 from by ring,
        show (D + 1 + 1 : ℕ) = D + 2 from by ring]
    exact r2_drain (C + 2) 1 (D + 2) e
  · -- B >= 3
    obtain ⟨B', rfl⟩ : ∃ B', B = B' + 3 := ⟨B - 3, by omega⟩
    rw [show e + C + (B' + 3) = (e + (C + 2) + B') + 1 from by ring,
        show (B' + 3 : ℕ) = B' + 2 + 1 from by ring]
    step fm
    rw [show (B' + 2 : ℕ) = B' + 1 + 1 from by ring]
    step fm
    rw [show (B' + 1 : ℕ) = B' + 0 + 1 from by ring]
    step fm
    rw [show (C + 1 + 1 + 1 : ℕ) = (C + 2) + 1 from by ring,
        show e + (C + 2) + B' = (e + (C + 2) + B') from rfl]
    step fm
    rw [show (D + 1 + 1 + 1 : ℕ) = D + 3 from by ring]
    apply stepStar_trans (ih B' (by omega) (C + 2) (D + 3) e)
    ring_nf; finish

theorem setup_phase (n t : ℕ) (ht : t ≥ 2) :
    ⟨(0 : ℕ), n + 1, 0, 0, t⟩ [fm]⊢* ⟨3, n, 1, 2, t - 2⟩ := by
  rw [show t = (t - 2) + 1 + 1 from by omega,
      show (n + 1 : ℕ) = n + 0 + 1 from by ring]
  step fm
  rw [show (n + 0 + 1 + 1 : ℕ) = n + 0 + 1 + 1 from rfl]
  step fm; step fm
  rw [show (t - 2 + 1 : ℕ) = (t - 2) + 1 from rfl,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  finish

theorem full_cycle (n t : ℕ) (ht : t ≥ n + 3) :
    ⟨0, 0, 0, n + 1, t⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, n + 2, t + n + 3⟩ := by
  have h1 : ⟨0, 0, 0, n + 1, t⟩ [fm]⊢* ⟨(0 : ℕ), n + 1, 0, 0, t⟩ := by
    rw [show (n + 1 : ℕ) = 0 + (n + 1) from by ring]
    exact d_to_b (n + 1) 0 0
  have h2 : ⟨(0 : ℕ), n + 1, 0, 0, t⟩ [fm]⊢* ⟨3, n, 1, 2, t - 2⟩ := by
    exact setup_phase n t (by omega)
  have h3 : ⟨3, n, 1, 2, t - 2⟩ [fm]⊢* ⟨2 * n + 6, 0, 0, n + 2, t - n - 3⟩ := by
    rw [show t - 2 = (t - n - 3) + 1 + n from by omega]
    have := loop n 1 2 (t - n - 3)
    rw [show 3 + 3 * 1 + 2 * n = 2 * n + 6 from by ring,
        show 2 + n = n + 2 from by ring] at this
    exact this
  have h4 : ⟨2 * n + 6, 0, 0, n + 2, t - n - 3⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, n + 2, t + n + 3⟩ := by
    rw [show (2 * n + 6 : ℕ) = 0 + (2 * n + 6) from by ring]
    have := a_to_e (2 * n + 6) 0 (n + 2) (t - n - 3)
    rw [show t - n - 3 + (2 * n + 6) = t + n + 3 from by omega] at this
    exact this
  have h12 : ⟨0, 0, 0, n + 1, t⟩ [fm]⊢* ⟨3, n, 1, 2, t - 2⟩ :=
    stepStar_trans h1 h2
  have h34 : ⟨3, n, 1, 2, t - 2⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, n + 2, t + n + 3⟩ :=
    stepStar_trans h3 h4
  have h1234 : ⟨0, 0, 0, n + 1, t⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, n + 2, t + n + 3⟩ :=
    stepStar_trans h12 h34
  exact stepStar_stepPlus h1234 (by
    intro h
    have := congr_arg Prod.fst (congr_arg Prod.snd (congr_arg Prod.snd (congr_arg Prod.snd h)))
    simp at this)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩)
  · execute fm 8
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n t, q = ⟨0, 0, 0, n + 1, t⟩ ∧ t ≥ n + 3)
  · intro c ⟨n, t, hq, ht⟩; subst hq
    exact ⟨⟨0, 0, 0, n + 2, t + n + 3⟩,
      ⟨n + 1, t + n + 3, rfl, by omega⟩,
      full_cycle n t ht⟩
  · exact ⟨0, 3, rfl, by omega⟩
