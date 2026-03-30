import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #817: [35/6, 8/55, 11/2, 3/7, 28/11]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_817

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
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
    rw [show (k + 1 : ℕ) = k + 1 from rfl,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 3) d e)
    ring_nf; finish

theorem loop : ∀ B, ∀ C D e, ⟨3, B, C, D, e + C + B⟩ [fm]⊢* ⟨3 + 3 * C + 2 * B, 0, 0, D + B, e⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih
  intro C D e
  rcases (show B = 0 ∨ B = 1 ∨ B = 2 ∨ B ≥ 3 from by omega) with rfl | rfl | rfl | hB
  · rw [show e + C + 0 = e + C from by ring,
        show 3 + 3 * C + 2 * 0 = 3 + 3 * C from by ring,
        show D + 0 = D from by ring]
    exact r2_drain C 3 D e
  · rw [show e + C + 1 = e + (C + 1) from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    rw [show 3 + 3 * C + 2 * 1 = 2 + 3 * (C + 1) from by ring]
    exact r2_drain (C + 1) 2 (D + 1) e
  · rw [show e + C + 2 = e + (C + 2) from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm; step fm
    rw [show (C + 1 + 1 : ℕ) = C + 2 from by ring,
        show (D + 1 + 1 : ℕ) = D + 2 from by ring,
        show 3 + 3 * C + 2 * 2 = 1 + 3 * (C + 2) from by ring]
    exact r2_drain (C + 2) 1 (D + 2) e
  · obtain ⟨B', rfl⟩ : ∃ B', B = B' + 3 := ⟨B - 3, by omega⟩
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

theorem mid_phase_0 (f : ℕ) :
    ⟨(0 : ℕ), 0 + 1, 0, 0, f + 0 + 2⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 0 + 2, f + 0 + 2 + 0 + 2⟩ := by
  step fm; step fm; step fm
  rw [show (4 : ℕ) = 0 + 4 from by ring]
  apply stepStar_trans (a_to_e 4 0 2 f)
  ring_nf; finish

theorem mid_phase_succ (n f : ℕ) :
    ⟨(0 : ℕ), n + 2, 0, 0, f + n + 3⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, n + 3, f + n + 3 + (n + 1) + 2⟩ := by
  rw [show f + n + 3 = (f + 1 + n) + 1 + 1 from by ring,
      show (n + 2 : ℕ) = n + 1 + 0 + 1 from by ring]
  step fm; step fm; step fm
  rw [show (f + 1 + n : ℕ) = f + 1 + n from rfl,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show f + 1 + n = f + 1 + n from rfl]
  apply stepStar_trans (loop n 1 3 f)
  rw [show 3 + 3 * 1 + 2 * n = 0 + (2 * n + 6) from by ring,
      show 3 + n = n + 3 from by ring]
  apply stepStar_trans (a_to_e (2 * n + 6) 0 (n + 3) f)
  ring_nf; finish

theorem full_cycle (n f : ℕ) :
    ⟨0, 0, 0, n + 1, f + n + 2⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, n + 2, f + 2 * n + 4⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show (n + 1 : ℕ) = 0 + (n + 1) from by ring]
    exact d_to_b (n + 1) 0 0
  rw [show (0 + (n + 1) : ℕ) = n + 1 from by ring]
  rcases n with _ | n
  · -- n = 0
    apply stepPlus_stepStar_stepPlus (mid_phase_0 f)
    ring_nf; finish
  · -- n + 1
    rw [show f + (n + 1) + 2 = f + n + 3 from by ring]
    apply stepPlus_stepStar_stepPlus (mid_phase_succ n f)
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩)
  · execute fm 4
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n e, q = ⟨0, 0, 0, n + 1, e⟩ ∧ e ≥ n + 2)
  · intro c ⟨n, e, hq, he⟩; subst hq
    obtain ⟨f, rfl⟩ : ∃ f, e = f + n + 2 := ⟨e - n - 2, by omega⟩
    exact ⟨⟨0, 0, 0, n + 2, f + 2 * n + 4⟩,
      ⟨n + 1, f + 2 * n + 4, rfl, by omega⟩,
      full_cycle n f⟩
  · exact ⟨0, 2, rfl, by omega⟩

end Sz22_2003_unofficial_817
