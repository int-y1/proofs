import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #198: [1/6, 3/35, 275/3, 2/5, 7/22, 3/2]

Vector representation:
```
-1 -1  0  0  0
 0  1 -1 -1  0
 0 -1  2  0  1
 1  0 -1  0  0
-1  0  0  1 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_198

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem b_drain : ∀ b c e, ⟨0, b, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2*b, 0, e + b⟩ := by
  intro b; induction b with
  | zero => intro c e; simp; exists 0
  | succ b ih =>
    intro c e; step fm
    apply stepStar_trans (ih (c + 2) (e + 1))
    have h1 : c + 2 + 2 * b = c + 2 * (b + 1) := by ring
    have h2 : e + 1 + b = e + (b + 1) := by ring
    rw [h1, h2]; finish

theorem c_to_a : ∀ c a e, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨a + c, 0, 0, 0, e⟩ := by
  intro c; induction c with
  | zero => intro a e; simp; exists 0
  | succ c ih =>
    intro a e; step fm
    apply stepStar_trans (ih (a + 1) e)
    have : a + 1 + c = a + (c + 1) := by ring
    rw [this]; finish

theorem ae_to_d : ∀ e r d, ⟨e + r, 0, 0, d, e⟩ [fm]⊢* ⟨r, 0, 0, d + e, 0⟩ := by
  intro e; induction e with
  | zero => intro r d; simp; exists 0
  | succ e ih =>
    intro r d
    have hr : (e + 1) + r = (e + r) + 1 := by ring
    rw [hr]; step fm
    apply stepStar_trans (ih r (d + 1))
    have : d + 1 + e = d + (e + 1) := by ring
    rw [this]; finish

theorem drain_step : ∀ k d, ⟨0, k+1, 0, d+2, k⟩ [fm]⊢* ⟨0, k+2, 0, d, k+1⟩ := by
  intro k d; step fm; step fm; step fm; finish

theorem drain_iter : ∀ j k r, ⟨0, k+1, 0, 2*j + r, k⟩ [fm]⊢* ⟨0, k+j+1, 0, r, k+j⟩ := by
  intro j; induction j with
  | zero => intro k r; simp; exists 0
  | succ j ih =>
    intro k r
    have h1 : 2 * (j + 1) + r = (2 * j + r) + 2 := by ring
    rw [h1]
    apply stepStar_trans (drain_step k (2*j + r))
    apply stepStar_trans (ih (k+1) r)
    have h2 : k + 1 + j + 1 = k + (j + 1) + 1 := by ring
    have h3 : k + 1 + j = k + (j + 1) := by ring
    rw [h2, h3]; finish

theorem tail_d0 (k : ℕ) : ⟨0, k+1, 0, 0, k⟩ [fm]⊢* ⟨1, 0, 0, 2*k+1, 0⟩ := by
  apply stepStar_trans (b_drain (k+1) 0 k)
  apply stepStar_trans (c_to_a (0 + 2 * (k + 1)) 0 (k + (k + 1)))
  have ha : 0 + (0 + 2 * (k + 1)) = (k + (k + 1)) + 1 := by ring
  rw [ha]
  apply stepStar_trans (ae_to_d (k + (k + 1)) 1 0)
  have : 0 + (k + (k + 1)) = 2*k+1 := by ring
  rw [this]; finish

theorem tail_d1 (k : ℕ) : ⟨0, k+1, 1, 0, k+1⟩ [fm]⊢* ⟨1, 0, 0, 2*k+2, 0⟩ := by
  apply stepStar_trans (b_drain (k+1) 1 (k+1))
  apply stepStar_trans (c_to_a (1 + 2 * (k + 1)) 0 (k + 1 + (k + 1)))
  have ha : 0 + (1 + 2 * (k + 1)) = (k + 1 + (k + 1)) + 1 := by ring
  rw [ha]
  apply stepStar_trans (ae_to_d (k + 1 + (k + 1)) 1 0)
  have : 0 + (k + 1 + (k + 1)) = 2*k+2 := by ring
  rw [this]; finish

theorem trans_even (j : ℕ) : ⟨0, 1, 0, 2*j+2, 0⟩ [fm]⊢⁺ ⟨0, 1, 0, 2*j+3, 0⟩ := by
  -- 3 initial steps
  apply step_stepPlus_stepPlus (by show fm ⟨0, 1, 0, 2*j+2, 0⟩ = some ⟨0, 0, 2, 2*j+2, 1⟩; simp [fm])
  apply step_stepPlus_stepPlus (by show fm ⟨0, 0, 2, 2*j+2, 1⟩ = some ⟨0, 1, 1, 2*j+1, 1⟩; simp [fm])
  apply step_stepPlus_stepPlus (by show fm ⟨0, 1, 1, 2*j+1, 1⟩ = some ⟨0, 2, 0, 2*j, 1⟩; simp [fm])
  -- drain
  apply stepStar_stepPlus_stepPlus (drain_iter j 1 0)
  -- endgame
  show ⟨0, 1 + j + 1, 0, 0, 1 + j⟩ [fm]⊢⁺ ⟨0, 1, 0, 2 * j + 3, 0⟩
  have h1 : 1 + j + 1 = (j + 1) + 1 := by ring
  have h2 : 1 + j = j + 1 := by ring
  rw [h1, h2]
  apply stepStar_step_stepPlus (tail_d0 (j+1))
  have : 2 * (j + 1) + 1 = 2 * j + 3 := by ring
  rw [this]; simp [fm]

theorem trans_odd (j : ℕ) : ⟨0, 1, 0, 2*j+3, 0⟩ [fm]⊢⁺ ⟨0, 1, 0, 2*j+4, 0⟩ := by
  apply step_stepPlus_stepPlus (by show fm ⟨0, 1, 0, 2*j+3, 0⟩ = some ⟨0, 0, 2, 2*j+3, 1⟩; simp [fm])
  apply step_stepPlus_stepPlus (by show fm ⟨0, 0, 2, 2*j+3, 1⟩ = some ⟨0, 1, 1, 2*j+2, 1⟩; simp [fm])
  apply step_stepPlus_stepPlus (by show fm ⟨0, 1, 1, 2*j+2, 1⟩ = some ⟨0, 2, 0, 2*j+1, 1⟩; simp [fm])
  -- drain
  apply stepStar_stepPlus_stepPlus (drain_iter j 1 1)
  -- ⟨0, j+2, 0, 1, j+1⟩
  show ⟨0, 1 + j + 1, 0, 1, 1 + j⟩ [fm]⊢⁺ ⟨0, 1, 0, 2 * j + 4, 0⟩
  have h1 : 1 + j + 1 = (j + 1) + 1 := by ring
  have h2 : 1 + j = j + 1 := by ring
  rw [h1, h2]
  -- 2 more steps: rule 3 then rule 2
  apply step_stepPlus_stepPlus (by show fm ⟨0, (j+1)+1, 0, 1, j+1⟩ = some ⟨0, j+1, 2, 1, j+2⟩; simp [fm])
  apply step_stepPlus_stepPlus (by show fm ⟨0, j+1, 2, 1, j+2⟩ = some ⟨0, j+2, 1, 0, j+2⟩; simp [fm])
  -- tail_d1
  show ⟨0, (j+1)+1, 1, 0, (j+1)+1⟩ [fm]⊢⁺ ⟨0, 1, 0, 2*j+4, 0⟩
  apply stepStar_step_stepPlus (tail_d1 (j+1))
  have : 2 * (j + 1) + 2 = 2 * j + 4 := by ring
  rw [this]; simp [fm]

theorem main_trans : ∀ n, ⟨0, 1, 0, n, 0⟩ [fm]⊢⁺ ⟨0, 1, 0, n+1, 0⟩ := by
  intro n
  match n with
  | 0 => execute fm 5
  | 1 => execute fm 9
  | n + 2 =>
    rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · show ⟨0, 1, 0, j + j + 2, 0⟩ [fm]⊢⁺ ⟨0, 1, 0, j + j + 2 + 1, 0⟩
      have h1 : j + j = 2 * j := by ring
      rw [h1]; exact trans_even j
    · show ⟨0, 1, 0, 2 * j + 1 + 2, 0⟩ [fm]⊢⁺ ⟨0, 1, 0, 2 * j + 1 + 2 + 1, 0⟩
      have h1 : 2 * j + 1 + 2 = 2 * j + 3 := by ring
      have h2 : 2 * j + 1 + 2 + 1 = 2 * j + 4 := by ring
      rw [h1, h2]; exact trans_odd j

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 1, 0, n, 0⟩) 0
  intro n
  exact ⟨n+1, main_trans n⟩

end Sz22_2003_unofficial_198
