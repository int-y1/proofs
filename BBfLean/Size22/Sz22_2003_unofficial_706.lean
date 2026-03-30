import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #706: [35/6, 4/55, 121/2, 3/7, 35/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_706

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem middle : ∀ n, ∀ c d F, ⟨0, n, c + 1, d, F + n + c + 1⟩ [fm]⊢* ⟨n + 2 * c + 2, 0, 0, d + n, F⟩ := by
  intro n; induction' n using Nat.strongRecOn with n ih
  rcases n with _ | _ | n
  · -- n = 0
    intro c d F
    have h := r2_chain (c + 1) 0 0 d F
    convert h using 2
    all_goals ring_nf
  · -- n = 1
    intro c d F
    rw [show F + 1 + c + 1 = (F + c + 1) + 1 from by ring]
    step fm
    step fm
    have h := r2_chain (c + 1) 1 0 (d + 1) F
    convert h using 2
    all_goals ring_nf
  · -- n + 2
    intro c d F
    rw [show F + (n + 2) + c + 1 = (F + n + c + 1 + 1) + 1 from by ring]
    step fm
    rw [show n + 2 = (n + 1) + 1 from by ring]
    step fm
    rw [show n + 1 = n + 1 from rfl]
    step fm
    have key := ih n (by omega) (c + 1) (d + 2) F
    have key2 : ⟨0, n, c + 2, d + 2, F + n + c + 2⟩ [fm]⊢* ⟨n + 2 * c + 4, 0, 0, d + 2 + n, F⟩ := by
      convert key using 2
    apply stepStar_trans key2
    ring_nf; finish

theorem r5_step (n e : ℕ) : ⟨0, n, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨0, n, 1, 1, e⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, n, 0, 0, e + 1⟩ = some ⟨0, n, 1, 1, e⟩
    rcases n with _ | n <;> simp [fm]
  finish

theorem main_trans (n t : ℕ) : ⟨n + 1, 0, 0, n, t⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, n + 1, t + n⟩ := by
  have h1 := r3_chain (n + 1) 0 n t
  have h1' : ⟨n + 1, 0, 0, n, t⟩ [fm]⊢* ⟨0, 0, 0, n, t + 2 * n + 2⟩ := by
    convert h1 using 2
    all_goals ring_nf
  have h2 := r4_chain n 0 0 (t + 2 * n + 2)
  have h2' : ⟨0, 0, 0, n, t + 2 * n + 2⟩ [fm]⊢* ⟨0, n, 0, 0, t + 2 * n + 2⟩ := by
    convert h2 using 2
    all_goals ring_nf
  have h5 : ⟨0, n, 0, 0, t + 2 * n + 2⟩ [fm]⊢⁺ ⟨0, n, 1, 1, t + 2 * n + 1⟩ := by
    rw [show t + 2 * n + 2 = (t + 2 * n + 1) + 1 from by ring]
    exact r5_step n (t + 2 * n + 1)
  have hmid := middle n 0 1 (t + n)
  have hmid' : ⟨0, n, 1, 1, t + 2 * n + 1⟩ [fm]⊢* ⟨n + 2, 0, 0, n + 1, t + n⟩ := by
    convert hmid using 2
    all_goals ring_nf
  exact stepStar_stepPlus_stepPlus (stepStar_trans h1' h2') (stepPlus_stepStar_stepPlus h5 hmid')

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, t⟩ ↦ ⟨n + 1, 0, 0, n, t⟩) ⟨1, 0⟩
  intro ⟨n, t⟩; exact ⟨⟨n + 1, t + n⟩, main_trans n t⟩

end Sz22_2003_unofficial_706
