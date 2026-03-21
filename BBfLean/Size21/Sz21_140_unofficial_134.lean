import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #134: [9/35, 1/33, 50/3, 11/5, 245/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  0  0 -1
 1 -1  2  0  0
 0  0 -1  0  1
-1  0  1  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_134

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+2, e⟩
  | _ => none

-- R4 chain: c → e
theorem r4_chain : ∀ k, ∀ a e, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  step fm
  apply stepStar_trans (ih a (e + 1))
  ring_nf; finish

-- R3 chain: b → a,c
theorem r3_chain : ∀ k, ∀ a c, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a+k, 0, c+2*k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  step fm
  apply stepStar_trans (ih (a + 1) (c + 2))
  ring_nf; finish

-- E drain: (A+1, 0, 0, D, E+2) → (A, 0, 0, D+1, E) per round
theorem e_drain : ∀ k, ∀ a d e, ⟨a+k, 0, 0, d, e+2*k⟩ [fm]⊢* ⟨a, 0, 0, d+k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
  step fm; step fm
  rw [show e + 2 * k + 1 = (e + 2 * k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih a (d + 1) e)
  ring_nf; finish

-- E=1 end: (a+1, 0, 0, d+1, 1) →* (a+1, 4, 0, d, 0)
theorem e1_end : ∀ a d, ⟨a+1, 0, 0, d+1, 1⟩ [fm]⊢* ⟨a+1, 4, 0, d, 0⟩ := by
  intro a d
  rw [show (a + 1 : ℕ) = a + 1 from rfl]
  show ⟨a + 1, 0, 0, d + 1, 1⟩ [fm]⊢* ⟨a + 1, 4, 0, d, 0⟩
  rw [show d + 1 = d + 1 from rfl]
  step fm
  rw [show d + 3 = (d + 2) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm
  step fm
  finish

-- D drain: k rounds of 3 steps each
theorem d_drain : ∀ k, ∀ a b d, ⟨a, b+1, 0, d+2*k, 0⟩ [fm]⊢* ⟨a+k, b+1+3*k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 1 + 1 from by ring]
  step fm
  rw [show d + 2 * k + 1 + 1 = (d + 2 * k + 1) + 1 from by ring]
  step fm
  rw [show d + 2 * k + 1 = (d + 2 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (a + 1) (b + 3) d)
  ring_nf; finish

-- D=1 end + R3 chain
theorem d1_end : ∀ a b, ⟨a, b+1, 0, 1, 0⟩ [fm]⊢* ⟨a+b+3, 0, 2*b+5, 0, 0⟩ := by
  intro a b
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (r3_chain (b + 2) (a + 1) 1)
  ring_nf; finish

-- E=0 start: (a+1, 0, 0, d, 0) → (a, 2, 0, d+1, 0)
theorem e0_start : ∀ a d, ⟨a+1, 0, 0, d, 0⟩ [fm]⊢* ⟨a, 2, 0, d+1, 0⟩ := by
  intro a d
  step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm
  finish

-- Full ABD: by induction on D
theorem abd : ∀ D, ∀ a b, ⟨a, b+1, 0, D, 0⟩ [fm]⊢* ⟨a+b+1+2*D, 0, 2*b+2+3*D, 0, 0⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro a b
  match D with
  | 0 =>
    apply stepStar_trans (r3_chain (b + 1) a 0)
    ring_nf; finish
  | 1 =>
    refine stepStar_trans (d1_end a b) ?_; ring_nf; finish
  | D' + 2 =>
    rw [show D' + 2 = D' + 2 * 1 from by ring]
    apply stepStar_trans (d_drain 1 a b D')
    rw [show b + 1 + 3 * 1 = (b + 3) + 1 from by ring]
    refine stepStar_trans (ih D' (by omega) (a + 1) (b + 3)) ?_
    ring_nf; finish

-- Even c transition
theorem trans_even (K : ℕ) (hK : K ≥ 1) (a : ℕ) (ha : a ≥ K + 1) :
    ⟨a, 0, 2*K, 0, 0⟩ [fm]⊢⁺ ⟨a+K+3, 0, 3*K+7, 0, 0⟩ := by
  obtain ⟨A, rfl⟩ : ∃ A, a = A + (K + 1) := ⟨a - (K + 1), by omega⟩
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨A + (K + 1), 0, 0, 0, 2*K⟩)
  · refine stepStar_trans (r4_chain (2*K) (A + (K + 1)) 0) ?_; ring_nf; finish
  apply step_stepStar_stepPlus (c₂ := ⟨A + K, 0, 1, 2, 2*K⟩)
  · show fm ⟨(A + K) + 1, 0, 0, 0, 2 * K⟩ = some ⟨A + K, 0, 1, 2, 2 * K⟩; simp [fm]
  step fm
  rw [show (2 * K) = (2 * K - 2) + 1 + 1 from by omega]
  step fm; step fm
  rw [show A + K = A + 1 + (K - 1) from by omega,
      show 2 * K - 2 = 0 + 2 * (K - 1) from by omega]
  apply stepStar_trans (e_drain (K - 1) (A + 1) 1 0)
  rw [show 1 + (K - 1) = K from by omega]
  apply stepStar_trans (e0_start A K)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  refine stepStar_trans (abd (K + 1) A 1) ?_
  ring_nf; finish

-- Odd c transition
theorem trans_odd (K : ℕ) (hK : K ≥ 1) (a : ℕ) (ha : a ≥ K + 1) :
    ⟨a, 0, 2*K+1, 0, 0⟩ [fm]⊢⁺ ⟨a+K+2, 0, 3*K+5, 0, 0⟩ := by
  obtain ⟨A, rfl⟩ : ∃ A, a = A + (K + 1) := ⟨a - (K + 1), by omega⟩
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨A + (K + 1), 0, 0, 0, 2*K+1⟩)
  · refine stepStar_trans (r4_chain (2*K+1) (A + (K + 1)) 0) ?_; ring_nf; finish
  apply step_stepStar_stepPlus (c₂ := ⟨A + K, 0, 1, 2, 2*K+1⟩)
  · show fm ⟨(A + K) + 1, 0, 0, 0, 2 * K + 1⟩ = some ⟨A + K, 0, 1, 2, 2 * K + 1⟩; simp [fm]
  step fm
  rw [show 2 * K + 1 = (2 * K - 1) + 1 + 1 from by omega]
  step fm; step fm
  rw [show A + K = A + 1 + (K - 1) from by omega,
      show 2 * K - 1 = 1 + 2 * (K - 1) from by omega]
  apply stepStar_trans (e_drain (K - 1) (A + 1) 1 1)
  rw [show 1 + (K - 1) = K from by omega]
  rw [show K = (K - 1) + 1 from by omega]
  apply stepStar_trans (e1_end A (K - 1))
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  refine stepStar_trans (abd (K - 1) (A + 1) 3) ?_
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  ring_nf; finish

-- Main transition
theorem main_trans (a c : ℕ) (h1 : 2 * a ≥ c + 1) (h2 : c ≥ 2) :
    ∃ a' c', (⟨a, 0, c, 0, 0⟩ : Q) [fm]⊢⁺ ⟨a', 0, c', 0, 0⟩ ∧ 2 * a' ≥ c' + 1 ∧ c' ≥ 2 := by
  rcases Nat.even_or_odd c with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK; subst hK
    have hK1 : K ≥ 1 := by omega
    have ha : a ≥ K + 1 := by omega
    exact ⟨a + K + 3, 3 * K + 7, trans_even K hK1 a ha, by omega, by omega⟩
  · subst hK
    have hK1 : K ≥ 1 := by omega
    have ha : a ≥ K + 1 := by omega
    exact ⟨a + K + 2, 3 * K + 5, trans_odd K hK1 a ha, by omega, by omega⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 7, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a, 0, c, 0, 0⟩ ∧ 2 * a ≥ c + 1 ∧ c ≥ 2)
  · intro q ⟨a, c, hq, h1, h2⟩
    subst hq
    obtain ⟨a', c', htrans, h1', h2'⟩ := main_trans a c h1 h2
    exact ⟨⟨a', 0, c', 0, 0⟩, ⟨a', c', rfl, h1', h2'⟩, htrans⟩
  · exact ⟨4, 7, rfl, by omega, by omega⟩

end Sz21_140_unofficial_134
