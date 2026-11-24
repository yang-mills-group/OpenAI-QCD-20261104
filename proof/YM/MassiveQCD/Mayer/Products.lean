import YM.MassiveQCD.Palette.Lamp
import YM.MassiveQCD.Mayer.Analytic
/-! # Ordered derivatives budget outward
 `Sen` is the actual weighted Bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew.Phased
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.Frobenius
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint
variable {c:Side}{N:ℕ}{o:Site c}{B:Support c} {t p q a s r:ℝ} {k n:ℕ}
local notation "Z"=>EvenA c N
local notation "Q"=>Sen (N:=N) o t
lemma submult (ht:0≤t)(x y:Z): Q (x*y) ≤ Q x * Q y:=roams (lens o) ht .. -- sig
lemma sentry_add (x y:Z): Q (x+y)≤Q x+Q y:= Brick.vested ..
open Next.Foundations
set_option maxHeartbeats 520000 in
theorem left_mul_tax {D : Directions su c → Prop} {f g : Config su c → Z} {k : ℕ} {U : Config su c}
    {a b : ℝ} (ht:0≤t) (hf : Push.Local.Chart k f U) (hg : Chart k g U)
    (hc : ∀ l : List (Directions su c), l.length ≤ k → (∀ v∈l, D v) → Q (leftDerivs f l U) ≤ a)
    (hc' : ∀ l : List (Directions su c), l.length ≤ k → (∀ v∈l, D v) → Q (leftDerivs g l U) ≤ b) :
    ∀ l : List (Directions su c), l.length ≤ k → (∀ v∈l, D v) → Q (leftDerivs (f*g) l U) ≤ 2^l.length * (a*b) := by
  intro l hl hD
  induction l using List.reverseRecOn generalizing f g k with
  | nil => simpa [leftDerivs] using (submult ht (f U) (g U)).trans (mul_le_mul
      (hc [] hl hD) (hc' [] hl hD) (show _≤Q (g U) from norm_nonneg _) ((norm_nonneg _).trans (hc [] hl hD)))
  | append_singleton l A ih =>
    have he : l.length+1 ≤ k := by simpa using hl
    have H (w : Config su c → Z) (hw : Chart k w U) : Chart l.length (leftDerivs w [A]) U :=
      leftDerivs_chart _ l.length (hw.of_le (Nat.cast_le.mpr (Nat.add_comm .. ▸ he)))
    have hN (w : Config su c → Z) (τ : ℝ) (hw : ∀ l : List (Directions su c), l.length ≤ k → (∀ v∈l, D v) → Q (leftDerivs w l U) ≤ τ)
        (l' : List (Directions su c)) (hl' : l'.length ≤ l.length) (he' : ∀ v∈l', D v) :
        Q (leftDerivs (leftDerivs w [A]) l' U) ≤ τ := by
      rw [← Work.G07.left_append]; refine hw _ (by simp; omega) ?_
      intro v hv; rcases List.mem_append.mp hv with h|h
      · exact he' _ h
      · exact hD _ (List.mem_append_right _ h)
    have ht : leftDerivs (f*g) [A] ∘ increment U =ᶠ[𝓝 0]
        (leftDerivs f [A]*g + f*leftDerivs g [A]) ∘ increment U := by
      have hk : (1:ℕ) ≤ k := by omega
      have h' (w : Config su c → Z) (hw : Chart k w U) : ∀ᶠ x in 𝓝 0, Chart 1 w (increment U x) :=
        chart_eventually (by rw [Work.G07.at_zero_increment]; exact hw.of_le (Nat.cast_le.mpr hk))
          fun i => by
            simp only [increment,su.mat_mul]; exact ((su.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt
      filter_upwards [h' f hf,h' g hg] with t ht ht'; exact left_first_mul A ht ht'
    rw [Work.G07.left_append,left_congr l U ht]
    have hle : l.length ≤ k := by omega
    have hsf := hf.of_le (Nat.cast_le.mpr hle)
    have hsg := hg.of_le (Nat.cast_le.mpr hle)
    have hd : ∀ v∈l, D v := fun v hv => hD v (by simp [hv])
    rw [left_add l ((H f hf).mul hsg) (hsf.mul (H g hg)) (le_refl l.length)]
    apply (sentry_add ..).trans
    exact (add_le_add
      (ih (k:=l.length) (H _ hf) hsg (hN _ a hc) (fun i hi => hc' i (hi.trans hle)) le_rfl hd)
      (ih (k:=l.length) hsf (H _ hg) (fun i hi => hc i (hi.trans hle)) (hN _ b hc') le_rfl hd)).trans_eq (by simp; ring)
end YM.QCD.Stew.Phased
#print axioms YM.QCD.Stew.Phased.left_mul_tax
