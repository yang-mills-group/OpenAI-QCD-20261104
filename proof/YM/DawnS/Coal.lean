import YM.DawnS.Trop
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix
abbrev PR:= ℝ×↥RingS
local notation "P"=> RingS
noncomputable abbrev wa : Measure PR := ((volume:Measure ℝ).restrict (Set.Ioi 0)).prod muS
noncomputable def priceK (r:ℝ)(x:ℝ):ℝ:=Real.exp (-x)*x^2*(normal/(sky*r^3))
lemma burning (s:ℕ): Integrable (fun x:ℝ=> Real.exp (-x)*x^s) (volume.restrict (Ioi 0)) ∧ ∫ x:ℝ in Ioi 0, Real.exp (-x)*x^s=(s.factorial:ℝ):=by
    let v:ℝ:=s+1; have hv:0<v:=by unfold v; positivity
    have he(x:ℝ): x^(v-1)=x^s:=by rw [show v-1=(s:ℝ) by unfold v; ring, Real.rpow_natCast]
    simp_rw[← he]; exact ⟨Real.GammaIntegral_convergent hv,(Real.Gamma_eq_integral hv).symm.trans (Real.Gamma_nat_eq_factorial s)⟩
variable (r:ℝ) (hr:0<r)
lemma prices_pos (x:ℝ)(hx:0<x) (hr:0<r): 0< priceK r x:=by unfold priceK; have h:0<normal:=(by unfold normal; positivity); have hg:=sky_pos; positivity
lemma burningR (n:ℕ): Integrable (fun x:ℝ=> priceK r x * (x/r)^n) (volume.restrict (Ioi 0)) ∧ ∫ x:ℝ in Ioi 0, priceK r x*(x/r)^n=rayG r (n+1):=by
     let s:=n+2; let K:= normal/(sky*r^3)/r^n; let f(x:ℝ):=Real.exp (-x)*x^s
     rw[show (fun x:ℝ=>priceK r x*(x/r)^n)=fun x=>f x*K from funext fun x=>by unfold f s K priceK; rw [div_pow]; ring]; obtain ⟨hv,h⟩:=burning s; refine ⟨(Integrable.mul_const hv K),?_⟩; rw[integral_mul_const,h]; unfold K rayG s; ring -- inv pow? 
-- WHEN integrating `priceK` included in kernel.M sign real and t.The.
lemma tallyCup (n:ℕ) (g:P→ℂ)(h: Continuous g): Integrable (fun p:PR=> ((↑(priceK r p.1):ℂ)* ((↑(p.1/r):ℂ)^n))*g p.2) wa ∧ (∫ p:PR, (((priceK r p.1:ℝ):ℂ)* ((↑(p.1/r):ℂ)^n))*g p.2 ∂wa)=(rayG r (n+1):ℂ)*(∫ p:P,g p ∂muS):=by
     let f(x:ℝ):= priceK r x*(x/r)^n
     rw [show (fun p:PR=>((↑(priceK r p.1):ℂ)*(↑(p.1/r):ℂ)^n)*g p.2)=(fun p: PR=> (f p.1:ℂ)*g p.2) from (by unfold f; push_cast; rfl)]
     obtain ⟨hF,hT⟩:= burningR r n; refine ⟨(hF.ofReal.mul_prod (h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))),?_⟩
     rw[wa,integral_prod_mul (fun x=>↑(f x)) g, show (∫ x:ℝ in Ioi 0,(↑(f x):ℂ))=_ from integral_ofReal .. ]; exact congr_arg (fun a:ℝ=>(a:ℂ)*_) hT
end YM.DawnS
