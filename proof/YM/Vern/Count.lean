import YM.Vern.Clique
set_option autoImplicit false
set_option maxHeartbeats 910000
noncomputable section
namespace YM.Vern
open Function Set Filter Analysis MeasureTheory Lattice QCD QCD.Lat
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix InnerProductSpace
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp Heron Iceberg Lobo
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K}{d:ℕ}
variable {φ:ℕ→ℕ}(hP:P.System)(hf:Foil P K T)(HQ:K.Harmony P φ)(E:Canopy P φ K)(X:Lanterns T E)
variable (V:Axis× Axis→ K.W)(hV: Persona T V)(J:Axle K (fun a b=>V (a,b))) (B:Vane J)
variable (r:ℝ)(hr:0<r)(s:ℝ)(z:IceT→ℝ)
variable (hD:(swingE K 1).range=(bits K).range)(hχ:∀ d, ∃ n:Lattice.Side, Injective (P.candidate d n 0))
set_option quotPrecheck false
local notation "Rt"=>peakΩ V hV.tense E X
lemma sees (g:Ortho.Skew)(f:ℕ→ℕ)(L:Module.End ℂ (Free.Symbol d))(ht:8≤ d)(h:Tendsto ((peakΩ V hV.tense E X)∘ f) atTop (𝓝 r))(hr:0<r) (x:Free.Symbol d)(hΩ:Tendsto (fun i:ℕ=> foldQ V E X hV J ht g (f i) x) atTop (𝓝 (L x))) :Tendsto (fun i:ℕ=>steel V E X J ht g (f i) x) atTop (𝓝 ((r:ℂ) • L x)):=by
     apply (((Complex.continuous_ofReal.continuousAt.tendsto).comp h).smul hΩ).congr'; refine Eventually.of_forall fun i=>?_ ; change (↑(peakΩ V hV.tense E X (f i)):ℂ) • ((↑(peakΩ V hV.tense E X (f i))⁻¹:ℂ) • steel V E X J ht g (f i) x) = _; push_cast; rw [smul_inv_smul₀ (by exact_mod_cast (viable V E X _ hV).ne')]
variable (f:ℕ→ℕ)(hF:Tendsto f atTop atTop)(s':Hail.RightAuth P.sym)
variable (h:∀ d:ℕ,∀ x:Free.Symbol d,∀ h:8 ≤ d,∀ k:Tri,Tendsto (fun i=> ((r⁻¹:ℝ):ℂ) • steel V E X J h (Omega k) (f i) x) atTop (𝓝 (omegaQ k z d x)))
include hV hP hf HQ hD hχ B hF h s'
lemma grist (p:Flavor 6): z none=z (some p) :=by
     by_contra ht
     obtain ⟨k,F,Z,hk,h0,hL,hB⟩:= align hf HQ E X V hV J B r⁻¹ (fun i=>omegaQ i z 10) f hF (by decide) (fun x=>h 10 x (by decide))
     obtain ⟨f',W,L,hg,h',hA,hS⟩:= align hf HQ E X V hV J B r⁻¹ (fun i=>omegaQ i z 8) (f ∘ k) (hF.comp hk.tendsto_atTop) (by decide) (fun x i=> (h 8 x (by decide) i).comp hk.tendsto_atTop)
     let C := Gcup hf HQ E X 10
     let C':= C.zz (Mango p 1 2); have hh (i:ℕ):Feasible hf HQ E X V hV J (d:=10) (by decide) r⁻¹ z Z (F i):=⟨hL,fun k u=>⟨(hB u k i).1,(hB u k i).2.1⟩⟩
     have hz(i:ℕ):Feasible hf HQ E X V hV J (d:=8) (by decide) r⁻¹ z L (W i):=⟨hA,fun k u=>⟨(hS u k i).1,(hS u k i).2.1⟩⟩
     let A(x:ℕ):= simV E X (f x) 10; let τ(i:ℕ):= (F i).symm ((A (k i)) (Starx p)); have htC: Tendsto (C' ∘ τ) atTop (𝓝 (C' (Starx p))):= C'.continuous_of_finiteDimensional.continuousAt.tendsto.comp (h0 _)
     have he(k:ℕ)(x: ↥(seatP 10)):C' x= _:= Eq.symm ((hB (Mango p 1 2) 0 k).2.2 x); have hx:C' (Starx p)≠0:=by rw [he 0]; exact forge_bar hf HQ E X V hV J B _ (E.B _).realH r⁻¹ z Z (F 0) (hh _) s' p ht
     apply hx; apply tendsto_nhds_unique (htC.comp hg.tendsto_atTop); apply tendsto_const_nhds.congr'; refine Eventually.of_forall fun i=>?_ ; change 0=C' _; rw [he (f' i)]; symm; dsimp only [τ, Function.comp_apply]; rw [LinearEquiv.apply_symm_apply]; exact priced hf HQ E X V hV J B _ (E.B _).realH _ z L Z _ _ (hz i) (hh (f' i)) s' p ht hP hD hχ _ -- check order
end YM.Vern
#print axioms YM.Vern.grist
#print axioms YM.Vern.sees
