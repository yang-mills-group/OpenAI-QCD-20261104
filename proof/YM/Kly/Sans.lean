import YM.Kly.Zone
import YM.Kly.Mark
import YM.MassiveBridge.Mantle
set_option autoImplicit false
set_option maxHeartbeats 610000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis
open OS (Cross)
open Fields (pointMoment distinct)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder
open MassiveTwoEstimates Spinor Spinor.Lift
variable {F:Fields} {S:F.Kernel}{V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){X:Bases F}{M':Momentum F}(U:X.Content C M')
local notation "a"=> timeAxis
variable (i: SpaceAxis)
abbrev budG(x:Pack F): V.D:= (M₀ P x).val V.omega0
open Chamber
lemma port {n k:ℕ} [FiniteDimensional ℂ (F.level k)] (u:CapIn F n k)(hu:Positive (parcels u) a):∀ᶠ y in 𝓝 u, Positive (parcels y) a:=by
      have ht:u.1∈ conf n:= (realized ..).1 hu.1; have he:∀ i: Fin n, 0< u.1 i a:=by intro i; exact hu.2 (u.1 i,(u.2 i).val) (by change _ ∈ List.ofFn _; rw[List.mem_ofFn]; exact ⟨_,rfl⟩)
      have h(i:Fin n):∀ᶠ y:CapIn F n k in 𝓝 u,0 < y.1 i a:=by
           refine ((show Continuous (fun y: Points n × (Fin n → F.level k)=> y.1.ofLp i |>.ofLp a) by fun_prop).continuousAt.tendsto).eventually ?_; exact lt_mem_nhds (he _)
      filter_upwards [continuous_fst.continuousAt.eventually ((conf_open _).eventually_mem ht),eventually_all.mpr h] with y h k; refine ⟨(realized ..).2 h,?_⟩; intro x hx; change _∈ List.ofFn _ at hx; obtain ⟨i,rfl⟩:= List.mem_ofFn.mp hx; exact k i
include E Y H R
open Spinor
lemma hale (x:Pack F) : Continuous (fun t:ℝ=>budG P (orbit R (Spinor.Lift.daylight i t) x)):=by
      let l:=x.val; let n:=l.length; obtain ⟨d,u,ht⟩:= Rotate.cover_cap E (tokens l); let w(t:ℝ):Fin n→F.level d:=fun j=> ⟨_, E.lift (u j).val (u j).property (Spinor.Lift.daylight i t)⟩
      have hh:l=realize (tokens l) (positions l):=(List.ofFn_get l).symm; let p(t:ℝ):Points n:= Points.move (Spinor.Lift.daylight i t).coord (positions l); have he(t:ℝ)(s:E4): carry (orbit R (Spinor.Lift.daylight i t) x).val s= parcels (F:=F) (Points.across s (p t),w t):=by
           change carry (rotate l _) s=_; unfold carry rotate; nth_rw 1[hh]; rw [ht]; simp only [realize,List.map_ofFn]; rfl
      haveI:= E.finite d
      have h(t:ℝ):Positive (carry (orbit R (Spinor.Lift.daylight i t) x).val 0) a ∨ True:= Or.inr trivial -- clean
      refine continuous_iff_continuousAt.mpr (fun t=>?_); obtain ⟨b,m,h⟩:=Spread.place_exists (orbit R (Spinor.Lift.daylight i t) x).property; let z(t:ℝ):CapIn F n d:=(Points.across b (p t),w t); let y:Future F a:=⟨_,h.2.1⟩; have hr:Positive (parcels (z t)) a:= he t b ▸ h.2.1
      have hz:Continuous z:=by
           apply Continuous.prodMk
           · apply (PiLp.homeomorph 2 _).symm.continuous.comp (f:=fun t:ℝ=>(Points.across b (p t)).ofLp); refine continuous_pi fun j=>?_ ; unfold p; change Continuous (fun s:ℝ=> Ortho.move _ _ + _); -- use continuous
             change Continuous (fun t:ℝ=>Ortho.move (Spinor.Lift.daylight i t).coord (positions l j)+b); simp_rw [(way i).2.2]; exact Continuous.add (continuous_iff_continuousAt.mpr fun t=>(Work.A13.hasDerivAt_move _ _ t).continuousAt) continuous_const
           exact continuous_pi fun j=> Continuous.subtype_mk ((E.properActs (u j).val).comp (way i).2.1) _
      have hv: Tendsto z (𝓝 t) (𝓝 (z t)):= hz.continuousAt; let W(r:ℝ):CapZone n d a F:= by classical exact if h:Positive (parcels (z r)) a then ⟨z r,h⟩ else ⟨_,hr⟩
      have hm(r:ℝ)(h: Positive (parcels (z r)) a):(W r).val=z r:=by classical unfold W; rw[dif_pos h]
      have hh: ∀ᶠ s in 𝓝 t, Positive (parcels (z s)) a:= hv.eventually (port (z t) hr); have hT:Tendsto W (𝓝 t) (𝓝 (W t)):= tendsto_subtype_rng.mpr (by rw [hm t hr]; exact hv.congr' (hh.mono fun r h=> (hm r h).symm))
      have hb(r:ℝ)(h:Positive (parcels (z r)) a): V.D.orthogonalProjectionOnto (V.sample n d (W r))=budG P (orbit R (Spinor.Lift.daylight i r) x):=by
           rw[Chamber.sample, ←almost P H]; apply congr_arg (fun i:P.algebra=>i.val V.omega0); symm; apply (travelled P H Y (E.reflected _) _ (orbit R (Spinor.Lift.daylight i r) x).property b).trans; congr 1; rw [he]; exact congr_arg _ (hm r h).symm
      change Tendsto _ _ (𝓝 (budG P (orbit R (Spinor.Lift.daylight i t) x))); rw [←hb t hr]; exact (V.D.orthogonalProjectionOnto.continuous.continuousAt.tendsto.comp ((V.sample_cont Y).continuousAt.tendsto.comp hT)).congr' (hh.mono fun r h=>hb r h)
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.hale
