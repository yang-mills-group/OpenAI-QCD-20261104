import YM.Lust.Pith
import YM.Dart.Latex
/-!
  Chassis for the spacetime hierarchy.
  In particular the smoothness and inclusion prices below
  refer to genuine forward unit differences on ONE volume and all other placements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P: Calibration C)
open GaugeP
structure Cottage (d:ℕ) where
    (E:Hub.Invest P d)
    (H:Rack E)
    (m:Laurel d)
    (J:Landing P.sym m)
    (K:GaugeP P m J)
    (G:∀ e:ℝ,0 < e→Nonempty (Capital P d e))
    u : Wealthy H
    b : Spring P d
    beam (u:Averaging) : Nonempty (LensZ P m J u)
    ink (D:ℕ)(h:D≤d)(v:Label D):∃ p:ℕ→Label d, Arc H (fun i=>stem P D i v) p
    eye (D:ℕ)(h:D+2≤d)(v:Label D)(b:Axis):∃ p:ℕ→Label d, Arc H (fun i=>lDer C i b (stem P D i v)) p
namespace Cottage
variable {P}{d:ℕ}(G: Cottage P d)
noncomputable def plate (u:Averaging)(i:ℕ):Label d→L[ℂ](Stokes d→ℂ):=LinearMap.toContinuousLinearMap (G.K.glean (E:=G.E) u i)
noncomputable def rise :Capital P d 1:= Classical.choice (G.G 1 zero_lt_one)
variable {β ν:ℝ}(hp:C.Path β ν)(hr:Sway C.S)
include hp hr
-- useful projection persistence-frame prices.Chassis. 
lemma heights (u:Averaging):∃ B:ℝ,0 ≤ B ∧ ∀ᶠ i:ℕ in atTop,‖G.plate u i‖≤B:=by
    obtain ⟨T,h,H1,h2,h⟩:= G.K.attests hp G.rise G.H hr G.u G.b u; refine ⟨T,H1,h.mono ?_⟩; exact fun i hi=>(G.plate u i).opNorm_le_bound H1 fun x=> (hi x).1
lemma pointsP (u:Averaging)(z:ℕ→Label d)(hc:∃ C:ℝ,0 ≤ C∧∀ᶠ i:ℕ in atTop,‖z i‖ ≤ C):LightP C (fun i=> stemV P d i u (z i)) ∧ DimP C (fun i=> stemV P d i u (z i)-stem P d i (G.K.ridge i ((G.plate u i) (z i)))):=by obtain ⟨V,hv,h⟩:=hc; exact G.K.edges G.u G.b G.rise hp hr u z V hv h -- sig
-- surjectivity limit.AOT check.M.Runs
omit hp hr in
set_option maxHeartbeats 490000 in
private lemma mouths {A B:Type*}[NormedAddCommGroup A][NormedSpace ℂ A][FiniteDimensional ℂ A][NormedAddCommGroup B][NormedSpace ℂ B][FiniteDimensional ℂ B] (plate:ℕ→ A →L[ℂ] B) (φ:ℕ→ℕ)(X:A →L[ℂ] B)(hx:Tendsto (fun i=>plate (φ i)) atTop (𝓝 X))(hv:Tendsto φ atTop atTop)(Q:ℕ→B→L[ℂ]A)(Y V:ℝ)(hh:∀ᶠ i in atTop,Q i∈Metric.closedBall 0 Y)(h1:∀ᶠ i in atTop,∀ v:B, ‖v‖ ≤ V * ‖plate i (Q i v)‖): Surjective X :=by
    -- further subseq, finite dimension. choose right inverse limit. 
    have hm:= hv.eventually hh; obtain ⟨j,hj⟩:=eventually_atTop.mp hm; let f(n):= φ (j+n); have hp': Tendsto (fun i:ℕ=>j+i) atTop atTop:= tendsto_atTop_mono (fun i=>Nat.le_add_left i j) tendsto_id
    obtain ⟨F,hM,g,hg,hF⟩:= (isCompact_closedBall _ _).tendsto_subseq (fun i=> show Q (f i) ∈ Metric.closedBall 0 Y from hj _ (Nat.le_add_right ..)); let h(i:ℕ):=f (g i)
    have ht:= hp'.comp hg.tendsto_atTop; have hu:Tendsto (fun i:ℕ=>plate (h i)) atTop (𝓝 X):=hx.comp ht
    let M:= X.toLinearMap.comp F.toLinearMap
    have hQ(v:B): ‖v‖ ≤ V * ‖M v‖:=by
         let L : ((A→L[ℂ] B) × (B→L[ℂ]A))→ℝ:=fun x=> ‖x.1 (x.2 v)‖; have hd: Continuous L:=by unfold L; fun_prop
         have hI:Tendsto (fun i=> ‖plate (h i) (Q (h i) v)‖) atTop (𝓝 ‖M v‖):=(hd.tendsto (X,F)).comp (hu.prodMk_nhds (show Tendsto (fun i=> Q (h i)) atTop (𝓝 F) from hF))
         exact le_of_tendsto_of_tendsto tendsto_const_nhds (hI.const_mul V) (((hv.comp ht).eventually h1).mono (fun i hi=> hi v)) -- need eventual
    have hz(x:B)(hx:M x=0): x=0:=norm_le_zero_iff.mp (by simpa only [hx,norm_zero,mul_zero] using hQ x)
    have hP : Injective M:= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hz); intro x; obtain ⟨y,rfl⟩:= (LinearMap.injective_iff_surjective.mp hP) x; exact ⟨F y,rfl⟩
lemma roles (u:Averaging)(φ:ℕ→ℕ)(hv: Tendsto φ atTop atTop)(X:Label d→L[ℂ](Stokes d→ℂ))(hx:Tendsto (fun i=>G.plate u (φ i)) atTop (𝓝 X)) : Surjective X:=by
    obtain ⟨L⟩:=G.beam u; obtain ⟨V,hV,h1⟩:= LensZ.checksW G.u G.b G.rise G.K hp hr L
    obtain ⟨Y,hy,h2⟩:= LensZ.pricingW L
    let Q(i):=((LensZ.spur L i).toContinuousLinearMap); have hh:∀ᶠ i:ℕ in atTop,Q i∈Metric.closedBall 0 Y:= h2.mono fun i hi=>by simp only [Metric.mem_closedBall,dist_zero_right]; exact (Q i).opNorm_le_bound hy hi
    exact mouths (G.plate u) φ X hx hv Q Y V hh h1
end Cottage
end YM.Massive.Needle
#print axioms YM.Massive.Needle.Cottage.roles
