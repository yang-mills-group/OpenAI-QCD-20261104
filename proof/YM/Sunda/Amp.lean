import YM.Sunda.Finch
set_option maxHeartbeats 540000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open Massive.Patria.Gall Massive.Patria.Gall.Onyx Massive.Tarn.ChargeQ
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis× Axis→ K.W}{A:Axle K (fun a b=>W (a,b))}{φ:ℕ→ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{I:ℕ→ℕ}(J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)
variable {ρ:EuPin→* (K.W≃ₗ[ℂ]K.W)}(S:Steps (A:=A) T R ρ)
set_option quotPrecheck false
local notation "X0"=> equip T ρ A.jet
open Sunda Lobo
local notation "Ω"=> Free.Symbol
-- generic uniform linear estimates
lemma cables {V Y:Type}[NormedAddCommGroup Y][NormedSpace ℂ Y](u:ℕ→V→Y)(w: V→Y)(T:ℕ→ℂ)(z:ℂ)(L:Set V)(h:Tendsto T atTop (𝓝 z))(he:∀ e:ℝ,0<e→∀ᶠ i in atTop,∀ y∈L,‖u i y-w y‖ ≤ e)(hp:∃ B:ℝ,0≤B∧∀ y∈L,‖w y‖≤B)(ε:ℝ)(hv:0<ε):∀ᶠ i in atTop,∀ y∈L,‖T i • u i y-z • w y‖ ≤ ε:=by
      obtain ⟨B,hB,h₁⟩:= hp; let b:= ε/2; let r:= b/(B+1); let W:= ‖z‖+1; have hr :0<r:=by unfold r b; positivity
      have hw:0<W:=by unfold W; positivity
      filter_upwards [h.norm.eventually_le_const (lt_add_one _), (Metric.tendsto_nhds.mp h r hr), he (b/W) (div_pos (half_pos hv) hw)] with i hi ht hh y hy; rw[dist_eq_norm] at ht
      calc _ = ‖T i • (u i y-w y)+(T i-z) • w y‖:=by rw [smul_sub,sub_smul]; congr 1; abel
           _ ≤ _:= norm_add_le ..
           _ ≤ W*(b/W)+r*B:= add_le_add (by rw [norm_smul]; exact mul_le_mul hi (hh _ hy) (norm_nonneg _) hw.le) (by rw[norm_smul]; exact mul_le_mul ht.le (h₁ y hy) (norm_nonneg _) hr.le)
           _ ≤ b+b:=by refine add_le_add (le_of_eq ?_) (le_trans (mul_le_mul_of_nonneg_left (le_of_lt (lt_add_one _)) hr.le) (le_of_eq ?_)); unfold W b; field_simp; unfold r; field_simp
           _ = _:= add_halves _
variable {n:ℕ}(d: Fin n →ℕ)(Z: Canopy.KForm K)(ht:Canopy.Groom K Z)(hv:Canopy.Money E Z)(hw: Canopy.Troupe E Z)
open Canopy
include J JQ R hv ht hw
variable (F:∀ d:ℕ,ℕ→ Ω d ≃ₗ[ℂ] ↥(K.level d))(hG:Glace A I X R ρ F)
include hG
local notation "Δ"=> hops T A E I ρ F
variable (u :(i:Fin n) → Label (d i)) (L:Set (Points n))(hL:IsCompact L)(hh:L ⊆ conf n)
include hh hL
open Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp
lemma spicy (j:ℕ)(ε:ℝ)(he:0<ε):∀ᶠ i in atTop,∀ y∈L, ‖iteratedFDeriv ℝ j (fun z=> Z n ((E.B (I i)).r • z) (fun l=> (hops T A E I ρ F).choice i (u l))) y- iteratedFDeriv ℝ j (fun x=>wick d x u) y‖ ≤ ε:=by
     -- define Label varying lifts with limit u (using additive rightInverse)
     let p(l:Fin n):= (X.base (d l)).liftS
     let q(k:ℕ)(l:Fin n):=(X.frame (I k) _).symm (F _ k (projection (u l)))
     let w(k:ℕ)(l:Fin n): Label (d l):= u l + p l (q k l - projection (u l)); have hP(k:ℕ)(l:Fin n): projection (w k l)= q k l:=by
            unfold w p; rw [map_add,(X.base _).right]; abel
     have hs(k:ℕ)(l:Fin n): (hops T A E I ρ F).choice k (u l)= Lanterns.cost T E X (I k) (w k l):=by unfold Bases.choice Lanterns.cost; rw [hP]; unfold q; rw [LinearEquiv.apply_symm_apply]; rfl
     have hx (l:Fin n): Tendsto (fun k=>w k l) atTop (𝓝 (u l)):=by
            unfold w; have hv:= (hG.smooth (d l) (projection (u l))).sub_const (projection (u l)); rw [sub_self] at hv; have hp:= ((p l).continuous_of_finiteDimensional.continuousAt.tendsto).comp hv; rw[map_zero] at hp; have he:=hp.const_add (u l); rw [add_zero] at he; exact he -- comp coe
     let b(l:Fin n):=Module.finBasis ℂ (Label (d l)); let P(l:Fin n):= Fin (Module.finrank ℂ (Label (d l))); let Y:= (l:Fin n)→P l; haveI (l:Fin n): Fintype (P l):= inferInstanceAs (Fintype (Fin _)); -- danger creates defeq mismatch
     let B(a:Y):= fun l=> b l (a l); let c(v:(i:Fin n)→ Label (d i))(e:Y):= ∏ l,(b l).coord (e l) (v l)
     let f(k:ℕ)(e:Y): Points n →ℂ:= LoomZ T E Z d (B e) X (I k)
     let g(e:Y)(x:Points n):ℂ:= UV.Free.wick d x (B e)
     have hU(e:Y): Tendsto (fun k=> c (w k) e) atTop (𝓝 (c u e)):= tendsto_finsetProd _ fun l _=> ((b l).coord _).continuous_of_finiteDimensional.continuousAt.tendsto.comp (hx l)
     have hV: (fun x:Points n=>UV.Free.wick d x u)=∑ e:Y, c u e • g e:= by funext x; rw[YM.Fir.Lantern.expansion b, Finset.sum_apply]; rfl -- instance
     have hR(k:ℕ): (fun x:Points n=>Z n ((E.B (I k)).r • x) (fun l=>(hops T A E I ρ F).choice k (u l)))=∑ e:Y, c (w k) e • f k e:=by
            funext x; let M:=MultilinearMap.compLinearMap (Z n ((E.B (I k)).r • x)) (fun l:Fin n=> (K.level (d l)).subtype ∘ₗ (X.frame (I k) (d l)).toLinearMap ∘ₗ projection)
            simp_rw [hs, Finset.sum_apply]; exact YM.Fir.Lantern.expansion b M (w k) -- inferred
     have hf(k:ℕ)(e:Y)(x:Points n)(hx:x∈ L) : ContDiffAt ℝ (j:ℕ) (f k e) x:=by
            let R:Points n→L[ℝ] Points n:= (E.B (I k)).r • ContinuousLinearMap.id _ _; have he:R x∈conf n:=Compass.vital _ _ K JQ x (hh hx) _ (E.B (I k)).realH; exact (((ht.nice n _).contDiffAt ((conf_open _).mem_nhds he)).of_le (show (↑(j:ℕ):WithTop ℕ∞) ≤ ∞ from (by exact_mod_cast (show ((j:ℕ):ℕ∞) ≤ ⊤ from le_top)))).comp x R.contDiff.contDiffAt
     have hg(e:Y)(x:Points n)(hx:x∈L): ContDiffAt ℝ (j:ℕ) (g e) x:= (UV.Free.Sip.smoothC (hh hx) d (fun i=> (B e i).val)).of_le le_top
     let r:= ε/(Fintype.card Y+1); have hr:0<r:=by unfold r; positivity -- coerces to real
     let M(k:ℕ)(e:Y):=iteratedFDeriv ℝ j (f k e); let N(e:Y):=iteratedFDeriv ℝ j (g e)
     have hb(e:Y): ∀ᶠ k:ℕ in atTop,∀ x∈ L, ‖c (w k) e • M k e x- c u e • N e x‖ ≤ r:=by
            refine cables (fun k=>M k e) (N e) _ (c u e) _ (hU e) ?_ ?_ r hr
            · intro δ hδ; have h:= linearW T E JQ X Z d (B e) hv ht hw j 0 δ hδ L hL hh; simp only [pow_zero,one_mul] at h; exact J.period.eventually h
            have hc:ContinuousOn (fun x=> ‖N e x‖) L:= fun x hx => ((hg e x hx).continuousAt_iteratedFDeriv le_rfl).norm.continuousWithinAt
            obtain ⟨u₀,h⟩:= (hL.image_of_continuousOn hc).bddAbove; exact ⟨max u₀ 0, le_max_right ..,fun x hx=> le_trans (h ⟨x,hx,rfl⟩) (le_max_left ..)⟩
     filter_upwards [eventually_all.mpr hb] with k hk x hx; rw[hR k,hV,iteratedFDeriv_sum_apply (u:=Finset.univ) (f:=fun e=> c (w k) e • f k e) (fun e _=> contDiffAt_const.smul (hf k e x hx)),iteratedFDeriv_sum_apply (u:=Finset.univ) (f:=fun e=> c u e • g e) (fun e _=> contDiffAt_const.smul (hg e x hx)),← Finset.sum_sub_distrib]
     apply le_trans (norm_sum_le ..); apply le_trans (b:=∑ _e:Y,r); · refine Finset.sum_le_sum fun e _=>?_ ; rw [iteratedFDeriv_const_smul_apply (hf k e x hx),iteratedFDeriv_const_smul_apply (hg e x hx)]; exact hk e _ hx
     simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (le_of_lt (lt_add_one _)) hr.le).trans; unfold r; exact (le_of_eq (by field_simp))
omit hL hh
lemma epochZ : (hops T A E I ρ F).Comparison Z:=by
     refine ⟨fun n d u j ε he L hL hh=> spicy J JQ R d Z ht hv hw F hG u L hL hh _ _ he,?_⟩ -- order
     intro n d u x hx; apply Metric.tendsto_nhds.mpr; intro e he; filter_upwards [spicy J JQ R d Z ht hv hw F hG u {x} isCompact_singleton (singleton_subset_iff.mpr hx) 0 (e/2) (half_pos he)] with i hi; apply lt_of_le_of_lt _ (half_lt_self he); have ht:= hi x rfl; rw [← dist_eq_norm, iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp] at ht; change dist ((continuousMultilinearCurryFin0 ℝ (Points n) ℂ).symm _) ((continuousMultilinearCurryFin0 ℝ (Points n) ℂ).symm _) ≤ _ at ht; rw [LinearIsometryEquiv.dist_map] at ht; exact ht
end YM.Mako
#print axioms YM.Mako.epochZ
