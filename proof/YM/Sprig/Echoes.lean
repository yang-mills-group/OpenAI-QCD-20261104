import YM.Sprig.Chap
/-! All-order literal jet comparison with pre-connected basis. Applicable to selection on same W. -/
set_option autoImplicit false
noncomputable section
namespace YM.Sprig
open Function Filter Set MeasureTheory
open Massive QCD QCD.Lat QCD.Grass Lattice Cylinder Patria Patria.Depth Massive.Tarn UV UV.Free
open YM.Fir Massive.Fir Choir Pollens HarmonyF YM.Intag.Sprig YM.Intag.Sprig.Canopy Chloe
open scoped BigOperators Topology InnerProductSpace Classical Matrix ComplexOrder ContDiff
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d n:ℕ}(T: Pollens P Q)(E: Canopy P φ Q)
open Compass
variable {β e:ℝ}(hc:C.Path β e)(hφ:Tendsto φ atTop atTop)(hP:P.System)(hQ:Q.Harmony P φ)(hv:Foil P Q T)
structure Lanterns (T:Pollens P Q)(E:Canopy P φ Q) where
    base(d:ℕ): Qua P d
    frame (i d:ℕ): UV.Free.Symbol d≃ₗ[ℂ]↥(Q.level d)
    leaders i d : Prose (frame i d) T
    secured(d:ℕ): ∀ᶠ i:ℕ in atTop,(frame i d).toLinearMap=snowH E (base d) i
variable (X:Lanterns T E)
open Lanterns
include T E hc hφ hP hQ hv
lemma reads (h:∀ d,∃ n:Side,Injective (P.candidate d n 0)): Nonempty (Lanterns T E):=by
    have hp(d:ℕ):Nonempty (Qua P d):=by obtain ⟨n,H⟩:= h d; exact funds T E hc hφ hP hQ hv _ H
    let B(d):= Classical.choice (hp d)
    choose f hΦ hz using fun d=> chose T E hQ hv (B d)
    exact ⟨⟨B,fun i d=> f d i,fun i d=> hΦ d i,hz⟩⟩
omit hc hφ hP hQ hv
noncomputable def Lanterns.cost (i:ℕ)(p:Label d): Q.W:= (X.frame i d (projection p)).val
variable (K:Canopy.KForm Q)(u:Fin n→ℕ)(p:(i:Fin n)→ Label (u i))
noncomputable def LoomZ (X:Lanterns T E)(i:ℕ)(x:Points n):= K n ((E.B i).r • x) (fun j=>cost T E X i (p j)) -- signature
noncomputable def Zenith (X:Lanterns T E)(i:ℕ)(x:Points n):= LoomZ T E K u p X i x - UV.Free.wick u x p -- names
include hQ
open Video
variable (H: Money E K)(s: Groom Q K)(h: Troupe E K)
include H s h
lemma genuine (j:ℕ):Video.rapid E.cc (conf n) (Zenith T E K u p X) j:=by
    intro L hL he n₀ ε hz
    let t (i:Fin n):= (X.base (u i)).liftS (projection (p i)); filter_upwards [Canopy.readings hQ E K s H h u t j L hL he n₀ ε hz,eventually_all.mpr (fun i:Fin n=>X.secured (u i))] with i hi hp y hy
    have hh: Zenith T E K u p X i=ᶠ[𝓝 y] pErr E K u t i:=by
          have hp(k:Fin n): cost T E X i (p k)= E.cut i (t k):=by unfold cost; change ((X.frame i _).toLinearMap (projection (p k))).val=_; rw[hp k]; rfl
          filter_upwards [(conf_open n).mem_nhds (he hy)] with z hz
          rw[Zenith,LoomZ,pErr]; simp_rw[hp]; rw [DawnS.trails z hz p t (fun k=>((X.base _).right ..).symm)]; rfl
    rw[(hh.iteratedFDeriv ℝ j).eq_of_nhds]; exact hi y hy
set_option maxHeartbeats 480000 in
lemma linearW (j n₀:ℕ)(ε:ℝ)(hp:0<ε)(L:Set (Points n))(hL:IsCompact L)(he:L⊆conf n):∀ᶠ i in atTop,∀ x∈L, E.cc i ^n₀ * ‖iteratedFDeriv ℝ j (fun y=> LoomZ T E K u p X i y) x- iteratedFDeriv ℝ j (fun y=> UV.Free.wick u y p) x‖ ≤ ε:=by
     have hv: (j : WithTop ℕ∞)≤ ∞ := (by exact_mod_cast (show ((j:ℕ):ℕ∞) ≤ ⊤ from le_top))
     filter_upwards [genuine T E hQ X K u p H s h j L hL he n₀ ε hp] with i hi y hy
     specialize hi y hy; let F(y:Points n):=UV.Free.wick u y p; let G:=(LoomZ T E K u p X i); have hF:ContDiffAt ℝ (j:ℕ) F y:= (UV.Free.Sip.smoothC (he hy) u (fun i=>(p i).val)).of_le le_top
     have hG: ContDiffAt ℝ (j:ℕ) G y:=by
          let b(j):= cost T E X i (p j); let R:Points n→L[ℝ] Points n:=(E.B i).r • ContinuousLinearMap.id _ _; have hv':R y∈ conf n:= vital P φ Q hQ y (he hy) _ (E.B i).realH; exact (((s.nice n b).contDiffAt ((conf_open n).mem_nhds hv')).of_le hv).comp y R.contDiff.contDiffAt
     rw[show Zenith T E K u p X i=G-F from rfl,iteratedFDeriv_sub_apply hG hF] at hi; exact hi
lemma nourish (y:Points n)(hy:y∈conf n): Tendsto (fun i=> LoomZ T E K u p X i y) atTop (𝓝 (UV.Free.wick u y p)):=by
     apply Metric.tendsto_nhds.mpr; intro ε he; filter_upwards [genuine T E hQ X K u p H s h 0 {y} isCompact_singleton (singleton_subset_iff.mpr hy) 0 (ε/2) (half_pos he)] with i hi; specialize hi y rfl; rw [dist_eq_norm]; apply lt_of_le_of_lt _ (half_lt_self he); simpa only [pow_zero,norm_iteratedFDeriv_zero, one_mul, Zenith] using hi
end YM.Sprig
#print axioms YM.Sprig.linearW
#print axioms YM.Sprig.nourish
#print axioms YM.Sprig.reads
