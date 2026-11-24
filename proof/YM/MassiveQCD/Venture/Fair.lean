import YM.MassiveQCD.Venture.Fleet
import YM.MassiveQCD.Palette.Doors
import YM.MassiveQCD.Relight.Wing
/-! # Repricing ALL K poses after wear and merging Soft fees
 Use exact Cauchy certificates after genuine-post processing. General κ valuations permit compact countable layout. Colors pay both at real marker and ZERO (unmarked strong sense).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open MassiveQCD.Analysis.Shelf Metric LanternK Relight
open Footprint Villa Port
variable {c:Side}{N n B:ℕ}{t s r δ T τ u v ζ σ A :ℝ}{i:Site c} {ι β: Type}
local notation "Ω"=> EvenA c N
local notation "T⁔" => Metric.ball (0:ℂ) 1
variable (X:Rail c N ι)(G:Hue c N ι)(F: LanternK c N ι)
lemma ridesK (h:X.Reg t)(r:ℝ): (flightK X r).Reg t:=⟨fun i U W hv hp=>congr_arg (wearK c N r) (h.uses i U W hv hp),fun i=>(songT (c:=c) (N:=N) r).continuous.measurable.comp (h.reads i),fun i W=> dings r _ _ (h.role i W),fun i U hx=> h.buys i U (fun hv=> hx ((congr_arg (wearK c N r) hv).trans (map_zero _)))⟩ -- congr
lemma inkK (h:MixedInk X)(r:ℝ): MixedInk (flightK X r):=by
    let K:=wearK c N r; refine ⟨fun i U z=> congr_arg Subtype.val (show sways (Lat.rotates N z) (K (X.warp i _))=K (X.warp i U) from ?_),fun i U W hw=>(purity _ _ r).trans (congr_arg K (h.num i U W hw)),fun i U=>(dearR _ r).trans (congr_arg K (h.real i U)),fun s d k hv=>?_⟩
    · exact (purity _ _ r).trans (congr_arg K (Subtype.ext (h.gauge i U z)))
    obtain ⟨e,hw⟩:= h.moves s d k hv; refine ⟨e,fun i=>⟨(hw i).1,(hw i).2.1,fun j=>(purity _ _ r).trans (congr_arg K ((hw i).2.2 j))⟩⟩
noncomputable def flightF (r:ℝ): LanternK c N ι:= ⟨F.bud,fun z=>(flightK (F.get z) r).warp⟩
@[simp] lemma get_ff (r:ℝ)(z:ℂ): get (flightF F r) z=flightK (F.get z) r:=rfl
lemma charteredK (h:F.ChargedK u r t T B δ τ)(hv:0<v)(hz:0<ζ)(hp:v*ζ ≤ t): (flightF F v).ChargedK u r ζ T B δ τ:=by
    refine ⟨h.system, fun z hh=> ridesK _ (h.temp z hh) v, fun z hh=> excess _ (h.power z hh) hz hv hp, ?_⟩; intro j x y hy
    let U : Ω→L[ℂ]Ω:= LinearMap.toContinuousLinearMap (wearK c N v).toLinearMap; exact (U.analyticAt _).comp (h.aura j x y hy)
-- use only stem chart analytic interior
structure BeamY (c:Side)(N:ℕ)(ι:Type) where
   bud : ι→ Support c
   view : ℂ→ι→Grid c→EvenA c N
namespace BeamY
variable (J:BeamY c N ι)(Y:BeamY c N β)
noncomputable def cupY (z:ℂ): Hue c N ι:=⟨J.bud,J.view z⟩
structure Vows (t u A v:ℝ)(B:ℕ) :Prop where
   light : ∀ z:ℂ,z∈T⁔→Wax (J.cupY z) t B u A v -- Wash
   shine i V: Roof (fun z:ℂ=>J.view z i V)
   base : Hue.Garish (J.cupY 0)
   real (x:ℝ): |x|<1 → Hue.Doorways (J.cupY x)
noncomputable def shadeY : BeamY c N (ι⊕β):=⟨Sum.elim J.bud Y.bud,fun z=> Sum.elim (J.view z) (Y.view z)⟩
lemma chargedM (p:BudgetPoint)(h:J.Vows t u A v p.B)(hp:Y.Vows t u σ v p.B): (shadeY J Y).Vows t u (A+σ) v p.B:=by
    refine ⟨fun z hv=> reach_w (h.light _ hv) (hp.light _ hv),?_,nestling _ _ h.base hp.base,fun x hx=> track_sum _ _ (h.real x hx) (hp.real x hx)⟩; rintro (i|i) V; exact h.shine i V; exact hp.shine i V
noncomputable def spectra (G: Hue c N ι)(χ:ι→ℕ): BeamY c N ι:=⟨G.bud,fun z=> (bleach G χ fun n=>z^n).mean⟩
@[simp] theorem get_spe (G: Hue c N ι)(χ:ι→ℕ)(z:ℂ): cupY (spectra G χ) z=bleach G χ (fun n=> z^n):=rfl
lemma stall (χ:ι→ℕ)(h:Yank G χ)(hp:∀ i,χ i=0 →∀ U, Patron.Fit (G.mean i U))(p:BudgetPoint)(hf:Wax G t p.B u A v): (spectra G χ).Vows t u A v p.B:=by
    have he x: cupY (spectra G χ) (x:ℝ)=bleach G χ fun n:ℕ=> ((x^n:ℝ):ℂ):=by rw [get_spe]; simp
    have hm x : Hue.Doorways (cupY (spectra G χ) (x:ℝ)):=by rw [he]; exact door _ χ (realY G χ _ h)
    have hx : Hue.Doorways (cupY (spectra G χ) 0):=by simpa using hm 0
    refine ⟨fun z hz=>?_,fun i U=> ?_,⟨hx.gauge,hx.real,?_,hx.travel⟩,fun x _=>hm x⟩
    · rw [get_spe]; simpa only [one_mul] using (bleachPay G χ (fun n=>z^n) (fun i=>by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hz).le) zero_le_one hf)
    · change AnalyticOnNhd ℂ (fun z:ℂ=>z^χ i • G.mean i U) T⁔; intro z _; exact ((analyticAt_id (𝕜:=ℂ)).pow _).smul analyticAt_const -- defeq
    intro i U; change Fit ((0:ℂ)^χ i • _); by_cases he:χ i=0; · rw [he,pow_zero,one_smul]; exact hp i he U
    rw [zero_pow he,zero_smul]; exact fun W _=> map_zero _
end BeamY
end YM.QCD.Ruby
#print axioms YM.QCD.Ruby.BeamY.stall
