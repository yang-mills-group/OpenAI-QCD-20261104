import YM.Poised.Fountain
import YM.Poised.Street
import YM.QCD.Fawn.Price
/-!
# Charter interior, picks real Crown.
Shrink discharged D.ε at furnishing before actual x height. Allows full-rank path cost with constant output.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo Planned.AtomRegular MeasureTheory Analysis
open AnalyticBridge.SectorAffine.Offset WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open QCD QCD.Lat QCD.Kit QCD.Grass QCD.Brick QCD.Cove QCD.Stew ConnectedActivityE6.Blaze Push.Uniform UV Cylinder SourceRead
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {B :Type}[Fintype B] {c f : Side} {S : StepData c f} {T : Tube su S} {Pt : Teller su} {k : S.Choices} {V : Config su c} {F : Forest S.ratio}
    {P R : BudgetPoint} {o : Site f} {g : Site c → su.El} {X : Support f} {Y : Support c} {Q M m r t x τ W w σ G₀ ρ v s u u₁ u₂: ℝ} {I : Type} {J: BudgetPoint}
    {A : Stores S} {n l N j q₀ : ℕ} {D : Slab su c l} {q : Chi} {d : ℝ} {V' : Config su f → Lat.Fields f 6}
namespace Fountain
open Pipes
local notation "Y'"=> Fields f 6 -- remove amb
variable (a:Museum F x A X Y I)[Fintype I] {C: Libretto su n}{E: Heir.Record}
variable (hp:Plays C E P R Pt T x) (b:Cover) (hw:wrap f b∈X) (hg :Canvas P (S.ratio.parent (wrap f b)) (reach x) V g n C.C)
variable (hO:Short S R X)(hn:2≤n)(hV: Healthy P.threshold Y V) (U:Grid f)(z: Prices su I)(hu:0≤u) (hv:u*‖tape z‖≤ E.ε*R.threshold)(hl:l≤n) (hD:∀ i,P.dirBound (S.ratio.parent (wrap f b)) (D i))
set_option quotPrecheck false
local notation "L"=> S.patch.L
local notation "O"=> S.ratio.parent (wrap f b)
local notation "X₀"=> enters V (S.ratio.parent (wrap f b)) (reach x) g D (a.extra g u z)
local notation "Z₀"=> launch V (S.ratio.parent (wrap f b)) (reach x) g D
local notation "V₀"=> Heir.loom P (reach x) C.C
local notation "b'"=> Kit.slope S.patch.L
variable {p p₀ :ℕ}{I₀ I₂ χ R₁ :ℝ}
variable (he:ScrollX C χ I₀ q₀ p Pt)(hPt:Pt.Funds S T)(hτ:R.power=p)(hE: clinicFee n E.Q*(loom P (reach x) C.C)^2 + E.ε*R.threshold ≤ (Kit.slope S.patch.L)^max q₀ 2 * R.threshold)
variable (f₀:ℝ)(w:B→ℝ)(Z:VectorD (Site f) B)(hX:∀ i,0 < w i)(hF:0<f₀) (ht:Heritage R X b (purseX (wrap f b) p₀ f₀) w q₀ (0,Z) (Kit.slope S.patch.L) I₂) (h1: 1≤I₂)
variable (ζ:ℝ)(hc:∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→Through n (yaw i j) x ζ) (hb : (1+patterns n)*(ζ*(C.M*loom P (Heir.reach x) C.C))*((Fintype.card Pipes.Shell:ℝ)*pup q₀ I₂ * (Kit.slope S.patch.L)^2) ≤ (Kit.slope S.patch.L)^max q₀ 2) (hM:C.M*loom P (Heir.reach x) C.C ≤1)
variable (YJ:Grid f→Lat.Fields f 6)(nf m₀:ℕ) -- remove
variable (χ₀ : TaperHol) (hG : ∀ k U,slots 6 k (YJ (gauge k U))=YJ U) (heV:Ease.Charm R X YJ) (hS:∀ U,YJ U∈ Creek.region (limits X)) (hB:∀ U,YJ U ∈ layer (Faces (Site f)) nf)(hvF: ∀ (J:Labels.Jet su)(t:ℕ),t<q₀ →WardBin.leading t (Beacon.moment (d:=m₀) χ₀ b J YJ)=0)
set_option quotPrecheck false
local notation "pⁱ"=> purseX (wrap f b) p₀ f₀
variable (hh:R.supBounds (wrap f b) X (framesF (purseX (wrap f b) p₀ f₀) ∘ YJ) τ)(Vb:Hera.Rights su n) (hy:m₀≤R.order)(hm:q₀ ≤ m₀+1)(hx₀:q₀≤2*n)
include hp hg hw hG heV
-- above b chosen by caller
noncomputable abbrev vat (Z:VectorD (Site f) B):Lat.Fields f 6 →L[ℝ] Alg B:= ((changeVars Z).toLinearMap.restrictScalars ℝ).toContinuousLinearMap
omit hp hg hw hG heV in
lemma recipro (S:Frame f)(U:Grid f): Lattice.gauge S⁻¹ (Lattice.gauge S U)=U:=by funext j; simp only [Lattice.gauge,Pi.inv_apply]; group
omit hp hg hw heV in
lemma oblique (S':Frame f)(A:Lat.Fields f 6→L[ℝ] ℝ): (fun U=> A (YJ (gauge S' U)))=(A.comp (mills S'⁻¹))∘ YJ:=by
   funext U; apply congr_arg A; change YJ (Lattice.gauge S' U)=slots 6 S'⁻¹ (YJ U); symm; have ht:= hG (S'⁻¹) (Lattice.gauge S' U); rwa [recipro] at ht
-- Joint chart smooth across Linked poles hope through masked function v; use Pane.joint.
include hn hV hu hv
lemma atReception (T0: Alg B →L[ℝ] ℝ) : let F':= g∘ S.ratio.parent; let f (i:Grid f):= T0 (framesF w (changeVars Z (YJ (Lattice.gauge F' i))))
   ContDiffAt ℝ n (fun z' : Directions su c × Prices su I => f (a.received k T q d u (increment V z'.1) U z'.2)) (0,z):=by
    intro F' f1
    let p := hp.rehearsed; obtain ⟨u',hr⟩:= framed a hV hp.space (by omega) (Z:=C.Z) p.wire
    have hW := border_healthy hp.sew C.width C.price p.early (hp.acts F k) E.majorant (by omega) p.tensions a hp.bulletin C.Z rfl p.wire hp.space p.temp_eq hV U z hu hv R.threshold_pos (q:=q) (d:=d) -- aT
    obtain ⟨he,hx⟩:= a.joint_overt (d:=d) (q:=q) (w:=z) (u:=u) (hp.acts F k) hp.bulletin hr U C.C_one p.tensions.allows (fun g=> (a.extra_size g u hu z).trans (hv.trans p.tensions.noise))
    let W (z' : Directions su c × Prices su I) := a.overt T k V u z u' (increment V z'.1) z'.2
    have hW₁ : W (0,z)=0 := by unfold W; rw [Work.G07.at_zero_increment,a.overt_home]
    let G:= (T0.comp (framesF w)).comp (vat Z); have hZ:f1=(G.comp (mills F'⁻¹)) ∘ YJ:= oblique YJ hG F' G
    have hX:Ease.Charm R X f1:= hZ.symm ▸ (heV.scales _)
    exact ((show ContDiffAt ℝ (↑n) (f1 ∘ increment (a.received k T q d u V U z)) (W (0,z)) by rw [hW₁]; exact (hX.smooth _ hW).of_le (Nat.cast_le.mpr p.orders)).comp (f:=W) _ he).congr_of_eventuallyEq (hx.mono (fun _ hz=>hX.sites _ _ hz))
omit hv
include Vb hb he hτ hV hPt hh h1 hx₀ hm hvF hE χ₀ hF hX hB hS hM hc hO ht hy
lemma reached (μ:ℝ)(T₁: Alg B→L[ℝ]ℝ)(hT: ‖T₁‖ ≤μ) (z:ℕ){Γ:Prices su I→ℝ}(hΓ:Silences su I n u (E.ε*R.threshold) Γ) :
    let A:= fun i => T₁ (framesF w (changeVars Z (YJ (Lattice.gauge (g∘ S.ratio.parent) i))))
    let t:=μ*((tithy nf I₀ I₂ Vb q₀)*τ*b'^q₀)
    Hera.Fugue a U A T C E P R z Γ u t k q d (wrap f b) V:=by
   intro K t y hyK; have hV':= hΓ.stay y hyK
   refine ⟨atReception a hp b hw hg hn hV U y hu hV' w Z YJ hG heV T₁,?_⟩ -- arg
   intro j hj A hA; have hr := tableau (U:=U) (k:=k) (d:=d) (q:=q) (D:=A) a hp b hw hg hO hn hV y hu hV' hj hA he hPt hτ hE f₀ w Z hX hF ht h1 ζ hc hb hM YJ nf m₀ χ₀ hG heV hS hB hvF hh Vb hy hm hx₀
   have hh:= linear_through T₁ hr hT; exact (hh.pay _ hj).trans (le_mul_of_one_le_right hh.nonneg (one_le_pow₀ ((Lute.leading_one _).trans (le_add_of_nonneg_right (mul_nonneg (Lute.rust_nn hu) (sq_nonneg _))))))
end Fountain
end YM.Massive.Poised
