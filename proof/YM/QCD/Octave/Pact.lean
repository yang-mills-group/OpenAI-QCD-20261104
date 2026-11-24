import YM.QCD.Octave.Vine
import YM.QCD.Raft.Port
/-! # Fixed analytic word for saturated trial agrees through captured degree even with SAME m. Includes U vertical tangents. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Octave
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam Cove Golden NormedSpace
open Lat YM.Next.Free Reggae Jets.Touch Port Kit Run Stew Bay Strut Leaf Tee Flume Garden Kings Orbit LeafM
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix Matrix.Norms.L2Operator
open Smoke Eyrie Raft Further.PhysicalPeriodLimitF933 Jacobi
variable {E F Y:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup Y][NormedSpace ℝ Y]
variable {A B:E → F}
lemma duchy (g:F→Y) (h: Eyrie.Duet A B) (hg: ContDiffAt ℝ ω g (A 0)):Eyrie.Duet (g ∘ A) (g ∘ B):=by
    have hh :ContDiffAt ℝ ω g (B 0):= h.meet ▸ hg
    refine ⟨hg.comp _ h.leftF,hh.comp _ h.rightF,congr_arg _ h.meet,fun v=>?_,fun i j=>?_⟩
    · rw [blade_over v h.leftF hg,blade_over v h.rightF hh,h.meet,h.paint]
    rw [area_eval _ _ h.leftF hg, area_eval _ _ h.rightF hh,h.meet,h.paint,h.paint,h.rep]
lemma duct (g:Y→E) (h: Eyrie.Duet A B)(hv:ContDiffAt ℝ ω g 0)(he:g 0=0):Eyrie.Duet (A∘g) (B∘g):=by
    have hA : ContDiffAt ℝ ω A (g 0):=he.symm ▸ h.leftF; have hB: ContDiffAt ℝ ω B (g 0):=he.symm ▸ h.rightF
    refine ⟨hA.comp _ hv,hB.comp _ hv,?_,fun i=> ?_,fun i j=>?_⟩
    · change A _= B _; rw [he,h.meet]
    · rw [blade_over i hv hA,blade_over i hv hB,he,h.paint]
    rw [area_eval _ _ hv hA,area_eval _ _ hv hB,he,h.paint,h.rep]
lemma paired {g h:E→Y}(hp:Eyrie.Duet A B)(hv:Eyrie.Duet g h): Eyrie.Duet (fun x=>(A x,g x)) (fun x=>(B x,h x)):=by
    let L:= ContinuousLinearMap.inl ℝ F Y; let P:= ContinuousLinearMap.inr ℝ F Y; have he (x:E→F)(y:E→Y):(fun i=>(x i,y i))=L ∘ x+P ∘ y:=funext fun i=> by ext <;> simp [P,L]
    rw [he A g,he B h]; exact (duchy L hp L.contDiff.contDiffAt).add (duchy P hv P.contDiff.contDiffAt) -- product add rfl?
lemma muted (h:Eyrie.Duet A B):∀ i≤2, iteratedFDeriv ℝ i A 0= iteratedFDeriv ℝ i B 0:=by
   intro i hi; ext1 x; interval_cases i
   · simp only [iteratedFDeriv_zero_apply,h.meet] -- name
   · rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply]; exact h.paint _
   have hx:= h.rep (x 0) (x 1); rw [iter _ _ h.leftF,iter _ _ h.rightF, show ![x 0,x 1]= x from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩) ] at hx; exact hx

variable {c f:Side}{D : Ratio c f}
open Work.F03 Sparks Eyrie Stationary
lemma chartG {S:StepData c f} (T : Forest S.ratio): ∃ p:(Positions (Uniform.Primary c su) × Poll.Body (Precision.Key T su)) → Quarry.Cnr f, p 0=0 ∧ ContDiffAt ℝ ω p 0 ∧ projection (G:=su) T=ᶠ[𝓝 0] (Stationary.input su f) ∘ p:=by
   let X:= paint T su; let Y:= combineH (G:=su) T; let L:=Quarry.Cnr f
   let y:= (arm su f 1).symm; let p:= y ∘ (Work.F03.axisLog (G:=su) T)
   let Q:= Y.trans X
   have hp: ContDiffAt ℝ ω p (Q 0):=by rw [map_zero]; apply y.contDiff.contDiffAt.comp (f:= _) 0; exact (inclusion_smooth _).snd
   have hv:(Work.F03.axisLog (G:=su) T 0)=0:=congr_arg Prod.snd (inclusion_zero T)
   refine ⟨p∘Q,?_, hp.comp (f:=Q) _ Q.contDiff.contDiffAt,?_⟩
   · change y (axisLog _ (Q 0))=_; rw [map_zero,hv,map_zero]
   have h:= Q.continuous.tendsto 0; rw [map_zero] at h; filter_upwards [h.eventually (Work.F03.inclusion_works T)] with x hx
   change live T (Q x)=represent (arm su _ 1 (p (Q x))); unfold p; rw [Function.comp_apply]; change _=represent (arm su f 1 (y _)); rw [ContinuousLinearEquiv.apply_symm_apply]; exact hx.symm
end YM.QCD.Octave
