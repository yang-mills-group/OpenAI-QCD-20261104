import YM.QCD.Shell.Glim
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Idyll
/-! # raw woodland multigrid gauge germs BEFORE new allowances. Hull Village. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Sands
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {j n l k : ℕ} {R : Rep su f} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B: ℝ}
variable {Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T R} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config su c} {x : E}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N){K:EvenA c N →+*EvenA c N}
local notation "I'"=> Pipe.Clump S ι
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage
open Ursell QCD.GasP Stained March Graph
open AnalyticBridge.LocalGaussianLaws
open WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Pane AnalyticBridge
instance (c:Side): Countable (RegularAddress c):=Function.Injective.countable (f:=fun i : RegularAddress c=> (i.site,i.support)) (by rintro ⟨x,a,h⟩ ⟨y,b,h'⟩; intro H; have hx:x=y:=congr_arg Prod.fst H; have hb: a=b:=congr_arg Prod.snd H; subst_vars; rfl)
instance (c:Side): Nonempty (RegularAddress c):=⟨⟨0,{0},mem_singleton_self _⟩⟩
def indexQ (c:Side):ℕ ≃ RegularAddress c × ℕ := Extra.Iteration.numbering _
def king (c:Side) : Activities su c:= {pale c su with reg := fun i=>(indexQ c i).1 }
def coverL (e:Equiv.Perm (Site c))(X:RegularAddress c): RegularAddress c:=⟨e X.site, X.support.image e, mem_image_of_mem _ X.anchor⟩
lemma coverQ (e: Equiv.Perm (Site c))(v: RegularAddress c): coverL e.symm (coverL e v)=v := by rcases v with ⟨u,v,h⟩; simp [coverL,image_image,Function.comp_def]
def invest (f: Side)(e:Equiv.Perm (Site f)): Equiv.Perm (RegularAddress f) := ⟨coverL e,coverL e.symm, coverQ e, coverQ e.symm⟩
def leafCode (X: RegularAddress f):ℕ:=(indexQ f).symm (X,0)
lemma lief (B:BudgetPoint)(S:Side): (king S).Valid B 0 0 := by
    let k:= pale S su; let K:=king S; obtain ⟨hh,hA,hz,h,hK⟩:= whey S su B; refine ⟨⟨fun i=> CouplingShape.reg_const _,fun _=> rfl, ?_⟩, ⟨hA.sym,hA.symtest,hA.meas,hA.meas_test,hA.reads,hA.reads_test,hA.permit⟩,?_,?_,hK⟩ -- v_n
    · -- Hess
      exact fun i hv x y hx hY=>by unfold logHessian; change iteratedFDeriv ℝ 2 (fun _ : Directions su S=> (0:ℝ)) 0 _=_; simp -- fix
    · intro s x; obtain ⟨e⟩:=hz s x; let v:= StepData.sendSites s x; let p:= invest S v; let q:= indexQ S
      let Q:= (q.trans (Equiv.prodCongr p (Equiv.refl _))).trans q.symm; have hh i:K.reg (Q i)=coverL v (K.reg i):=(congr_arg Prod.fst (q.apply_symm_apply _))
      refine ⟨⟨Q,e.kp,fun i=> congr_arg RegularAddress.site (hh _),fun i=> congr_arg RegularAddress.support (hh _),e.forced_support,e.forced_inventory,e.forced_tests,fun i U=>rfl,fun i U=>rfl⟩⟩ -- names
    refine ⟨fun _=>0,fun i=> ?_,fun x=>by simp [SumBudget,BudgetPoint.mass]⟩
    simpa only [abs_zero] using! CouplingShape.sup_const (G:=su) (p:=B) (o:=(K.reg i).site) (X:=(K.reg i).support) 0
noncomputable def lore (R: Rep su f): Rep su f:= { R with activities:=king f }
lemma labelR (U:RegularAddress f)(R:Rep su f): (lore R).activities.reg (leafCode U)=U:=congr_arg Prod.fst ((indexQ _).apply_symm_apply (U,0))
lemma chips (R:Rep su f)(h:Intake P T s R): Intake P T s (lore R):= by
    let Q:= lief R.p f; refine ⟨h.ready,⟨h.received.path,h.received.clip,h.received.temp⟩,⟨h.cap.paths, ?_⟩,h.exponent,h.height,h.sizes,h.window⟩; refine {Q with boundE:= VerifiedReset.Time.E_rises Q.boundE ?_, boundK:= VerifiedReset.Time.K_rises Q.boundK (Real.exp_pos _).le}; unfold incomingE; positivity
end YM.ConnectedActivityE6.Blaze.Sands
