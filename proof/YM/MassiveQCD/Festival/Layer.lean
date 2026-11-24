import YM.MassiveQCD.Festival.Song
/-! # Ports for tilted log commuting before assembling a Cents layout
 Keep arbitrary P.t.order, lemma costs have `window`. Zero π still gives all masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Festival
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Brick Dust Reggae Stem Stew Stew.Phased
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n:ℕ} {a r u t σ τ η ξ T θ x:ℝ}{p:BudgetPoint}{o:Site c}
open Villa Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint Jets.Touch Kites
variable {I J K K₀:Type}
open Ruby Ruby.LanternK Acre Acre.Rails
open Stew.Phased Villa Ruby.LanternK
open MassiveQCD.Analysis.Many MassiveQCD.Analysis
variable (G:Gem c N I)(X:Patron.Rail c N J)(z:ℂ)
namespace Layer
variable (M:Layer c N I K J)(A:BudgetPoint)
variable (b:Flavor N)
noncomputable def costumes (z:ℂ):= tuneLayout M.sheet M.crown z
abbrev PlayK (c:Side)(I K:Type):= I ⊕ (Site c ⊕ K) × Rays
noncomputable def prepare : Loom.StageF c N (PlayK c I K) J:= ⟨(Reggae.weave M.base (M.costumes 1)).addr,M.forced.addr,fun z=>(Reggae.weave M.base (M.costumes z)).view,
    fun z=> (M.mask z).warp, Sum.elim (fun _=>0) (tierM M.crown),M.degree⟩
noncomputable abbrev prim (i:PlayK c I K):Prop:= ∃ j:Site c,i= Sum.inr (Sum.inl j,[])
-- erases all base ids. marker-1 live mass phosphorus at κ only
noncomputable def gain (M:Layer c N I K J)(i:PlayK c I K):Bool:= M.prepare.generation i=1 && !(decide (prim i)) -- coe
variable (Hq: Hill M b p t η τ ξ T θ) -- τ variable real specified
include Hq
local notation "F"=> M.sheet
local notation "U"=> M.crown
lemma stamp : RotationE M.sheet M.crown ∧ ∀ i, 1 ≤ M.crown i ∧ mud (M.sheet.view i 1)=0:=by
    obtain ⟨hG,hH,hx,hK,hV⟩:= Hq.picture; let X:= fun b:Flavor N=>(M.point b:ℂ) • (1:Spike)
    let P:= canon c M.point
    have he : RotationE P (fun _=>1):=by
      constructor
      · refine ⟨fun i=> flashColor i _, fun i V=> pageK _, fun i V=>?_⟩; change Regal c N (Phased.beam i X)=_; rw [flashStar]; apply congr_arg (Phased.beam i); funext b; simp [X,g5_sq] -- inspect.Phased.beam unalias
      intro s k d h; refine ⟨act s,fun i=> ⟨rfl,?_,fun V=>?_⟩⟩
      · unfold P canon rotateL; dsimp only; congr 1
      change Diode _ _ _ _ (Phased.beam i X)=_; rw [flashTwist _ _ _ _ _ h]; apply congr_arg (Phased.beam _); funext b; unfold X; simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_one,h.2.unit.2] -- twist last goal
    exact ⟨quilt P _ _ he _ hG,fun i=>by rcases i with i|i; exact ⟨le_refl 1,plankGrade _⟩; exact ⟨hH i,hx i⟩⟩
omit Hq
-- anchored budgets.Actual, no requirement invoice through positivity when ψ=0.
local notation "F!"=> canon c M.point
lemma sizeN (x:ℝ) (ht:0<t)(hy:t^2*‖M.point‖=x) : ∀ i,Woven ((F!).addr i).site ((F!).addr i).support p t ((F!).view i) (stampFee N*x):=by
    let A i:=(M.point i:ℂ) • (1:Spike); intro i; apply Woven.stretches (A:={(F!).addr i |>.site}) (stamped i ht A _) (Subset.refl _) (le_of_eq ?_); rw [show ‖A‖=‖M.point‖ from wage M.point,hy]
-- base unpublished powers.Mass at exponent. Pay on asset estimator Thorn.
lemma priced_interest (u:ℝ)(h:0≤ u) (x:ℝ)(hx:0 ≤ x) : Anchored (fun i=>((F!).addr i).site) (fun _=> stampFee N*x) (fun i=>coverNumber p.B ((F!).addr i).support) u (stampFee N*x*Real.exp u):=by
    intro i
    have he : 1 ≤ stampFee N:= stampFound
    have hp : coverNumber p.B ({i}:Support c) ≤1:=(Corona.cover_mono (Lattice.halo_subset 0 {i}) p.B).trans (show coverNumber p.B (Lattice.halo 0 {i}) ≤ _ from by simpa using Corona.tile i 0 p.B p.B_pos)
    refine budget_finite (fun i=> ite_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans he) hx) (Real.exp_pos _).le) le_rfl) ?_
    change (∑ j:Site c, if j=i then _ else _)≤_; rw [sum_ite_eq',if_pos (mem_univ _)]; gcongr; change u*(coverNumber p.B {i}:ℝ) ≤ u; exact mul_le_of_le_one_right h (by exact_mod_cast hp)
section meters
open High.PrismT
include Hq
variable (f:Site c⊕ K → ℝ) (ht:1 ≤ t) (hx:∀ i,2^p.order*f i ≤1/4)(hp:∀ i, Woven (M.sheet.addr i).site (M.sheet.addr i).support p t (M.sheet.view i) (f i))
include ht hx hp
local notation "x!"=>p.order
local notation "F'"=> M.prepare
local notation "R"=> (M.costumes 1)
-- sticker for Atlas Ballast. input uses tagged-row geometric estimator, Pays received.H.T.
lemma frenzy (i:(Site c⊕ K) × Rays) (h: Nonwrapping ((R).addr i).support ((R).addr i).site): Dust.Temper p ((R).addr i).support ((R).addr i).site (gain M (.inr i)) ((R).view i) t (priceM (p.order) f i):=by
    have hh:= stamp M b Hq -- specify Hq
    let y:= (F).view i.1; have hA: (tuneLayout M.sheet M.crown 1).view i=plyM y 1 i.2:=by unfold tuneLayout; simp; rfl -- edit
    have hr:= candles F U 1 f hp hx ht (by simp) i; have hu := oriented (F) (U) hh.1 (1:ℝ); rw [Complex.ofReal_one] at hu; let G:= grow (y 1); have hpS: plyM y 1 i.2 1=logM (G i.2):=by unfold plyM; simp only [comp_apply,braid,one_smul]; rfl
    have hW : ‖G i.2‖<1:=by
      have he := (braidLaw 1 ht (hp i.1) (hx i.1) (by simp) i.2).2 1 (flat_ok ..); unfold braid at he; rw [one_smul] at he; exact he.trans_lt ((holdsU (hp i.1) (hx i.1) i.2).trans_lt (by norm_num)) -- order hp args
    have hE :∀ l,mud (G l)=0:= by
      intro l; induction l with
      | nil=> exact (hh.2 i.1).2
      | cons j l ih=> change ((clay c N).restrictScalars ℝ) ((-coeffM (j+2)) • ((G l)^(j+2))) =0; rw [map_smul, show _root_.Eq (((clay c N).restrictScalars ℝ) ((G l)^(j+2))) 0 from held _ _ ih (by omega),smul_zero] -- syntax
    apply Phased.eligible ((R).addr i).site hr (hu.notes.num _ _) (hu.notes.gauge _) (zero_le_one.trans ht) ((R).addr i).anchor (hu.notes.real i) -- rack
    · rw [hA,hpS]; exact (unmaskA _ hW (hE _)).1
    intro hP b'
    rw [hA,hpS]; change shape _ (meter b' (logM (G i.2))) none=_; rw [(unmaskA _ hW (hE _)).2 b']
    -- from activation
    obtain ⟨hd,he⟩:= Bool.and_eq_true_iff.mp hP; have hx' : tierM U i=1:= of_decide_eq_true hd; have hTier:= Nat.eq_one_of_mul_eq_one_right hx' -- naming. Need both
    rcases i with ⟨i,l⟩; cases l with
    | nil=>
       rcases i with i|i
       · exfalso; change (!decide (prim (Sum.inr (Sum.inl i, []):PlayK c I K)))= true at he; simp [prim] at he
       exact Hq.picture.reply i b' (show M.invoice i=1 from (show M.crown (.inr i)=1 from (mul_one _).symm.trans hx')) h
    | cons i k=> exfalso; change M.crown _*((i+2)*Many.tier k)=1 at hx'; have hc:(i+2)*Many.tier k=1:= Nat.eq_one_of_mul_eq_one_left hx'; have hk:i+2=1:=Nat.eq_one_of_mul_eq_one_right hc; omega
end meters
end Layer
end YM.QCD.Festival
