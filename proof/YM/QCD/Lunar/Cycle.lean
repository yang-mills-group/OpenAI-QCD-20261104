import YM.QCD.Lunar.Shield
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lunar
open Function Filter Lattice RG Wilson Gauge Metric Finset
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical InnerProductSpace ContDiff
variable {b k i l : ℕ} {c f L:Side} {P:BudgetPoint}{x a t u σ ε:ℝ} {W V:Support c}{o p:Site c}
open AnalyticBridge.VerifiedReset
variable {G:Gauge}
namespace Ring0
open Cove StepData Stew Reggae Patron Lat Acre Rails Kites Push.AbsoluteSums Matrix
variable {I:Type} {u₀:Pot su c}{v M θ H K A B d η r α:ℝ}
open PhysicalNext.Repeat WilsonStartup Collection Extra.Iteration Progress.DirectedRecipe
section tune
-- delta=1 with fake input. lens.Blue.Plain.
variable (T:PathData su)(O:Clip)(P:BudgetPoint) (N:ℕ)
noncomputable def emT (N:ℕ)(c:Side):Patron.Gem c N Empty:=⟨Empty.elim,Empty.elim⟩
lemma amends : Crossing (emT N c):=by refine ⟨⟨fun i=>i.elim, fun i=>i.elim, fun i=>i.elim⟩,fun _ _ _ _=> ⟨Equiv.refl _,fun i=>i.elim⟩⟩
lemma mudd : Local (theater (emT N c)) P (stock (emT N c)) (P.threshold^2) 0:=by
    let G:= emT N c; have h: Licence P (Quotes.preExponent P) (P.threshold^2) 0 G:= by
         refine ⟨Empty.elim,fun i=> ?_,fun i=>i.elim⟩; refine ⟨fun i=> i.elim,Summable.of_finite,?_⟩; rw [tsum_empty]; exact sq_nonneg _
    exact regMoney _ (amends ..) h le_rfl
lemma zeroL (i:ℕ) : ((stock (emT N c)).logRead i) =0:=by
    unfold stock; simp only [Function.comp_apply,padX]; rcases numbering (Curtain c Empty) i with i|i; exact i.elim; rfl
-- payouts zero.Payment
lemma empty_delta (P:Listing su c)(T: Collection.Source su c)(h:∀ i,T.logRead i=0)(i:ℕ)(b:BudgetPoint)(U:Grid c): untagged P b T i U=0∧ Collection.dust P b T i U=0:=by
    let A:= P.reg i; let p:=b.threshold; have hF : projection A (T.logRead i)=0:=by
        rw [h i]; ext x y; unfold projection; split
        · change logHessian (fun _=>0) ((wedge x (spike su)).field A.site) ((wedge y (spike su)).field A.site)=0
          unfold logHessian; simp
        rfl
    have hz: Residual.payout A (T.logRead i)=0:=by unfold Residual.payout; rw [hF]; funext x; simp [counter,quad]
    have hh : Residual.rebate A (T.logRead i)=0:=by unfold Residual.rebate; rw [hz,h]; simp; rfl -- or simp linter
    refine ⟨?_,?_⟩
    · change masked p (expand A) _ U=0; rw [hh]; exact Start.masked_zero ..
    change Residual.fault A (T.logRead i) p U=0; unfold Residual.fault; split; rfl; rw [hz,h i]; simp
set_option quotPrecheck false
noncomputable abbrev bedT (R:PathData su)(P:BudgetPoint)(c:Side):= shelves (theater (emT 0 c)) R P
noncomputable abbrev vowT (R:PathData su)(P:BudgetPoint)(O:Clip)(c:Side):=Collection.fill (theater (emT 0 c)) R O P (stock (emT 0 c)) 0 1
local notation "X?"=> emT 0 c
variable {V':PathData su}(hV: T.Bounds O σ A M) (he: Decent O P)(hW: Geo.Width P O σ)(hc:20<c.val)
include hW hV he hc
-- Recipe exact orientation. kinetic = old + corrected. Choir need negative sign.
lemma wedgeK (U:Grid c) :Push.BetaTransport.kinetic T O P U+ ((bedT T P c).pours (vowT T P O c)).additive P U=(∑ i,heads P i U)+(∑' i,(vowT T P O c).logarithm i U):= by
    let V:= theater X?; let p:= stock X?; have hh: Local V P p (P.threshold^2) 0:= mudd P 0; unfold bedT vowT
    rw [hh.additive simple hV 0 1, hh.throw_sum simple hV he hW 0 1]; simp_rw [fun i=>(empty_delta V p (zeroL 0) i P U).1,fun i=>(empty_delta V p (zeroL 0) i P U).2]; simp only [tsum_zero,zero_add]; simpa only [zero_add, one_mul, zero_mul] using! path_split hV hW he 0 1 U -- names
open Loom
lemma vowsP (hr:0<r):let X:= ostinato (bedT T P c) (vowT T P O c) N; let Z:= riff (bedT T P c) (vowT T P O c) N
   Crossing X∧Quartz X∧ Licence P P.supportExponent (regularNeed su P O σ A 0 (P.threshold^2)) r X∧ Purchases Z P.threshold P.B (P.supportExponent+1) (softNeed su P O σ A 0 (P.threshold^2)) r ∧∀ (U:Grid c), HasSum (fun i=> Z.mean i U) (baker c N (∑' i,(vowT T P O c).logarithm i U)) ∧ HasSum (letters X P.threshold U) (ocean c N (((bedT T P c).pours (vowT T P O c)).additive P U)) :=by
    intro Q Y; let E:= theater (emT 0 c); let p:=stock (emT 0 c); let W:= P.threshold^2; have hh : Local E P p W 0:=mudd ..; have h:=hh.fittings simple hV he hc 0 1
    obtain ⟨g,hg,hB⟩:= hh.cheap; let M:= numbering (EKey c); let D:= numbering (LKey c); let u:=quoteE (n:=c) T P O 0 1 g; let l:=quoteL (n:=c) T P O 0 1 g; obtain ⟨hv,hL⟩:= Local.quote_family hV he hW 0 1 hg hB (by rw [abs_one,mul_one]); let x:=bedT T P c; let y:=vowT T P O c
    have hf i: P.supBounds (Q.addr i).site (Q.addr i).support (y.regular i) (u (M i)):= Local.quote_regular simple hV he 0 _ hg hh.smooth (M i)
    have hi :Licence P P.supportExponent (regularNeed su P O σ A 0 W) r Q:=by
         refine ⟨u∘M,fun i=> ?_,fun i=>wealthy N _ _ _ (h.regular.smooth i) (hf i) hr.le⟩
         let L i:=incoming E T P i; have hb: SumBudget (fun j=> if (L (M j)).site=i then P.mass (L (M j)).support (u (M j)) else 0) (regularNeed su P O σ A 0 W):= Extra.Iteration.Cost.equiv M (hv i)
         simp only [BudgetPoint.mass,mul_comm (Real.exp _)] at hb; exact hb
    have hx i U : ‖y.logarithm i U‖≤ l (D i):= Local.quote_soft simple 0 1 hg hh.smooth (D i) U -- implicit chooses O or issue
    obtain ⟨hK,hG⟩:= readySoft _ _ h (N:=N); have hΞ: Ac.Hit Y.bud P.B (l∘ D) (P.supportExponent+1) (softNeed su P O σ A 0 W):= fun i=> Extra.Iteration.Cost.equiv D (hL i)
    refine ⟨visa _ _ h, ready_rose _ _ h, hi, ⟨hG,hK,l∘ D,?_,hΞ⟩,fun i=> ?_⟩
    · intro i U; apply le_trans (b:=Sen (0:Site c) r (baker c N (y.logarithm i U))) (Stew.shot (Stew.lens 0) _ _ hr); rw [vine _ _ _ hr.le]; exact hx i U
    have he:= permits Q hi hr P.exponent_pos.le i; exact ⟨visor _ _ i hx hΞ,(rose_sum _ _ i he) ▸ he.hasSum⟩ -- no congr_sum?
end tune
end Ring0
end YM.QCD.Lunar
