import YM.QCD.Finch.Alfa
/-! # transport by spice. give height via fareG -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Finch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove
variable {t s τ u :ℝ}{j k:ℕ}{B:BudgetPoint}
section oste
variable (v:Strut c)
local notation "A₀"=> Keys c N
local notation "U₀"=> Crate c N
abbrev sol (v:Strut c)(N:ℕ):= copies N (haze v (sat v) (ink v))
abbrev vat (v:Strut c)(N:ℕ): Matrix (Keys c N) (Keys c N) ℂ:= Matrix.fromBlocks (sol v N) 0 0 (star (sol v N))ᵀ
lemma vPaid (i j:A₀): ‖vat v N i j‖≤1:=by
   have hv:= copies_unitary N (haze v _ _) (trail (assured v)) -- type mismatch
   rcases i with i|i <;>rcases j with j|j
   · exact (Cost.north (sol v N) i j).trans (Lat.rotation_price hv)
   · exact norm_zero.le.trans zero_le_one
   · exact norm_zero.le.trans zero_le_one
   exact (Cost.north (star (sol v N)) _ _).trans (Lat.rotation_price (Unitary.star_mem hv))
lemma vapor (i j:A₀)(he:act v (locationP i)≠locationP j): vat v N i j=0:=by
   have hk (x y:Modes c N)(he:act v (x.1.1) ≠ y.1.1) : sol v N x y=0:=by unfold sol copies haze; rw [Matrix.blockDiagonal_apply]; split; exact if_neg he; rfl
   rcases i with i|i<;> rcases j with j|j
   · exact hk _ _ he
   · exact rfl
   · exact rfl
   change star ((sol v N) i j)=0; rw [hk _ _ he,star_zero]
variable (o:Site c){P:ℝ}
lemma stakes (i:A₀)(h:0<t): dryL t (changeVars (vat v N) (atom i)) ≤ stemF N*t ∧ visc (Stew.lens (act v o)) t (changeVars (vat v N) (atom i))≤(1+(Stew.lens o i:ℝ))^2*(stemF N*t):=by
   rw [change_atom]; let s:=locationP i; let S:= limits (F:=N) ({act v s}); rw [← sum_subset (s₁:=S) (subset_univ S) (fun j _ hh=>?_)]
   swap
   · rw [vapor v _ _ (fun k=>hh (show j∈limits (F:=N) {act v s} from mem_filter.mpr ⟨mem_univ _,mem_singleton.mpr k.symm⟩)),zero_smul]
   constructor
   · apply (load_sum ..).trans; simp_rw [load_scale]; apply (sum_le_sum (g:=fun _=>1*t) (fun j _=> ?_)).trans_eq; · simp only [sum_const,nsmul_eq_mul,S,leapX,one_mul]
     rw [load_atom _ (fun _=>h)]; exact mul_le_mul_of_nonneg_right (vPaid ..) h.le
   apply (vc_sum ..).trans; simp_rw [vc_scale]; apply (sum_le_sum (g:=fun _=>1*((1+(Stew.lens o i:ℝ))^2*t)) (fun j hj=>?_)).trans_eq; · simp only [sum_const,nsmul_eq_mul,S,leapX]; ring
   rw [reachA _ h.le]; have hV :Stew.lens (act v o) j=Stew.lens o i:=(congr_arg (fun x=>separation x (act v o)) (mem_singleton.mp (mem_filter.mp hj).2)).trans (turn_sep ..)
   rw [hV]; exact mul_le_mul_of_nonneg_right (vPaid ..) (by positivity)
lemma soared (u:ℝ)(hp:fareG 1 t N ≤ u) (h:0<t) (x: EvenA c N):
  Sen (act v o) t (spice v x) ≤ Sen o u x ∧ ‖token c N t (spice v x)‖≤ ‖token c N u x‖ :=by
   let r:= stemF N*t; have hh:0 ≤r:=mul_nonneg (by unfold stemF fingers; positivity) h.le
   have hz : 2*r ≤u:= le_trans (b:=fareG 1 t N) (by unfold r fareG; nlinarith only [h]) hp; have ht:0<u:=lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) (mul_pos zero_lt_one (by unfold stemF fingers; positivity))) h) hp
   let g:= changeVars (vat v N); change visc _ t (g x.val)≤ visc _ u x.val ∧ dryL t (g x.val) ≤ dryL u x.val
   refine ⟨?_, ferry g (fun _=> ht) (fun i _=> ((stakes v (0:Site c) i h).1).trans (le_trans (show r≤ 2*r from (by linarith)) hz)) x.val (boarded _)⟩
   have ht:= sprinkles (g:= Stew.lens o) (f:= Stew.lens (act v o)) (L:=0) h hh g _ (fun i _=> stakes v o i h) x.val (regio _) (by simp) ((one_mul (2*r)).symm) zero_le_one le_rfl (by positivity)
   simp only [pow_zero,one_mul] at ht; exact ht.trans (future _ (by positivity) hz _)
-- no norm operator global
variable (X:Gem c N I)(U:Site c)
lemma owls (i:I)(u:ℝ)(hp:Woven (X.addr i).site (X.addr i).support B u (X.view i) s)(ht:fareG 1 t N ≤ u)(he:0<t): Woven ((glean X).addr (v,i)).site ((glean X).addr (v,i)).support B t ((glean X).view (v,i)) (averageC c*(turnCost B.order B.power*s)):=by
     let z:= turnCost B.order B.power; let K:=(X.addr i).support; let Q:=(X.addr i).site; let U:=act v Q; let T:EvenA c N→L[ℝ] EvenA c N:= LinearMap.toContinuousLinearMap { toFun:=spice v,map_add':=map_add _,map_smul':=fun i j=> eSM _ (phare _) ..}
     let R:= {(glean X) with view:=fun p V=> spice p.1 (X.view p.2 (Strut.sky p.1 V))}
     have hX:Woven U ((glean X).addr (v,i)).support B t (R.view (v,i)) (z*s):=by
          refine ⟨fun x y hv=> congr_arg (spice v) (hp.room _ _ (agrees_pull _ _ hv)),fun j=> gateS _ _ _ _ _ (hp.gated _),?_,?_,T.continuous.measurable.comp (hp.Borel.comp (continuous_pull ..).measurable),mul_nonneg (by unfold z turnCost; positivity) hp.travel⟩
          · intro V hh; exact T.contDiff.contDiffAt.comp 0 (chart_pull v.1 v.2 (hp.use _ ((healthy_pull ..).1 hh)))
          intro V hV l hL hv; have hh' := hp.use _ ((healthy_pull v.1 v.2 B.threshold K V).1 hV)
          rw [show R.view (v,i)= (T: EvenA c N → EvenA c N) ∘ (X.view i ∘ pull v.1 v.2) from rfl,left_linear T _ (chart_pull _ _ hh') hL] -- edit chart
          apply ((soared v Q u ht he _).1).trans; let M:= (needle Q N u).restrictScalars ℝ; let f: Config su c→ Crate c N:= M ∘ X.view i
          have hn:Chart B.order f (pull v.1 v.2 V):=M.contDiff.contDiffAt.comp 0 hh'
          have hz: (f∘pull v.1 v.2)=M∘ (X.view i ∘ pull v.1 v.2):=rfl
          have hq:= Julius.sails V v.1 v.2 hn (B:=B) (o:=Q) (a:=s) (fun m h ht'=>?_ ) hp.travel l hL hv; swap
          · unfold f; rw [left_linear M m hh' h]; exact hp.pole _ ((healthy_pull ..).1 hV) m h ht'
          rw [hz,left_linear M _ (chart_pull _ _ hh') hL] at hq; exact hq
     exact Eq.subst (motive:=fun v' :ℝ=>Woven U ((glean X).addr (v,i)).support B t ((glean X).view (v,i)) (v'*(z*s))) (Real.norm_of_nonneg (show 0 ≤ averageC c from (by unfold averageC; positivity))) (hX.byScalar _)
end oste
end YM.QCD.Finch
