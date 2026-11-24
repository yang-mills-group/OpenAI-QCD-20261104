import YM.QCD.Fog.Atlas

/-! # Match to inherited score and Herm log price. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fog
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Orbit Run Revolve Flume Sparks Quarry Tavern Birth YM.Further.PhysicalPeriodLimitF933 Jacobi Macrame Push.Uniform Garden Transfer Extra Iteration QCD.Smoke Work.F03
open scoped Matrix Topology ContDiff BigOperators Classical
variable {E: Patch} {j k N B:ℕ}{K:KernelChoices}{p:Clip}{r D A u v Λ δ c Y w q g R a b d η Ω Θ:ℝ}{M: Before su u v E.J K N}
variable (V:Back E K j k p u v) {J:Plan j}{U:On}{n:Side}{I T:Type}
structure Avenue (V:Back E K j k p u v)(η Ω Θ:ℝ) extends Engine V η Ω Θ where
 paidUp (i:ℕ):DemandG (anchor V i) p D D' T η Ω Θ s su
 merits : D'.metric.strip η Θ
 home : D'.metric.read 0=1
 Sw (i):Bid.Sworn D' (V.chain.n i) su
structure Ornament (r c:ℝ) where
 mark : Type
 [idx : Countable mark] -- syntax
 P:mark→PairG su
 paid: Palisade P r c
attribute [instance] Ornament.idx
namespace Ornament
variable (O:Ornament r c)
def page:= installG O.P
lemma cost (hp:0<r): Charged O.page r (expPrice 2 r*c):= padded_cost (assembled hp.le O.paid.2.2)
lemma permit (hp:0<r): Silent O.page ∧ SymmetricAtoms O.page:= ⟨padded_silent (assemble_silent hp O.paid),padded_sym (assemble_symm O.P O.paid.2.1)⟩
lemma trace_payment (V:Flux su n)(hp:0<r):total (Iteration.plain∘O.page) V=total O.P V:= (total_padded (assembled hp.le O.paid.2.2) hp.le _).trans (assemble_at O.paid.2.2 hp.le V)
def graft (P: Ornament r d): Ornament r (c+d) where
 mark:= O.mark⊕P.mark
 idx := inferInstance
 P:= Sum.elim O.P P.P
 paid:= ⟨fun i=> by cases i <;> first| exact P.paid.1 _| exact O.paid.1 _,fun i=> by cases i <;> first| exact P.paid.2.1 _| exact O.paid.2.1 _, Cost.sum (f:=fun i=> ((Sum.elim O.P P.P i).atom).budget r) O.paid.2.2 P.paid.2.2⟩
lemma graft_score (P: Ornament r d) (hp:0<r)(V:Flux su n):total (Iteration.plain ∘ (O.graft P).page) V=total (Iteration.plain∘ O.page) V+total (Iteration.plain∘P.page) V:=by
  rw [trace_payment (O.graft P) V hp,O.trace_payment V hp,P.trace_payment V hp]; unfold total; exact Summable.tsum_sum (f:=fun i:O.mark ⊕ P.mark=> ∑ x, (Sum.elim O.P P.P i).sample V x) (net_summable O.P V hp.le O.paid.2.2) (net_summable P.P V hp.le P.paid.2.2)
def rise (h:c ≤ D): Ornament r D:={O with paid:=⟨O.paid.1,O.paid.2.1, Cost.enlarge O.paid.2.2 h⟩}
end Ornament
namespace Voyage
open scoped Matrix.Norms.Frobenius
variable (O: Ornament r c) -- fix
/- `Probe` for instantiated action -/
def barG (P:ℕ→ Atom su 2)(n:Side): Cnr n→ℝ := fun x=>Iteration.action P (input su n x)
lemma small_basis {P:ℕ→ Atom su 2}(hp:Charged P r c)(h:0<r)(x:Cnr n):
    Tendsto (fun t:ℝ=> barG P n (t • x)/t^2) (𝓝[≠] 0) (𝓝 (Patch.average fun s:Signed=>total (Iteration.plain ∘ P) (flux (Bid.pulled (arm su n 1 x) s)))):=by
  unfold barG input; simp_rw [map_smul]; exact action_limit P h hp _
lemma zen {P:ℕ→Atom su 2} (hp:Charged P r c)(h:0<r)(n:Side):ContDiffAt ℝ ω (barG P n) 0:=by
  have ht (i:Edge (Site n)): ContDiffAt ℝ ω (fun x:Cnr n =>su.mat (input su n x i)) 0:= ((represent_smooth ..).comp (arm su n 1).contDiff).contDiffAt
  exact Iteration.action_smooth h hp ht
lemma zenith {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]{F:X→ℝ}(h: ContDiffAt ℝ ω F 0)(Q:X→ℝ)(hh:∀ x,Tendsto (fun t:ℝ=> F (t • x)/t^2) (𝓝[≠] 0) (𝓝 (Q x))) (x:X):
    blade x F 0=0 ∧ Jacobi.mixed x x F 0=2* Q x:=by
  have hd(x:X): ContDiffAt ℝ 2 (fun t:ℝ=>F (t • x)) 0:=(show ContDiffAt ℝ 2 F ((0:ℝ) • x) from by simpa using h.of_le (show (2: WithTop ℕ∞)≤ω from le_top)).comp 0 (by fun_prop)
  have hz x:=value_slope_of_sq_limit (hd x).continuousAt (hh x)
  have hp : fderiv ℝ F 0=0:=ContinuousLinearMap.ext fun i=> (Push.side F (h.differentiableAt (by simp)) i).unique (hz i).2
  have he:=tendsto_nhds_unique (taylor_limit_two (hd x) (hz x).1 (hz x).2.deriv) (hh x); rw [line_second (h.of_le le_top) hp] at he; rw [blade,hp,iter _ _ h]; refine ⟨rfl,?_⟩; linarith
lemma crust (hp:0<r)(x:Cnr n): blade x (barG O.page n) 0=0 ∧ Jacobi.mixed x x (barG O.page n) 0=2*Patch.average (fun s:Signed=>total (Iteration.plain ∘O.page) (flux (Bid.pulled (arm su n 1 x) s))):=zenith (zen (O.cost hp) hp _) _ (small_basis (O.cost hp) hp) x
end Voyage
open Voyage
-- `barG` evaluated at stationary

def litG (P:ℕ→Atom su 2)(i:ℕ)(x:Cnr (V.chain.n i)):= Iteration.action P (encamp (V.port.forest i) (V.port.u i) x).1
lemma identical (F:Avenue V η Ω Θ) {Y X:ℕ→Atom su 2}{i:ℕ}(he: ∀ j ≤2, SameJet j (fun z=> Iteration.action X (liftedTo (V.port.forest i) (V.port.u i) z)) (fun z=> Iteration.action Y (represent z))):
    Duet (litG V X i) (barG Y (V.chain.n i)):=by
  let L: Cnr (V.chain.n i)→ Bid.Dir su (V.chain.n i):= arm su _ 1
  let Z:= (arm su (V.chain.n i) 1).toContinuousLinearMap
  let A:= fun z: Bid.Dir su (V.chain.n i)=> Iteration.action X (liftedTo (V.port.forest i) (V.port.u i) z)
  let B:= fun z: Bid.Dir su (V.chain.n i)=> Iteration.action Y (represent z)
  have hz : Z 0=0:= map_zero _
  have hp : ContDiffAt ℝ ω A (Z 0):=hz.symm ▸ (he 2 le_rfl).1
  have hh : ContDiffAt ℝ ω B (Z 0):=hz.symm ▸ (he 2 le_rfl).2.1
  change Duet (A ∘ Z) (B ∘ Z)
  refine ⟨hp.comp (f:=Z) _ Z.contDiff.contDiffAt,hh.comp (f:=Z) _ Z.contDiff.contDiffAt,?_ ,fun x=>?_,fun x y=>?_⟩
  · rw [Function.comp_apply,Function.comp_apply,map_zero]; have he: iteratedFDeriv ℝ 0 A 0=iteratedFDeriv ℝ 0 B 0:=(he 0 (by omega)).2.2; have hv:= DFunLike.congr_fun he ![]; simpa only [iteratedFDeriv_zero_apply] using hv
  · rw [transfuse _ _ hp,transfuse _ _ hh,hz]; have hk: iteratedFDeriv ℝ 1 A 0=iteratedFDeriv ℝ 1 B 0:=(he 1 (by omega)).2.2; have hV:=DFunLike.congr_fun hk ![Z x]; rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply] at hV; exact hV
  rw [adapt _ _ _ hp,adapt _ _ _ hh,iter _ _ hp,iter _ _ hh,map_zero,show iteratedFDeriv ℝ 2 A 0=_ from (he 2 le_rfl).2.2]
end YM.QCD.Fog
