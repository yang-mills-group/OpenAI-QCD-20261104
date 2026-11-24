import YM.QCD.Acre.Horse
import YM.Next.FOUNDATIONS.Primary
/-! # trajectory stations: fixed ratio. period mesh at every rung. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft
open Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {j t k i l n N: ℕ}{K:KernelChoices}{q: Clip}{E:Patch}{σ η Ω A γ β b C D u v x y W:ℝ}{p:ChartRatio su}{M:ℕ→ Bed}{T:ℕ→Towers E.L}
variable {F L:Side→ℝ}{Λ Γ r c:ℝ}
open Ride Flume YM.Next.Foundations
abbrev passportM (j:ℕ)(hj:4 ≤ j):Plan j:= Classical.choice (passport (by omega))
-- Order P fixed before Plateau
lemma attachedM (K:KernelChoices)(O:ChartRatio su)(ho:LocalRatio O)(j:ℕ)(hj:4≤j) : ∃ (σ η Ω u v D γ:ℝ)(q:Clip),0<σ∧0<η∧1≤Ω∧0<u∧0≤v∧0≤D∧q.direct ≤ 1∧ 0<γ∧∃ L:ℕ,∀ E:Patch,E.J=j→ E.Branches K su→L≤ E.L.val → ∃ (M:ℕ→Bed)(T:ℕ→Towers E.L)(Λ c Γ W:ℝ) (Z:ParcelR), Soil K q E σ η Ω M T∧1 ≤ Λ∧0<c∧1 ≤ Γ∧ReadyR Z (passportM E.J E.order_cut) E K q u v σ Ω Ω∧ Cumulative (passportM E.J E.order_cut) E K q Z u v σ Ω Ω W∧∀ N (S:SparkMesh), reachM E S→ ∃ (R:Ride K q E u v S N),Ingress R O M T c Γ γ D Λ :=by
  obtain ⟨p,hp,s,e,a,h,hη,hA,n,H⟩:= sustain K j hj
  obtain ⟨r,b,d,x,hu,hv,hh,hP,ht,u,hF,hL,Y⟩:= sprouts K p j hp h hη hA
  obtain ⟨L,HE⟩:= issuesG (passportM j hj) hj h (zero_le_one.trans hA) (zero_le_one.trans hA)
  refine ⟨s,e,a,r,b,d,x,p,h,hη,hA,hu,hv,hh,hp,hP,max n (max L u),fun E Hs H' hc=>?_⟩
  subst j
  obtain ⟨M,T,A⟩:= H E rfl ((le_max_left ..).trans hc)
  obtain ⟨c,hc',hm⟩:= embarkM A Y ho H' ((le_max_right ..).trans ((le_max_right ..).trans hc)) hη ht
  obtain ⟨P⟩:= Push.Uniform.pre_order su r b E.J K (le_refl 3)
  obtain ⟨Z,W,Z',hZ⟩:= HE E ((le_max_left ..).trans ((le_max_right ..).trans hc)) K p r b _ P
  refine ⟨M,T,max 1 (hL E.L),c,max 1 (hF E.L),W,Z,A,le_max_left ..,hc',le_max_left ..,Z',hZ,fun N S h=> hm N S _ _ (le_max_left ..) (le_max_right ..) h (le_max_right ..)⟩
lemma issuedM (O:ChartRatio su)(ho:LocalRatio O)(K:KernelChoices)(hj:4 ≤ j):∃ (σ η Ω u v D γ:ℝ)(q:Clip),0<σ∧0<η∧1≤Ω∧0<u∧0≤v∧0≤D∧q.direct ≤ 1∧ 0<γ∧∃ L:ℕ,∀ E:Patch,E.J=j→E.Branches K su→L ≤E.L.val→
    (∀ f:ℕ,f≤16 → 4*(D+1) ≤ betaQ f *Real.log E.L.val)∧∃ (M:ℕ→Bed)(T:ℕ→Towers E.L)(Λ c Γ W:ℝ) (Z:ParcelR), Soil K q E σ η Ω M T∧1 ≤ Λ∧0<c∧1 ≤ Γ∧ReadyR Z (passportM E.J E.order_cut) E K q u v σ Ω Ω∧ Cumulative (passportM E.J E.order_cut) E K q Z u v σ Ω Ω W∧∀ N (S:SparkMesh), reachM E S→ ∃ (R:Ride K q E u v S N),Ingress R O M T c Γ γ D Λ:=by
  obtain ⟨σ,η,Ω,u,v,D,γ,Z,ht,hv,hH,hA,hD,hC,hB,hY,n,G⟩:=attachedM K O ho j hj
  have hz : Tendsto (fun i:ℕ=> betaQ 16* Real.log (i:ℝ)) atTop atTop := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop ((ultraviolet 16).2 le_rfl)
  obtain ⟨t,hT⟩:= eventually_atTop.1 (hz.eventually_ge_atTop (4*(D+1)))
  refine ⟨σ,η,Ω,u,v,D,γ,Z,ht,hv,hH,hA,hD,hC,hB,hY,max n t,fun E HE h H=>⟨fun f hf=> ?_,G E HE h ((le_max_left ..).trans H)⟩⟩
  have HH:= (le_max_right ..).trans H
  apply (hT E.L.val HH).trans; have he: 0 ≤ Real.log (E.L.val:ℝ):=Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt E.L.pos)
  change _*Real.log _ ≤ _* Real.log _; apply mul_le_mul_of_nonneg_right _ he; rw [qbeta,qbeta]; gcongr
-- Mesh even deployment
lemma meshBirth (n:Side):∃ S:SparkMesh,S.n 0=n ∧ ∀ i,n.val ≤(S.n i).val:=by
  let S :SparkMesh :={ n:= fun i=> n*(3:Side)^i
                       cofinal:=by
                         have he:= tendsto_pow_atTop_atTop_of_one_lt (by decide : (1:ℕ)<3)
                         apply tendsto_atTop_mono _ he; intro i; simp; have hi := n.pos; exact hi
                       ratio:=fun i j=> 3^(j-i)
                       factor:= by intro i j he; simp; rw [mul_assoc,← pow_add, Nat.add_sub_of_le he] -- arithmetic
                       parity:= fun i j _=>Odd.pow (by decide) }
  refine ⟨S,?_,fun i=>?_⟩; · simp [S]
  dsimp [S]; simp; exact one_le_pow₀ (by decide)
lemma road_ready (S: SparkMesh)(K:KernelChoices)(E:Patch)(H: reachM E S)(he:Even (S.n 0).val)(N i n:ℕ):Even (((footM E S N i).n n).val) :=by
  have hi : Even (S.n n).val:= by rw [S.factor 0 n (by omega)]; exact he.mul_right _
  unfold footM climbM; induction (N-i) with
  | zero=> exact hi
  | succ k ih=> rw [iterate_succ_apply']; apply Even.mul_right ih
end YM.QCD.Acre
