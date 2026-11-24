import YM.Poised.Costs
/-! # Intrinsic coordinate costs. Uniform bounds, arbitrary moment costs permissible
    (checkout per order, power) -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Display Papyrus MassiveQCD.Plate QCD.Kites
variable {c : Side} {d k n : ℕ}
namespace Sieve
open Beacon Next.Foundations Costs
variable (H:TaperHol)(c:Side)(b:Cover)
local notation "Ψ"=>Lat.Fields c 6
local notation "Z"=> SpinPol d
local notation "N"=> Pairs (SpinMode d)
local notation "Ω"=> SpinMode d
variable (θ v:ℝ)
-- grades. operations spin
noncomputable abbrev life (p:Powers):ℕ:= ∑ i∈p.support,p i
noncomputable def widths : Pol d→ₗ[ℂ]Pol d:= (zBasis d).constr ℂ (fun p=> ((θ:ℂ)^life p.1*(v:ℂ)^p.2.card) • gen p)
-- threshold grade diag arbitrary, not assumed basis-invariance
lemma widths_m (p:PowerPair d): widths θ v (gen p)= ( (θ:ℂ)^life p.1*(v:ℂ)^p.2.card) • gen p:=by nth_rw 1 [← minted p]; exact Module.Basis.constr_basis ..
private lemma stripe_d (p:GPol)(m:Powers)(J:Labels.Jet su): Labels.read (θ • J) (MvPolynomial.monomial m 1)= (θ:ℂ)^life m*Labels.read J (MvPolynomial.monomial m 1):=by
    simp only [Labels.read,MvPolynomial.aeval_monomial, Algebra.algebraMap_self,RingHom.id_apply,one_mul, Finsupp.prod]
    have he i: Labels.coord (θ • J) i=(θ:ℂ)*Labels.coord J i:=by simp [Labels.coord]
    simp_rw [he,mul_pow, Finset.prod_mul_distrib, prod_pow_eq_pow_sum]
lemma countingG (J:Labels.Jet su)(x:Pol d)(h:ℝ): observation d J h (widths θ v x)=engine v N (observation d (θ • J) h x):=by
    let q:=observation d J h; refine DFunLike.congr_fun (f:=q.comp (widths θ v)) (g:= (engine v N).toLinearMap.comp (observation d (θ • J) h)) ?_ x
    apply (zBasis d).ext; intro i; rw [minted]; change q (widths θ v (gen i))=engine v N (observation d _ _ _); rw [widths_m, map_smul, gen_value]; rw [gen_value,gen,ready_t,ready_t,stripe_d θ 0, map_smul,map_smul,nominate (mono _) v _ (Grass.homogeneous _)]
    simp_rw [smul_smul]; ring_nf -- ring handles module structure?
lemma sizes_cap(x:Pol d)(h:x∈UV.cap d): widths θ v x∈UV.cap d:=by
    apply Submodule.span_induction (p:=fun x _=> widths θ v x∈UV.cap d) ?_ ?_ ?_ ?_ h
    · rintro _ ⟨i,hi,rfl⟩; rw [widths_m]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_,hi,rfl⟩)
    · simp
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    intro u x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx
lemma colorWidth (p:su.El)(x:Pol d): colorAct p (widths θ v x)=widths θ v (colorAct p x):=by
   apply distinct; intro J; rw [← one_scene, lamp_obs,countingG,countingG, lamp_obs,show Labels.colored p (θ • J)=θ • Labels.colored p J from funext fun i=>map_smul (Labels.Taylor.paint p) θ (J i)]; exact ridesB v _ _
def dimming (d:ℕ): Label d→ₗ[ℂ] Label d:= { toFun:=fun x=>⟨widths θ v x.val,(label_law _).mpr ⟨ sizes_cap θ v _ ((label_law _).1 x.property).1,fun u=>by rw [colorWidth, ((label_law _).1 x.property).2]⟩⟩, map_add':=fun x y=>Subtype.ext (map_add _ _ _), map_smul':=fun z y=>Subtype.ext (map_smul _ _ _) }
lemma stage_count (x: Grid c→Ψ)(J:Labels.Jet su)(h:ℝ): endor h (producing H c b (d:=d) x v J h)= engine v N (moment (d:=d) H b J x h):=by rw [splitD]; exact ridesB v _ _
variable {θ v}
lemma voices (x: Grid c→Ψ)(J:Labels.Jet su)(h:ℝ): endor h (producing H c b (d:=d) x v J h)= ∑ i:Finset N, coef i (producing H c b x v J h) • ((h:ℂ)^sky i • mono i):=by
    conv_lhs=>rw [← write (producing (d:=d) H c b x v J h),map_sum]
    simp_rw [map_smul,pieces]
lemma composed (P:BudgetPoint) (x: Grid c→Ψ)(u: Pol d) (h:ActionTest H b x u) (hc: ContDiffAt ℝ (d : WithTop ℕ∞) (x∘increment 1) 0): ∀ J:Labels.Jet su,let Z':= producing H c b (d:=d) x θ (v • J); ContDiffAt ℝ d Z' 0 ∧ ∀ j≤d, iteratedDeriv j (observation d J · (widths v θ u)) 0=iteratedDeriv j (fun t=> endor t (Z' t)) 0 :=by
    intro J Q; let S:= engine θ N; let L:= (S.toLinearMap.restrictScalars ℝ).toContinuousLinearMap; let K:=v • J; refine ⟨?_,fun j hj=>?_⟩
    · let Y:=core H b x d; have hy:ContDiffAt ℝ d (Y∘scaledD d K) 0 := (show ContDiffAt ℝ d Y (scaledD d K 0) from (scaled_zero d K).symm ▸ core_smooth H b x hc).comp (0:ℝ) (scaled_smooth d K)
      exact L.contDiff.contDiffAt.comp _ hy
    change _= iteratedDeriv j (fun t=> endor t (producing H c b x θ (v • J) t)) 0; simp_rw [stage_count,countingG,observe]; have he:=h K
    change iteratedDeriv j (L∘desired u K) 0 = iteratedDeriv j (L∘moment H b K x) 0; rw [clm_step _ _ _ (he.2.1.of_le ?_), clm_step _ _ _ (he.1.of_le ?_),he.2.2 j hj] <;> exact_mod_cast hj
-- pick arbitrary coefficient frame via finite-dim.Later pure basis enrich
open Module
abbrev Fog (d:ℕ) := Fin (Module.finrank ℂ (Label d))
variable (F₀: Basis (Fog d) ℂ (Label d)) (p:Label d)
def cose : (Fog d→ℂ):=F₀.equivFun p
local notation "Q"=> Fog d→ℂ
def watch (θ v:ℝ):ℝ:= ‖cose F₀ (dimming θ v d p)‖
-- scalar projections detect via `ready` after trunc. Bounds by budgets.V. avoids family sum norm in derivative m.Brush
lemma boost (d j : ℕ): ∃ A : ℝ,0 ≤ A ∧ ∀ {f : ℝ→ SpinPol d}, ContDiffAt ℝ j f 0→ ∀ C:ℝ,0≤C→ (∀ i≤j, ‖iteratedDeriv i f 0‖≤C) → ‖iteratedDeriv j (fun t=> endor t (f t)) 0‖≤A*C:=by
   -- continuous bilinear process and polarization. easy component Leibniz
   let X:= SpinPol d
   let G:=Pairs (SpinMode d)
   let Y(X:Type)[Fintype X][DecidableEq X](s:Finset X):ℂ→L[ℝ]Alg X:= (((LinearMap.toSpanSingleton ℂ (Alg X) (Grass.mono s)).restrictScalars ℝ).toContinuousLinearMap)
   let B(i:Finset G):ℂ→L[ℝ]SpinPol d:= Y G i
   -- component tally
   let S (i:Finset G):ℝ→ℂ:=fun t=>(t:ℂ)^sky i
   let T (i:Finset G):X→L[ℝ]ℂ:= ((coef i).restrictScalars ℝ).toContinuousLinearMap
   let K(i:Finset G) (k:ℕ):ℝ:=(j.choose k:ℝ)*(‖T i‖*‖iteratedDeriv (j-k) (S i) 0‖)
   let W(i:Finset G):ℝ:=∑ k∈Finset.range (j+1), K i k
   have hW i:0≤ W i:=sum_nonneg fun _ _=> by unfold K; positivity
   refine ⟨∑ i:Finset G, ‖B i‖*W i, sum_nonneg (fun _ _=>mul_nonneg (norm_nonneg _) (hW _)),?_⟩
   intro f h C hc hf
   let v(i:Finset G):= T i ∘ f
   have hs(i:Finset G):ContDiffAt ℝ j (S i) 0:= Complex.ofRealCLM.contDiff.contDiffAt.pow _
   have hV(i:Finset G):ContDiffAt ℝ j (v i) 0:= (T i).contDiff.contDiffAt.comp _ h
   have hz(i:Finset G): ‖iteratedDeriv j (v i*S i) 0‖ ≤ W i*C :=by
      change ‖iteratedDeriv j (fun t=> v i t*S i t) 0‖≤_; rw [iteratedDeriv_fun_mul (hV i) (hs i)]; apply (norm_sum_le ..).trans; unfold W; rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro k hk'
      have hk:k≤j:=by simpa using hk'
      have ht:‖iteratedDeriv k (v i) 0‖ ≤ ‖T i‖*C:=by unfold v; rw [clm_step _ _ _ (h.of_le ?_)]; exact ((T i).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hf k hk) (norm_nonneg _)); exact_mod_cast hk
      rw [norm_mul,norm_mul,Complex.norm_natCast,mul_assoc]
      apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (norm_nonneg _)) (by positivity)); unfold K; exact le_of_eq (by ring)
   have he(t:ℝ): endor t (f t)=∑ i:Finset G,(B i ∘ (v i*S i)) t:=by
      conv_lhs=>rw [← write (f t),map_sum]
      refine Finset.sum_congr rfl fun i _=> ?_; rw [map_smul,pieces]; change _= (coef i (f t)*(t:ℂ)^sky i) • mono i; rw [smul_smul]
   rw [funext he,iteratedDeriv_fun_sum (fun i _=> (B i).contDiff.contDiffAt.comp (f:=v i * S i) _ ((hV i).mul (hs i))),Finset.sum_mul]
   apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun i _=>?_ ; rw [clm_step (v i*S i) j _ ((hV i).mul (hs i)) (B i)]; exact ((B i).le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hz i) (norm_nonneg _)).trans_eq (mul_assoc ..).symm)
lemma priceAll (j:ℕ)(hj:j≤d)(J:Labels.Jet su): ∃ C:ℝ, 0≤C ∧ ∀ (H:TaperHol) (c:Side)(b:Cover)(P:BudgetPoint)(x:Grid c→Lat.Fields c 6)(u:Label d)(r v:ℝ)(k:ℕ)(D:Support c), Sight D (wrap c b) k P v x r → surface d ≤ k → d≤P.order → d*d≤P.power → 0 ≤ v → ActionTest H b x u.val → ‖iteratedDeriv j (observation d J · (dimming P.threshold v d u).val) 0‖ ≤ C*r:=by
   choose C hc hC using fun i:Fin (d+1)=>curvatureW d i.val J (Nat.le_of_lt_succ i.isLt)
   let W:=∑ i,C i; have hW:0≤W:= Finset.sum_nonneg fun _ _=>hc _
   obtain ⟨A,hA,hE⟩:= boost d j; refine ⟨A*W,mul_nonneg hA hW,fun H c b P x u r v k D h hs ho hp ht he=>?_⟩
   have hy: ContDiffAt ℝ d (x∘increment 1) 0:= (h.use 1 (one_healthy _ _ P.threshold_pos.le)).of_le (by exact_mod_cast ho)
   have hv:= composed (θ:=v) (v:=P.threshold) H c b P x u.val he hy J
   change ‖iteratedDeriv j (observation d J · (widths P.threshold v u.val)) 0‖ ≤ _; rw [hv.2 j hj]; apply (hE (hv.1.of_le (by exact_mod_cast hj)) (W*r) (mul_nonneg hW h.travels) ?_).trans_eq (mul_assoc ..).symm
   intro i hi; let z:Fin (d+1):= ⟨i,Nat.lt_succ_of_le (hi.trans hj)⟩; exact (hC z H c b k P v x r D h hs ho hp ht).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=C) (fun _ _=>hc _) (mem_univ z)) h.travels)
abbrev Field(d:ℕ):= SpinPol d
lemma pricedW : ∃ C:ℝ,0≤C ∧ ∀ (H:TaperHol) (c:Side)(b:Cover)(P:BudgetPoint)(x:Grid c→Lat.Fields c 6)(u:Label d)(r v:ℝ)(k:ℕ)(D:Support c), Sight D (wrap c b) k P v x r → surface d ≤ k → d≤P.order → d*d≤P.power → 0 ≤ v → ActionTest H b x u.val → watch F₀ u P.threshold v ≤ C*r:=by
    choose C hc hC using fun (i:Labels.Jet su × Fin (d+1))=> priceAll i.2.val (Nat.le_of_lt_succ i.2.isLt) i.1
    let p (i:Labels.Jet su × Fin (d+1)) : (Fog d→ℂ) →L[ℝ] SpinPol d:= LinearMap.toContinuousLinearMap (((i.2.val.factorial:ℂ) • ((ready d i.1).comp ((geometry i.2.val).comp ((labels d).subtype.comp (F₀.equivFun.symm).toLinearMap)))).restrictScalars ℝ)
    have he (i)(x:Label d): iteratedDeriv i.2.val (observation d i.1 · x.val) 0=p i (cose F₀ x):=by
       unfold cose; rw [order_test]; change _= (i.2.val.factorial:ℂ) • ready _ _ (geometry _ (F₀.equivFun.symm _).val); rw [F₀.equivFun.symm_apply_apply]
    have hv(x)(h:∀ i,p i x=0): x=0:=by
       let u:=F₀.equivFun.symm x; have hx:cose F₀ u=x:=F₀.equivFun.apply_symm_apply _; have ht:= (label_law _).1 u.property; suffices hf:u=0 by rw [← hx,hf]; exact map_zero _
       refine Subtype.ext (Display.unique u.val (0:Pol d) ht.1 (Submodule.zero_mem _) ?_); intro J; rw [← funext (observe _ _), ← funext (observe _ _)]; refine ⟨(painted _ _ _).contDiffAt,(painted _ _ _).contDiffAt,fun k hk=>?_⟩
       let I:Labels.Jet su × Fin (d+1):= (J,⟨k,Nat.lt_succ_of_le hk⟩); rw [order_test (0:Pol d), map_zero,map_zero,smul_zero]; exact (he I u).trans (hx ▸ h I)
    obtain ⟨A,ha,H⟩:=budget_probes p hv C hc; exact ⟨A,ha.le,fun K c b P x u r v k D h hs ho hp ht he'=> H _ h.travels _ (fun i=>by rw [← he]; exact hC i K c b P x u r v k D h hs ho hp ht he')⟩
end Sieve
end YM.Massive.Poised
