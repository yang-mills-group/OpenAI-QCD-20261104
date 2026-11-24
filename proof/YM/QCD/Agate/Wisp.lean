import YM.QCD.Agate.Follower
import YM.Push.BETA_TRANSPORT.Block
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Agate
open Land Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f G K L: Side}{F i j:ℕ}{β t:ℝ} {D Y:Lot}
open Tide Flume YM.Next.Free Kites
-- fallback matrix projector always exists
open Push.BetaTransport
variable {P:Flight i i}{W:KernelChoices} (h:f.val=c.val*P.L.val)
variable {S:StepData c f}
open ContinuousMap
-- direct bound on variation of insertion under beta through joint tags (same fine).
noncomputable def pique (x:Stud c F)(u:ℝ)(V: Grid c):=patternC c F u (x V)
lemma pious : Continuous (fun i:ℝ × Fields c F=> patternC c F i.1 i.2):=by
     apply Grass.continuous_by_coef; intro i; unfold patternC; simp_rw [fundW]; fun_prop
-- finite compact norm portal (avoid definitional issues with concrete product)
lemma blowing {A C: Type} [TopologicalSpace C][PseudoMetricSpace A]{u: Type} [TopologicalSpace u]{p:u} (f:u×C→A)(h:Continuous f)(X:Set C)(hh:IsCompact X):∃ v:u→ℝ, Continuous v∧ v p=0∧∀ i x,x∈X→ dist (f (i,x)) (f (p,x)) ≤ v i:=by
     let T:=fun i:u×X=> f (i.1,i.2.val); letI := isCompact_iff_compactSpace.mp hh
     let P:C(u×X,ℝ):= ⟨fun i=> dist (T i) (f (p,i.2)), by have he:Continuous T:= h.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)); exact he.dist (h.comp (continuous_const.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
     let M:= P.curry; refine ⟨fun i=> ‖M i‖,M.continuous.norm,by change ‖M p‖=0; rw [show M p=0 from ContinuousMap.ext (fun i=> dist_self _),norm_zero],fun i x hx=> ?_⟩; exact (by simpa [Real.norm_eq_abs,abs_of_nonneg dist_nonneg] using (show ‖dist (f (i,x)) (f (p,x))‖ ≤ _ from ContinuousMap.norm_coe_le_norm (M i) ⟨x,hx⟩))
lemma viso {A B:Type}[TopologicalSpace A][CompactSpace A] [NormedAddCommGroup B][NormedSpace ℝ B][ProperSpace B](p:ℝ×A→ℝ)(t:ℝ×B→B)(hp:Continuous p)(ht:Continuous t)(K:ℝ×ℝ)(z:ℝ):∃ v:ℝ×ℝ→ℝ,Continuous v ∧ v K=0∧∀ (q:ℝ×ℝ)(a:A)(w:B), ‖w‖ ≤ z→ ‖p (q.1,a) • t (q.2,w)-p (K.1,a) • t (K.2,w)‖ ≤ v q:=by
     let T:= fun i:(ℝ×ℝ) × (A×B)=> p (i.1.1,i.2.1) • t (i.1.2, i.2.2); have he:Continuous T:=by unfold T; fun_prop
     obtain ⟨v,hv,hH,hx⟩:= blowing (p:=K) T he (Set.univ ×ˢ Metric.closedBall 0 z) (isCompact_univ.prod (isCompact_closedBall ..)); refine ⟨v,hv,hH,fun q a w h=>?_⟩; have H:=hx q (a,w) (show (a,w)∈ Set.univ ×ˢ Metric.closedBall 0 z from ⟨Set.mem_univ _,Metric.mem_closedBall.mpr (by simpa)⟩); rw [dist_eq_norm] at H; exact H
variable (hp:S.patch.Branches S.kernel su)
include hp
lemma dreaming (x: Stud c F)(z:ℝ)(hx:∀ i,‖x i‖ ≤ z)(p:ℝ×ℝ):∃ v:ℝ×ℝ→ℝ,Continuous v∧ v p=0∧∀ (q:ℝ×ℝ)(U: Grid f)(V:Grid c), ‖S.density q.1 U V • stampC x q.2 V - S.density p.1 U V • stampC x p.2 V‖ ≤ v q:=by
    let T:= fun i:(ℝ×ℝ) × ((Grid c × Grid c) × Fields c F)=> S.noise i.1.1 i.2.1.1 i.2.1.2 • patternC c F i.1.2 i.2.2
    obtain ⟨v,hV,hp0,hL⟩:= viso (fun i:ℝ×Grid c×Grid c=> S.noise i.1 i.2.1 i.2.2) _ (noise_cont_all S) (pious (F:=F) (c:=c)) p z; refine ⟨v,hV,hp0,fun q U V=>?_⟩
    let C (a:S.Choices):= S.likelihood U a; let g (a:S.Choices):= ((S.prediction U a,V),x V)
    unfold StepData.density; simp_rw [sum_smul,mul_smul, ← sum_sub_distrib,← smul_sub]; refine (norm_sum_le ..).trans ((sum_le_sum (s:=univ) (g:=fun u:S.Choices=> C u*v q) (fun a _=>?_)).trans_eq ?_)
    · have he:= hL q (g a).1 (x V) (hx V); change ‖C a • (T (q,g a)-T (p,g a))‖ ≤ _; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0≤C a from S.likelihood_pos ..)]; exact mul_le_mul_of_nonneg_left he (S.likelihood_pos ..)
    rw [← sum_mul,show ∑ a:S.Choices,C a=1 from S.chosen hp U,one_mul]
omit hp
variable {Ω:Ultrafilter ℕ}
lemma prof : ∃ M:ℝ,0 ≤ M ∧∀ (U:Grid f)(x:Fields c F), ‖furnace (ater P h U) x‖ ≤ M*‖x‖:=by
    -- shortcut norm op continuous via unit ball
    let A:= Metric.closedBall (0:Fields c F) 1; let S:= fun i:Grid f×Fields c F=> furnace (ater P h i.1) i.2; have hp:Continuous S:= comics _ (grew ..)
    obtain ⟨T,hT⟩:= ((((isCompact_univ.prod (isCompact_closedBall (0:Fields c F) 1)).image hp).image continuous_norm).bddAbove)
    refine ⟨max T 0,le_max_right _ _,fun U x=>?_⟩; by_cases hX:x=0; · simp [hX]
    have hk:= (norm_pos_iff.mpr hX); have H:(‖x‖⁻¹ :ℂ) • x ∈ A:=Metric.mem_closedBall.mpr (by simp [norm_smul,inv_mul_cancel₀ hk.ne']); have he:‖furnace (ater P h U) ((‖x‖⁻¹:ℂ) • x)‖ ≤ max T 0:= (hT ⟨_,⟨(U,_),⟨Set.mem_univ U,H⟩,rfl⟩,rfl⟩).trans (le_max_left ..); rw [map_smul,norm_smul] at he; simp only [norm_inv,Complex.norm_real,norm_norm, mul_comm (‖x‖⁻¹), ← div_eq_mul_inv] at he; exact (div_le_iff₀ hk).mp he
lemma loomed (x:Stud c F)(hx:Tide.Stays x)(M N:ℕ→ℝ)(H:Tendsto M (Ω:Filter ℕ) (𝓝 β))(ht:t≠0)(hy:Tendsto N (Ω:Filter ℕ) (𝓝 t))(hx': P.patch.Branches W su):∃ u:ℕ→ℝ,Tendsto u (Ω:Filter ℕ) (𝓝 0)∧∀ (i:ℕ)(U:Grid f),‖look P W h (M i) (N i) x U-look P W h β t x U‖≤u i:=by
    obtain ⟨z,hz⟩:=hx.bounded; let A:=P.visit W h; let p(i:ℕ):=(M i,(N i)⁻¹); let q:= (β,t⁻¹); obtain ⟨v,hv,K⟩:=prof (F:=F) h; obtain ⟨r,hr,hR,hk⟩:= dreaming (S:=A) hx' x z hz q; refine ⟨fun i=> v*r (p i),?_,?_⟩
    · have hp:Tendsto (fun i=> r (p i)) (Ω:Filter ℕ) (𝓝 (r q)):=((hr.tendsto _).comp (H.prodMk_nhds (hy.inv₀ ht))); simpa only [hR,mul_zero] using hp.const_mul v
    intro i U; unfold look offer; rw [← map_sub]; refine (K U _).trans (mul_le_mul_of_nonneg_left ?_ hv); have he(p:ℝ×ℝ):=deltaPay (S:=A) (β:=p.1) hx' (stampC x p.2) (paysA x hx) U; unfold brook; change ‖ (∫ w,A.density (p i).1 U w • stampC x (p i).2 w ∂prior su c) - (∫ w,A.density q.1 U w • stampC x q.2 w ∂prior su c)‖ ≤ _; rw [← integral_sub (he (p i)) (he q)]; simpa only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using norm_integral_le_of_norm_le_const (ae_of_all (prior su c) (fun V=> hk (p i) U V))
end YM.QCD.Agate
