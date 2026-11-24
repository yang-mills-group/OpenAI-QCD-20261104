import YM.Massive.Filament.Seal
import Mathlib.Analysis.SpecialFunctions.Exponential
/-! # Analytic calculus on priced markers. Separate discipline used only for K (regular E clones
carry degree cards). -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Filament
open Function Filter Complex Metric Finset
open scoped BigOperators Topology ContDiff Classical
variable {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [CompleteSpace E] [CompleteSpace F]
variable (n:ℕ) {p:ℂ→E}{q:ℂ→F}{U:ℂ→ℂ→E}{V:ℂ→ℂ→F}
lemma duo (hf:Holo p)(hg:Holo q): bead n (fun i=> (p i,q i))=(bead n p,bead n q):=by
   let H(i):=(p i,q i); let S:=ContinuousLinearMap.fst ℂ E F; let R:=ContinuousLinearMap.snd ℂ E F; have hh:Holo H:=hf.prodMk hg; exact Prod.ext (handset n S hh zero_lt_one).symm (handset n R hh zero_lt_one).symm
lemma Fused.pair (h:Fused U)(hg:Fused V): Fused (fun z s=> (U z s,V z s)):=by
    obtain ⟨x,hx⟩:=h.linear; obtain ⟨y,hy⟩:=hg.linear
    refine ⟨fun z hz=> (h.lamp z hz).prodMk (hg.lamp z hz), fun s hs=> (h.wire s hs).prodMk (hg.wire s hs), fun s hs=> Prod.ext (h.baseS s hs) (hg.baseS s hs), fun z hz=> Prod.ext (h.base z hz) (hg.base z hz), fun z hz=> ?_, ⟨(x,y), fun z hz=> ?_⟩⟩
    · rw [duo _ (h.lamp z hz) (hg.lamp z hz),h.mute z hz,hg.mute z hz]; rfl
    rw [duo _ (h.lamp z hz) (hg.lamp z hz), hx z hz,hy z hz]; rfl
omit [CompleteSpace E] in
lemma Fused.congr (h:Fused U)(V:ℂ→ℂ→E)(hp:∀ i j:ℂ, ‖i‖<1→ ‖j‖<1 → V i j= U i j): Fused V:=by
    have h₀: ‖(0:ℂ)‖<1:=by simp
    have hx n (z:ℂ)(hz:‖z‖<1): bead n (V z)=bead n (U z):=congr_arg ((n.factorial:ℂ)⁻¹ • ·) (Filter.EventuallyEq.iteratedDeriv_eq _ (Filter.mem_of_superset (ball_mem_nhds _ zero_lt_one) (fun i hi=> hp z i hz (mem_ball_zero_iff.mp hi))))
    obtain ⟨x,hx'⟩:= h.linear
    exact ⟨fun z hz=>(h.lamp z hz).congr fun i hi=> hp z i hz (mem_ball_zero_iff.mp hi), fun s hs=>(h.wire s hs).congr fun i hi=> hp i s (mem_ball_zero_iff.mp hi) hs, fun s hs=>by rw [hp 0 s h₀ hs, hp _ _ h₀ h₀,h.baseS s hs], fun z hz=>by rw [hp z 0 hz h₀,hp _ _ h₀ h₀,h.base z hz], fun z hz=> (hx 1 z hz).trans (h.mute _ hz), ⟨x,fun z hz=>(hx 2 z hz).trans (hx' z hz)⟩⟩
-- Doesn't need C∞ outer b. Hooks E.g. exponent on even subalgebra.
omit [CompleteSpace F] in
lemma Fused.compose (h:Fused U)(g:E→F)(hp:ContDiff ℂ 2 g): Fused (fun z s=> g (U z s)):=by
    have hg := hp.differentiable (by decide)
    let D:=fderiv ℂ g (U 0 0); have hX :∀ z:ℂ, ‖z‖<1→ bead 2 (g ∘ U z)=D (bead 2 (U z)):=by
       intro z hz; have hx:deriv (U z) 0=0:=by rw [← bead_first]; exact h.mute _ hz
       unfold bead
       rw [iteratedDeriv_vcomp_two hp.contDiffAt ((h.lamp z hz).apex 2 zero_lt_one),hx]
       rw [show (iteratedFDeriv ℂ 2 g (U z 0)) (fun _=>0)=0 from ContinuousMultilinearMap.map_coord_zero _ (0:Fin 2) rfl,h.base z hz,zero_add,map_smul]
    obtain ⟨x,hx⟩:= h.linear
    refine ⟨fun z hz=> hg.comp_differentiableOn (h.lamp z hz), fun s hs=> hg.comp_differentiableOn (h.wire s hs),fun s hs=> congr_arg _ (h.baseS s hs), fun z hz=> congr_arg _ (h.base z hz),?_,⟨D x,fun z hz=> (hX z hz).trans ((congr_arg D (hx z hz)).trans (map_smul D _ _))⟩⟩
    intro z hz; have hd: HasDerivAt (U z) (0:E) 0:= by rw [← h.mute z hz,bead_first]; exact ((h.lamp z hz).differentiableAt (ball_mem_nhds 0 zero_lt_one)).hasDerivAt
    rw [bead_first]; exact (((hg (U z 0)).hasFDerivAt.comp_hasDerivAt 0 hd).deriv.trans (map_zero _))
variable [NormedCommRing X][NormedAlgebra ℂ X]
section operations
variable {R P: ℂ→ℂ→X}
omit [CompleteSpace E] in
lemma Fused.steady (c:E): Fused fun _ _=> c:=by refine ⟨fun _ _=>differentiableOn_const _, fun _ _=>differentiableOn_const _, fun _ _=>rfl, fun _ _=>rfl,fun _ _=> ?_, ⟨(0:E), fun _ _=> ?_⟩⟩ <;> simp only [bead_const, if_false, Nat.reduceEqDiff, smul_zero] -- reducer
lemma Fused.plus {V:ℂ→ℂ→E}(hf:Fused U)(hg:Fused V): Fused (fun z s=> U z s + V z s):=(hf.pair hg).compose (fun p=> p.1+p.2) (by fun_prop)
lemma Fused.minus {V:ℂ→ℂ→E}(hf:Fused U)(hg:Fused V): Fused (fun z s=> U z s-V z s):=(hf.pair hg).compose (fun p=>p.1-p.2) (by fun_prop)
lemma Fused.minusC (hf:Fused U): Fused (fun z s=> -U z s):=hf.compose (fun x=> -x) (by fun_prop)
lemma Fused.sigma (Q:ι→ℂ→ℂ→E)(B:Finset ι) (h:∀ i∈B,Fused (Q i)): Fused (fun z s=>∑ i∈B,Q i z s):=by
    induction B using Finset.induction_on with
    | empty=> simpa only [sum_empty] using (Fused.steady (0:E))
    | insert i B hi ih=> simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).plus (ih fun j hj=>h j (mem_insert_of_mem hj))
variable [CompleteSpace X]
lemma Fused.times (hf:Fused R)(hg:Fused P): Fused (fun z s=> R z s*P z s):= (hf.pair hg).compose (fun p=>p.1*p.2) (by fun_prop)
lemma Fused.multiple (Q:ι→ℂ→ℂ→X)(B:Finset ι)(h:∀ i∈B,Fused (Q i)): Fused (fun z s=>∏ i∈B,Q i z s):=by
    induction B using Finset.induction_on with
    | empty=> simpa only [prod_empty] using (Fused.steady (1:X))
    | insert i B hi ih=> simp_rw [prod_insert hi]; exact (h i (mem_insert_self ..)).times (ih fun j hj=>h j (mem_insert_of_mem hj))
lemma Fused.exponential [NormedAlgebra ℚ X] (hf:Fused R): Fused (fun z s=> NormedSpace.exp (R z s)):= hf.compose NormedSpace.exp (contDiff_iff_contDiffAt.mpr fun _=> (NormedSpace.exp_analytic ..).contDiffAt)
omit [CompleteSpace E] in
lemma Fused.code (x:E) (n r:ℕ) (h:(n=0∧r=0)∨ (n=1∧ r=2)∨(0<n∧3≤ r)): Fused (fun z s:ℂ=> s^r • z^n • x):=by
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩|⟨hn,hr⟩
    · simp only [pow_zero,one_smul]; exact steady _
    · exact ⟨fun _ _=>by unfold Holo; fun_prop, fun _ _=>by unfold Holo; fun_prop,fun s h=>by simp,fun s h=>by simp,fun z h=>by rw [bead_mono, if_neg (by decide)], ⟨x,fun z h=>by rw [bead_mono,if_pos rfl,pow_one]⟩⟩
    exact ⟨fun _ _=>by unfold Holo; fun_prop, fun _ _=>by unfold Holo; fun_prop,fun s h=>by simp [hn.ne'],fun s h=>by simp [zero_pow (by omega : r≠0)], fun z h=>by rw [bead_mono, if_neg (by omega)], ⟨0,fun z h=>by rw [bead_mono,if_neg (by omega),smul_zero]⟩⟩
end operations

section sums
variable {Q:ι→ℂ→E} {P:ι→ℂ→ℂ→E}{u:ι→ℝ}{z:ℂ}
lemma Holo.iter (hf:Holo p): Holo (iteratedDeriv n p):=by
    induction n with |zero=>rwa [iteratedDeriv_zero]| succ n ih=>rw [iteratedDeriv_succ]; exact ih.deriv isOpen_ball
lemma Holo.all (h:∀ i,Holo (Q i)) (hu:Summable u)(hb:∀ i z, ‖z‖<1→‖Q i z‖≤u i): HasSum (fun i=>bead n (Q i)) (bead n (fun z=>∑' i,Q i z)):=by
    let f:=(fun z=> ∑' i,Q i z); let H(t:Finset ι)(z):=∑ i∈t,Q i z
    have hW t:Holo (H t):=DifferentiableOn.fun_sum fun i _=>h i
    have hv:TendstoLocallyUniformlyOn H f atTop (ball 0 1):=(tendstoUniformlyOn_tsum hu fun i z (hz:z∈ball 0 1)=>hb i z (mem_ball_zero_iff.mp hz)).tendstoLocallyUniformlyOn
    have hh :TendstoLocallyUniformlyOn (fun i=>iteratedDeriv n (H i)) (iteratedDeriv n f) atTop (ball 0 1):=by
        induction n with
        | zero=> simpa only [iteratedDeriv_zero]
        | succ n ih=> simp_rw [iteratedDeriv_succ]; exact ih.deriv (Eventually.of_forall fun i=> (hW i).iter n) isOpen_ball
    have hx:= hh.tendsto_at (mem_ball_self zero_lt_one)
    have h1 : HasSum (fun i=>iteratedDeriv n (Q i) 0) (iteratedDeriv n f 0):= by apply hx.congr'; filter_upwards with t; exact iteratedDeriv_fun_sum fun i _=> (h i).apex _ zero_lt_one
    exact h1.const_smul _
lemma Fused.roll (hp:∀ i,Fused (P i))(hu:Summable u)(hb:∀ i (z s:ℂ), ‖z‖<1→‖s‖<1→‖P i z s‖≤u i): Fused (fun z s=> ∑' i,P i z s):=by
    let F z s:= ∑' i,P i z s
    have h (n:ℕ) (z:ℂ)(hz:‖z‖<1): HasSum (fun i=>bead n (P i z)) (bead n (F z)) := Holo.all n (fun i=>(hp i).lamp z hz) hu (fun i s hs=>hb i z s hz hs)
    let d:ℂ:=2⁻¹; have h₁:‖d‖<1:=by norm_num [d]
    have hm(i) (z:ℂ)(hz:‖z‖<1): bead 2 (P i z)= (2*z) • bead 2 (P i d):=by
         obtain ⟨x,hx⟩:= (hp i).linear; rw [hx _ hz,hx d h₁,smul_smul,show 2*z*d=z from (by unfold d; ring)]
    refine ⟨?lamp,?wire,(fun s hs=>tsum_congr fun i=> (hp i).baseS s hs), (fun z hz=>tsum_congr fun i=> (hp i).base z hz), (fun z hz=> (h 1 z hz).unique (hasSum_zero.congr_fun (fun i=> (hp i).mute z hz))), ⟨(2:ℂ) • bead 2 (F d),fun z hz=>?_⟩⟩
    case lamp=> intro z hz; exact Complex.differentiableOn_tsum_of_summable_norm hu (fun i=> (hp i).lamp z hz) isOpen_ball fun i s hs=> hb i z s hz (mem_ball_zero_iff.mp hs)
    case wire=> intro s hs; exact Complex.differentiableOn_tsum_of_summable_norm hu (fun i=> (hp i).wire s hs) isOpen_ball fun i z hz=> hb i z s (mem_ball_zero_iff.mp hz) hs
    rw [smul_smul,mul_comm]; exact (h 2 z hz).unique (((h 2 d h₁).const_smul _).congr_fun fun i=> hm _ _ hz)
end sums
end YM.Massive.Filament
#print axioms YM.Massive.Filament.Fused.compose
#print axioms YM.Massive.Filament.Fused.exponential
#print axioms YM.Massive.Filament.Fused.roll
