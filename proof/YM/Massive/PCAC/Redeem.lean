import YM.Massive.PCAC.Passages
/-! # Packing lap/contact identities into actual push with spacetime and rescale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
variable (P:Flight j k)(K:KernelChoices)(h:f.val=c.val*P.L.val) (β w:ℝ)(hk:P.patch.Branches K su)
local notation "S"=> coarse P K h
abbrev qmove (F:ℕ)(U:Grid f): Matrix (Modes c F) (Modes f F) ℂ:= Kit.choir F (Flume.tied P h 0 U)
@[fun_prop] lemma q_cont (F:ℕ): Continuous (qmove P h F):=(Kit.choir_cont (A:=Row c) (B:=Row f) F).comp (Pine.tied_cont ..)
lemma reset_atom (i:Pairs (Modes c F)) : rescale w (atom i)=(w:ℂ) • atom i:=by unfold rescale; rw [change_atom]; simp [Matrix.diagonal_apply,ite_smul]
lemma reset_grade (x:Fields c F): grade (rescale w x)= rescale w (grade x):= exterior_parity _ _
lemma resetD (i:Pairs (Modes c F))(x: Fields c F): vary i (rescale w x)=(w:ℂ) • rescale w (vary i x):=by
   let l(j:Pairs (Modes c F)):= atom j
   have hh(j): vary i (rescale w (l j))= (w:ℂ) • rescale w (vary i (l j)):=by
       by_cases h:i=j
       · subst j; unfold l; rw [reset_atom,map_smul,vary_self,map_one]
       unfold l; rw [reset_atom,map_smul,vary_off i j h,map_zero]
   have H(q:List (Pairs (Modes c F))): vary i (rescale w (q.map l).prod)=(w:ℂ) • rescale w (vary i (q.map l).prod):=by
       induction q with
       | nil=> simp [vary_one]
       | cons j q ih=> simp only [List.map_cons,List.prod_cons,map_mul,vary_mul,hh,ih,reset_grade,smul_mul_assoc,mul_smul_comm,map_add,smul_add] -- hs simp
   have hr(s:Finset (Pairs (Modes c F))): vary i (rescale w (mono s))=(w:ℂ) • rescale w (vary i (mono s)):=by
       obtain ⟨q,hQ,hv,hX⟩:= expression s; rw [hX]; simpa only [l,List.map_ofFn] using H (List.ofFn q)
   rw [←write x]; simp only [map_sum,map_smul,hr,Finset.smul_sum]; exact Finset.sum_congr rfl fun q _=> smul_comm .. -- Finset.smul_sum global
lemma unpair (hw:0 < w)(i j: Modes c F)(x:Fields c F): rescale w (pairD i j x) = (w:ℂ)⁻¹^2 • pairD i j (rescale w x):=by
    have hs:(w:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hw.ne'
    unfold pairD; rw [LinearMap.comp_apply,LinearMap.comp_apply, resetD, map_smul, resetD, ← mul_smul, pow_two, mul_smul, mul_smul]; rw [inv_smul_smul₀ hs,inv_smul_smul₀ hs] -- order
lemma resetMark(b: Bool)(W:Sour (Modes c F))(x:Fields c F) : rescale w (applyMark b W x)= applyMark b W (rescale w x):=by
    have h(i j:Pairs (Modes c F)) : rescale w (gen i j x)=gen i j (rescale w x):=by change rescale _ (atom j*_)=atom j*vary _ _; rw [map_mul,reset_atom,resetD,mul_smul_comm,smul_mul_assoc]
    cases b <;> simp [applyMark,h]
lemma unlap (hw:0<w)(W:Sour (Modes c F))(x:Fields c F): rescale w (lap W x)= (w:ℂ)⁻¹^2 • lap W (rescale w x):=by unfold lap; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,unpair w hw,Finset.smul_sum,smul_comm ((w:ℂ)⁻¹^2)]

def steer (F:ℕ)(U:Grid f)(x:Fields f F): Fields c F:= rescale w (Kit.sheath 1 (qmove P h F U) x)
lemma v_smul (u:ℂ)(U:Grid f)(x:Fields f F): steer P h w F U (u • x)= u • steer P h w F U x:=by unfold steer; rw [show Kit.sheath 1 (qmove P h F U) (u • x)=_ from congr_fun (Transfer.soften_smul P h (fun _=>x) u) U ,Pi.smul_apply,map_smul]; rfl -- defeq
lemma dungeon {X:Grid f→Fields f F}(U:Grid f): steer P h w F U (X U)= rescale w (soften P h X U):=rfl
local notation "Θ"=> prior su f
lemma acrossPush (Z:Fields c F→ₗ[ℂ] Fields c F) (u:ℝ)(x: Fields c F): Z (u • x)=u • Z x:= map_smul (Z.restrictScalars ℝ) ..
-- partner integral
include hk
local notation "toM"=> Transfer.blockMap P K h β w hk
local notation "markX"=> steer P h w F
local notation "lag"=> S
lemma partner (T:Fields c F→ₗ[ℂ] Fields c F)(x:Insertion f F)(V:Grid c) : Integrable (fun U=> ((lag).density β U V) • T (markX U (x U))) Θ ∧ T (toM x V)= ∫ U, ((lag).density β U V) • T (markX U (x U)) ∂Θ:=by
    let μ:=Θ; let A:= S; let Φ(U:Grid f):= (A.density β U V) • soften P h ⇑x U; let T':= T.comp (rescale w (F:=F) (c:=c)).toLinearMap -- shadow F! replace
    let R:= LinearMap.toContinuousLinearMap (T'.restrictScalars ℝ)
    have hi:Integrable Φ μ := StepData.push_slice (Transfer.kernel P K h β hk) V _ (Transfer.soften_pay P h x.continuous)
    have hp : R ∘ Φ = fun U=> (A.density β U V) • T (markX U (x U)):=by funext U; unfold Φ Function.comp; rw [map_smul]; rfl
    rw [show (fun U=> ((lag).density β U V) • T (markX U (x U)))= _ from hp.symm]; exact ⟨R.integrable_comp hi,(R.integral_comp_comm hi).symm⟩
/-- Transfer the point calculations using operator-China, all terms on actual integration. -/
lemma point_transfer {ι: Type*}(s:Finset ι)(T:ι→Fields c F→ₗ[ℂ]Fields c F)(X:Insertion f F)(p:ι→ Insertion f F)(he:∀ i:Grid f, markX i (X i) = ∑ j∈s, T j (markX i (p j i))) (V:Grid c):
    toM X V= ∑ j∈s,T j (toM (p j) V):=by
    rw [show toM _ _= _ from (partner P K h β w hk LinearMap.id X V).2]; simp_rw [LinearMap.id_apply,(fun j=> (partner P K h β w hk (T j) (p j) V).2)]; rw [← integral_finsetSum]; refine integral_congr_ae (Eventually.of_forall fun i=>?_)
    · dsimp only; rw [he,Finset.smul_sum]
    intro j _; exact (partner P K h β w hk (T j) (p j) V).1
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.point_transfer
