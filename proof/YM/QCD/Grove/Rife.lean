import YM.QCD.Grove.Dock
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type*}[Fintype I][Fintype J]{c f:Side}{N n:ℕ}
section bags
variable {T:Type*}{p:I→V}{s:J→T}
open scoped ComplexConjugate
lemma clocks [DecidableEq V](x:V)(i:Finset I)(u:ℝ): ∏ k∈i, ((if p k=x then u else 1:ℝ):ℂ)=(u:ℂ)^held p x i:=by classical -- two dec prob
  simp only [Complex.ofReal_one,apply_ite]; simp_rw [← prod_filter]; rw [prod_const]; rfl
lemma waive [DecidableEq V] [DecidableEq T] (M:Matrix I J ℂ) (x: V)(y:T)(Z:Finset I)(h: ∀ i∈ Z,∀ j,M i j≠0→ (p i=x↔s j=y)) (i:Alg I)(ht:i∈region Z): poker s y (changeVars M i)= changeVars M (poker p x i):=by
    let v (k:I):ℝ:= if p k=x then 2 else 1; let w (k:J):ℝ:= if s k=y then 2 else 1
    let W:=changeVars (Matrix.diagonal (fun i:J=>(w i:ℂ))); let Q:= changeVars (Matrix.diagonal (fun i:I=>(v i:ℂ))); let F:= changeVars M
    have hx : ∀ a:Finset I,a⊆ Z → W (F (mono a))= F (Q (mono a)):=by
       intro a ha; obtain ⟨u,-,hf,H⟩:=Grass.expression a
       have hk (k:I)(hp:k∈ Z):W (F (atom k))=F (Q (atom k)):=by
          have he (z:J): W (atom z)=(w z:ℂ) • atom z:=by unfold W; rw [change_atom]; simp only [Matrix.diagonal_apply,ite_smul,zero_smul,Fintype.sum_ite_eq]
          have hh:Q (atom k)= (v k:ℂ) • atom k:=by unfold Q; rw [change_atom]; simp only [Matrix.diagonal_apply,ite_smul,zero_smul,Fintype.sum_ite_eq]
          unfold F; rw [hh,map_smul,change_atom,map_sum, Finset.smul_sum]; refine sum_congr rfl fun j _=>?_ ; rw [map_smul,he,smul_smul,smul_smul]; by_cases H:M k j=0; · simp [H]
          rw [show w j = v k from ite_congr (propext (h k hp j H|>.symm)) (fun _=>rfl) (fun _=>rfl),mul_comm]
       rw [H]; -- induction List
       let L:= List.ofFn u
       have hv:(List.ofFn (atom ∘ u)).prod=(L.map atom).prod:=by simp [L]
       rw [hv]; have hQ:∀ i∈ L,i ∈ Z:=fun i hi=> ha ((hf i).2 (List.mem_ofFn.mp hi)) -- sig
       suffices h :∀ L:List I,(∀ i∈ L,i∈Z)→ W (F (L.map atom).prod)=F (Q (L.map atom).prod) from h L hQ
       intro L; induction L with
          | nil=> simp
          | cons l L ih=> intro h; simp only [List.map_cons,List.prod_cons,map_mul]; rw [hk l (h _ (by simp)),ih (fun i hi=>h i (List.mem_cons_of_mem _ hi))]
    have hn i (he:i ⊆ Z) : poker s y (F (mono i)) = ((vote p x i:ℝ):ℂ) • F (mono i):=by
       apply (blades J).ext_elem; intro j; change coef j _=coef j _; rw [gateB,map_smul,smul_eq_mul]; by_cases hh:coef j (F (mono i))=0; · rw [hh,mul_zero,mul_zero]
       have hm:j.card=i.card:= by by_contra h; exact hh (Grass.spectrum (Grass.exterior_layer _ (Grass.homogeneous i)) j h)
       have hK:= congr_arg (coef j) (hx i he)
       change coef j (wscale w _)=coef j _ at hK; rw [show Q (mono i)=(∏ k∈i,(v k:ℂ)) • _ from wscale_mono v i,map_smul,map_smul, waxG] at hK
       have hK':(∏ k∈j,(w k:ℂ))=∏ k∈i,(v k:ℂ):=mul_right_cancel₀ hh hK
       have hL := clocks (p:=s) y j 2; have hf := clocks (p:=p) x i 2
       have hy:(↑(2:ℝ):ℂ)^held s y j=(↑(2:ℝ):ℂ)^held p x i:=hL.symm.trans (hK'.trans hf)
       have hz:held s y j=held p x i:= StrictMono.injective (pow_right_strictMono₀ (show 1<(2:ℝ) from one_lt_two)) (Complex.ofReal_injective (by simpa only [Complex.ofReal_pow] using hy))
       unfold vote; rw [hm,hz]
    change poker s y (F i)= F _; conv=> lhs; rw [← write i]; conv=>skip
    conv_rhs=> rw [← write i]
    simp_rw [map_sum,map_smul]; refine sum_congr rfl fun j hj=>?_ ; by_cases H:j⊆ Z; · rw [hn j H, accentP,map_smul]
    rw [ember i ht j H,zero_smul,zero_smul]
lemma salute [DecidableEq V](x:V) (i:Alg I): cc (poker p x i)=poker p x (cc i):=by rw [← write i,map_sum,map_sum,map_sum,map_sum]; simp_rw [map_smul,map_smulₛₗ,accentP,map_smulₛₗ,cc_mono,accentP]; simp
end bags
variable (x:Site c)
include x
noncomputable def buds (N:ℕ): EvenA c N→L[ℝ] EvenA c N := ContinuousLinearMap.restrictScalars ℝ (LinearMap.toContinuousLinearMap (𝕜:=ℂ) (F':=EvenA c N) { toFun:=fun i:EvenA c N=>⟨poker locationP x i.val,keep_plus locationP x i.val i.property⟩, map_add':=fun i j=> Subtype.ext (map_add (poker locationP x) i.val j.val), map_smul':=fun k i=>Subtype.ext (map_smul (poker locationP x) k i.val)}) -- edit
local notation "L"=>EvenA c N
lemma green (U:Support c)(A:L)(hx:Gated U A):Gated U (buds x N A):=poker_mem locationP x A.val _ hx
lemma sprout (U:Support c)(A:L)(hx:Gated U A)(hp:x∉ U): buds x N A=0:=Subtype.ext (waiving locationP x (limits U) (fun i hi h=>hp (h ▸ (mem_filter.mp hi).2)) A.val hx)
open Flume
lemma corporation (A:L)(t:ℝ)(h:0<t): ‖token c N t (buds x N A)‖≤ ‖token c N t A‖:=bottled locationP x (fun _=>t) (fun _=>h) A.val
omit x in
lemma sourcesR (x:EvenA c N): x= Port.sparkF c N (mud x)+∑ i: Site c,buds i N x:=by
    apply Subtype.ext; change _=(Cove.light _ (Port.sparkF c N _+_)); rw [map_add,map_sum]; exact scoreB locationP x.val
lemma scalesR (a:ℝ): buds x N (baker c N a)=0:=sprout x ∅ (baker c N a) (by rw [gets]; refine Territory.club _ _ _ ?_; unfold Gated; rw [map_one]; exact Subalgebra.one_mem _) (notMem_empty _)
end YM.QCD.Grove
