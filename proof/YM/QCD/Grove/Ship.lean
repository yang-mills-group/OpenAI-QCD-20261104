import YM.QCD.Grove.Chrome
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type*}[Fintype I][Fintype J]{c f:Side}{N n:ℕ}
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
-- right inverse of cut chosen on patch (output. collar)
variable {C:Side}{D w:ℕ}{H:C.val=c.val*D}
section algebra
variable {K:Type*}
def marker (p:Site C→ Site c)(d:Site C→ℂ) (N:ℕ): Matrix (Modes C N) (Modes c N) ℂ:= Matrix.of fun i j=> if ((p i.1.1,i.1.2),i.2)=j then d i.1.1 else 0
noncomputable def streamL (p:Site C→ Site c)(d:Site C→ℂ) (N:ℕ): EvenA C N→L[ℝ] EvenA c N:= LinearMap.toContinuousLinearMap ((divert (marker p d N)).toLinearMap)
lemma marker_down (A:Window c C D)(d:Site C→ ℂ) (i:EvenA C N): axes A d N i=streamL A.cut d N i:=by
   change divert (choir N _) _= divert _ _; congr 2; ext ⟨⟨x,y⟩,z⟩ ⟨⟨a,b⟩,t⟩; by_cases he:z=t; all_goals simp [choir,Matrix.blockDiagonal_apply,marker,Quarry.stream,he]
lemma offer_boom (p: Site C→ Site c)(d:Site C→ℂ)(A:EvenA C N)(ht:∀ i,‖d i‖=1)(r:ℝ)(h:0<r): ‖token c N r (streamL p d N A)‖ ≤ ‖token C N r A‖:=by
   let K:= marker p d N; change load (fun _=>r) (adapter K Kᴴᵀ A.val) ≤ load (fun _=>r) A.val; apply ferry _ _ _ _ (boarded A.val)
   exact fun i=>h
   rintro (i|i) hi -- progress
   · rw [adapt_psi]; simp only [K,marker,Matrix.of_apply,ite_smul,zero_smul,Fintype.sum_ite_eq]; rw [load_scale,load_atom _ (fun _=>h),ht,one_mul] -- psi
   rw [adapt_bar]; simp only [Matrix.transpose_apply,Matrix.conjTranspose_apply,K,marker,Matrix.of_apply,apply_ite,star_zero,ite_smul,zero_smul,Fintype.sum_ite_eq]; rw [load_scale,norm_star, ht,one_mul]; exact (load_atom _ (fun _=>h) _).le
variable (A:Window c C D)(d:Site C→ℂ)(p:Site C)(g: Site c→ Site C)(Z: Support C)
variable (hp:Set.InjOn A.cut Z)(he:∀ i∈Z,g (A.cut i)=i)(hx:Quaint A d)
-- patch inverse
include he hx
lemma quayK (X:EvenA C N)(hX:Gated Z X) : streamL g (star ∘ d ∘ g) N (axes A d N X)=X:=by
    rw [marker_down]; apply Subtype.ext
    let P:=marker A.cut d N; let V:=marker g (star ∘ d ∘ g) N; let M:= (adapter V Vᴴᵀ).comp (adapter P Pᴴᵀ); change M X.val= X.val
    have ht (i: Modes C N)(h:i.1.1∈ Z): M (psi i)=psi i∧ M (bar i)=bar i:=by
        have hk:=he i.1.1 h; cases hv: i with| mk a b=>cases hz:a with|mk x k=>
         subst a i; constructor
         · simp only [M,P,V,AlgHom.comp_apply,adapt_psi,marker,Matrix.of_apply,ite_smul,zero_smul,Fintype.sum_ite_eq,map_smul]; simp only [Function.comp_apply,hk]; rw [smul_smul]; rcases hx.sign x with h|h <;> rw [h]<;>simp
         simp only [M,P,V,AlgHom.comp_apply,adapt_bar,marker,Matrix.of_apply,Matrix.transpose_apply, Matrix.conjTranspose_apply,apply_ite,star_zero,ite_smul,zero_smul,Fintype.sum_ite_eq,map_smul]; simp only [Function.comp_apply,hk]; rw [smul_smul]; rcases hx.sign x with h|h <;> rw [h]<;>simp
    have hh i (h:i⊆limits Z): M (mono i)=mono i:=by
       obtain ⟨w,hp,hb,H⟩:=Grass.expression i; rw [H]; rw [map_list_prod]; congr 1; rw [List.map_ofFn]; congr 1; funext i; let g:= w i; have hx:g∈limits Z:= h ((hb g).2 ⟨i,rfl⟩); change M (atom g)= _; change M (atom g)=atom g; rcases g with g|g; exact (ht g (mem_filter.mp hx).2).1; exact (ht g (mem_filter.mp hx).2).2 -- rewrite let dependent issue
    rw [← write X.val, map_sum]; -- nested rewrite!
    -- edit
    refine sum_congr rfl fun i _=>?_ ; by_cases he:i⊆ limits Z; · rw [map_smul,hh i he]
    rw [ember X.val hX i he,zero_smul,map_zero]
end algebra
end YM.QCD.Grove
