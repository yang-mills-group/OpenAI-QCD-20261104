import YM.Kwick.Grist
/-! phase grade exact. weighted standard forgetting. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.Perla Tawny.Cast.TableT Tawny.Cast.Zinc
open Oriole
local notation "D"=>10
local notation "T"=>Grade
local notation "L"=> (0:Multi 10)
local notation "Z"=> RawVec 10
variable (x:Grade)
local notation "P"=> kind 10 x
local notation "sK" k:arg=> if k=x then (1:ℂ) else 0
noncomputable def slots7 (a: Flavor 6) : Fin 7→ Z := ![bee a,beeA a,lup a,lapL a,slashS a,slashT a,starV a]
def τ7 : Fin 7→ Fin 4:=![0,0,1,1,1,1,2]
noncomputable def harps : Fin 3→ Z:=![Perla.leapV,Perla.lunar,Perla.eulerV]
open LinearMap
set_option maxHeartbeats 900000 in
lemma blastT(a:Flavor 6)(p:Fin 7)(i:Axis) : gradeCut 10 x ((slots7 a p).val i)=(sK (tierQ (τ7 p))) • (slots7 a p).val i:=by
     apply Subtype.ext; fin_cases p
     · change P ((bee a).val i).val= (sK (tierQ 0)) • ((bee a).val i).val; rw [bee_val,beta_up]; simp only [_root_.map_add,form_height,cost_root,gradeL]; rw [smul_add]; rfl
     · change P ((beeA a).val i).val=(sK (tierQ 0)) • ((beeA a).val i).val; rw [sea_val,AddSubmonoidClass.coe_finsetSum]; simp_rw [_root_.map_sum,sea_up,_root_.map_add,form_height,cost_root,gradeL,smul_sum]; apply sum_congr rfl; intro i _; rw [smul_add]; rfl
     · change P ((lup a).val i).val=(sK (tierQ 1)) • ((lup a).val i).val; rw [lup_val,shell0,basil_pond]; rw [_root_.map_sub,form_height,form_height,cost_root,gradeH,smul_sub]; rfl
     · change P ((lapL a).val i).val=(sK (tierQ 1)) • ((lapL a).val i).val; rw [lap_val,AddSubmonoidClass.coe_finsetSum]; simp_rw [_root_.map_sum,shell0,basil_pond,_root_.map_sub,form_height,cost_root,gradeH,smul_sum]; apply sum_congr rfl; intro i _; rw [smul_sub]; rfl
     · change P ((slashS a).val i).val=(sK (tierQ 1)) • ((slashS a).val i).val; rw[s_val,AddSubmonoidClass.coe_finsetSum]; simp_rw [_root_.map_sum,shell1,basil_pond,_root_.map_sub,form_height,cost_root,gradeH,smul_sum]; apply sum_congr rfl; intro i _; rw [smul_sub]; rfl
     · change P ((slashT a).val i).val=(sK (tierQ 1)) • ((slashT a).val i).val; rw[t_val,AddSubmonoidClass.coe_finsetSum]; simp_rw [_root_.map_sum,shell2,basil_pond,_root_.map_sub,form_height,gradeL,smul_sum]; apply sum_congr rfl; intro i _; rw[smul_sub]; rfl
     change P ((starV a).val i).val=(sK (tierQ 2)) • ((starV a).val i).val; rw[star_val,AddSubmonoidClass.coe_finsetSum]; simp only [_root_.map_sum,smul_sum]; exact sum_congr rfl fun j _=>chillS ..
set_option maxHeartbeats 650000 in
lemma craftT (p:Fin 3)(i:Axis): gradeCut 10 x ((harps p).val i)=(sK (tierQ 3)) • (harps p).val i:=by
     have hp(i j k l m): gradeCut 10 x (GE i j k l m)= (sK (tierQ 3)) • GE i j k l m:=Subtype.ext (phosphor x i j k l m)
     have hK(u: Axis→Label 10)(h:∀ i,gradeCut 10 x (u i)=(sK (tierQ 3)) • u i): gradeCut 10 x (∑ i,u i)=(sK (tierQ 3)) • ∑ i,u i:=by rw [_root_.map_sum,Finset.smul_sum]; exact sum_congr rfl fun i _=>h i
     have h1:harps 0=Perla.leapV:=rfl; have h2:harps 1=Perla.lunar:=rfl; have h3:harps 2=Perla.eulerV:=rfl; have hh: p=0 ∨ p=1∨p=2:=by omega
     rcases hh with h|h|h; rw[h,h1,oleap]; exact hK _ fun i=> hp ..; rw[h,h2,olun]; exact hK _ fun i=> hK _ (fun j=> hp ..); rw[h,h3,oeul]; exact hK _ fun i=> hK _ (fun j=> hp ..)
variable (h:Values 7)(v:Fin 3→ℂ)
private lemma tableEq (a:Flavor 6) (v:Fin 7→Z): (∑ i:Fin 7,v i)= v 0+v 1+v 2+v 3+v 4+v 5+v 6:=by simp [Fin.sum_univ_succ]; abel
lemma tabsT : plaza (h,v)= (∑ i:Flavor 6,∑ j:Fin 7,h i j • slots7 i j)+ ∑ j:Fin 3,v j • harps j:=by unfold plaza; simp_rw[tableEq 0,Fin.sum_univ_three]; rfl
-- Kind on Z
set_option maxHeartbeats 600000 in
lemma species (i:Axis) : gradeCut 10 x ((plaza (h,v)).val i)= (plaza ((fun a j=> (sK (tierQ (τ7 j))) * h a j),(sK (tierQ 3)) • v)).val i:=by
     rw [tabsT,tabsT]; simp only [Submodule.coe_add,Pi.add_apply,AddSubmonoidClass.coe_finsetSum,Finset.sum_apply,Submodule.coe_smul, Pi.smul_apply,_root_.map_add,_root_.map_sum,_root_.map_smul,blastT, craftT,smul_smul,smul_eq_mul]; exact congr_arg₂ HAdd.hAdd (sum_congr rfl fun i _=>sum_congr rfl fun j _=>by rw[mul_comm]) (sum_congr rfl fun i _=>by rw[mul_comm])
noncomputable def vaultP : Z→ₗ[ℂ] Z:= LinearMap.codRestrict (RawVec 10) (show _ from ((LinearMap.pi fun i:Axis=> (gradeCut 10 x) ∘ₗ LinearMap.proj i) ∘ₗ (RawVec 10).subtype)) (fun y=> by
     obtain ⟨⟨h,v⟩,rfl⟩:=certified.2 y; change (fun i:Axis=>gradeCut 10 x ((plaza (h,v)).val i)) ∈ _; simp_rw [species]; exact Submodule.coe_mem _)
noncomputable def bet (p:Fin 4): Z→ₗ[ℂ] Z:= vaultP (tierQ p)
lemma spec0(q:Z)(p:Grade)(h:∀ i, p≠ tierQ i) : vaultP p q=0:=by
     obtain ⟨⟨b,v⟩,rfl⟩:=certified.2 q; apply Subtype.ext; ext1 i; change gradeCut 10 p ((plaza (b,v)).val i) = 0; rw [species]; simp_rw[show ∀ i, (if tierQ i=p then (1:ℂ) else 0)=0 from fun i=> if_neg (Ne.symm (h i)),zero_mul,zero_smul]; rw[show ((fun a:Flavor 6=>fun j:Fin 7=>(0:ℂ)),(0:Fin 3→ℂ))=0 from rfl,_root_.map_zero]; rfl
lemma vaultE : vaultP x (plaza (h,v))= plaza ((fun a j=> (sK (tierQ (τ7 j)))*h a j),(sK (tierQ 3)) • v):=Subtype.ext (funext fun i=> species x h v i)
lemma bill_zero (q:Z): q=∑ i:Fin 4,bet i q:=by
     obtain ⟨⟨b,v⟩,rfl⟩:=certified.2 q; simp_rw[bet,vaultE,← _root_.map_sum]; congr 1; rw [Fin.sum_univ_four]; apply Prod.ext
     · ext1 i; ext j; have hh(k l:Fin 4):tierQ k=tierQ l ↔ k=l:=by decide +revert
       simp only[Prod.fst_add, Pi.add_apply, hh]; fin_cases j <;> norm_num [τ7,Fin.ext_iff] -- simp
     have h(k l: Fin 4): tierQ k=tierQ l ↔ k=l:=by decide +revert
     simp [h]
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.vaultE
