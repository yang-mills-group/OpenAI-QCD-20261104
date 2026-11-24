import YM.DawnS.Pet
import YM.DawnS.Sea
import YM.Next.MAXWELL.Core

set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexOrder
variable {d:ℕ}(r:ℝ)(hr:0<r)
local notation "I₀"=> Vault d
local notation "wd"=>fun _ : Fin 2 =>d
local notation "Q"=> chime (fun _ : Fin 2=>d) (dotsG r)
local notation "QZ"=>unionB Q
variable (C:Matrix (Vault d) (Vault d) ℂ)(hc:IsUnit C)(he:Cᴴ*hank d r*C=1)
noncomputable def swell : Alg (Vault d)→ₐ[ℂ] SpinPol d:= ExteriorAlgebra.map (vaultT C)
local notation "H"=> swell C
noncomputable abbrev Wp(p:SpinPol d):= twig wd 0 (τSpin d p)
noncomputable abbrev Hp(p:SpinPol d):= twig wd 1 p
lemma puff(a b:List (Vault d)): Wp (H (a.map atom).prod) * Hp (H (b.map atom).prod)= pwn (a.reverse.map (leans C) ++ b.map (rightP C)) :=by
     have h(i:I₀): H (atom i)=line (jewel C i):= ExteriorAlgebra.map_apply_ι _ _
     have hx : Wp (H (a.map atom).prod)= pwn (a.reverse.map (leans C)):=by
          induction a using List.reverseRecOn with
          | nil=> simp only [List.map_nil,List.reverse_nil,List.prod_nil,Wp,map_one,τSpin_one,pwn]
          | append_singleton a t ih=>
             rw [List.map_append,List.prod_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,map_mul]; unfold Wp at *; rw [τSpin_mul,map_mul, show _ = _ from ih, List.reverse_append,h,legged]
             rw [twig, ExteriorAlgebra.map_apply_ι]; rfl -- order low path
     have hy:Hp (H (b.map atom).prod)=pwn (b.map (rightP C)):=by
          induction b with
          | nil=>simp [Hp,pwn]
          |cons i b ih=>
             simp only[List.map_cons,List.prod_cons]; unfold Hp at *; rw[map_mul,map_mul,h, show _=_ from ih]; rw[twig, ExteriorAlgebra.map_apply_ι];rfl
     rw[hx,hy]; unfold pwn; rw [List.map_append,List.prod_append] -- rw `pwn` picks first not last
lemma plume (t:Finset (Vault d)): mono t=((atomList t).map atom).prod:=by rw[atomList,List.map_ofFn]; exact (expression t).choose_spec.2.2
lemma scent (t:Finset (Vault d)): (atomList t).Nodup ∧ (atomList t).toFinset=t:=by
    refine ⟨List.nodup_ofFn.mpr (Grass.expression t).choose_spec.1,?_⟩; ext1 i; rw[List.mem_toFinset,atomList,List.mem_ofFn]; exact (Grass.expression t).choose_spec.2.1 i |>.symm
include he hr
lemma eclipse(V W:Finset (Vault d)): lease Q (Wp (H (mono V))*Hp (H (mono W)))=(if V=W then 1 else 0):=by
    rw [plume V,plume W,puff]; by_cases h:V=W
    · subst W; rw [if_pos rfl]; exact vernal r hr C he _ (scent V|>.1)
    rw [if_neg h]; refine wiseman r hr C he _ _ (scent _|>.1) (scent _|>.1) (fun hv=>h ((scent V).2.symm.trans (hv.trans (scent W).2)))
end YM.DawnS
