import YM.DawnS.Flea

set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Pointwise
open Arise.Pair Arise.Count
variable {d n m k :ℕ}{u:Fin n→ℕ}
variable (x:Points n)(hx:x∈conf n)(A:Occ u)
local notation "QZ"=>chime u x
local notation "G"=> unionB (chime u x)
variable (i:Fin n)
local notation "Z"=> slashEq (u i)
include hx
lemma asleep : Z ≤ LinearMap.ker ((G).comp (rifle u i)):=by
   apply Submodule.span_le.mpr; rintro a (⟨b,rfl⟩|⟨b,rfl⟩) <;> apply LinearMap.mem_ker.mpr <;> apply (thetaBasis (Occ u)).ext <;> intro k
   exact col_gone _ hx i b k; exact bar_gone _ hx i b k
lemma lease_quiet {z:beam (u i)}(he:z∈slashEq (u i))(b c:Alg (Occ u)):lease QZ (b * line (rifle u i z) * c)=0:=by
    rw [← grade_twice b] -- find
    rw [← line_across, mul_assoc]; suffices h:∀ x:Alg _,lease QZ (line (rifle u i z)*x)=0 from h _
    intro y; rw [← write y, Finset.mul_sum,map_sum]; refine Finset.sum_eq_zero fun j _=>?_
    let f:Fin j.card→ Occ u:=(Grass.expression j).choose; let q:=List.ofFn fun k:Fin j.card=>thetaBasis _ (f k)
    rw [mul_smul_comm,map_smul,show Grass.mono j=pwn q from ?h]; swap; · unfold pwn q; rw[List.map_ofFn]; exact (Grass.expression j).choose_spec.2.2
    rw[veil]; simp only [show G (rifle u i z)=0 from asleep _ hx _ he,LinearMap.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero,smul_zero]
local notation "Rι"=> u i
noncomputable abbrev scarG (d:ℕ):= Grass.Seed (letters d) ⧸ slashEq d
noncomputable abbrev wedgeR (d:ℕ):= ExteriorAlgebra ℂ (scarG d)
noncomputable abbrev bareT (d:ℕ): SpinPol d→ₐ[ℂ]wedgeR d:= ExteriorAlgebra.map (slashEq d).mkQ
lemma waist (ξ:scarG (u i)→ₗ[ℂ]beam (u i))(hξ: (slashEq (u i)).mkQ.comp ξ=LinearMap.id) (p:SpinPol (u i)):∀ b c:Alg (Occ u), lease QZ (b* twig u i p*c)=lease QZ (b* twig u i (ExteriorAlgebra.map ξ (bareT (u i) p))*c):=by
     let W:=twig u i; let F:=(ExteriorAlgebra.map ξ).comp (bareT (u i))
     have ht (l:List (letters Rι)) (b c:Alg (Occ u)): let z: SpinPol _:= (l.map Grass.atom).prod; lease QZ (b*W z*c)=lease QZ (b*W (F z)*c):=by
          induction l generalizing b with
          | nil=> intro z; simp only[z,List.map_nil,List.prod_nil,map_one]
          | cons j l ih=>
             intro z; let v:= thetaBasis _ j; let t:= atom j; let p:= (l.map Grass.atom).prod; have he:z=t*p:=rfl
             rw[he,map_mul W,map_mul F,map_mul W,← mul_assoc,← mul_assoc b]
             rw [show lease (chime u x) (b*W t* W p*c)= _ from ih (b*W t)] -- introduces c? depends fixed
             apply sub_eq_zero.mp
             rw [← map_sub, ← sub_mul, ← sub_mul,← mul_sub b,←map_sub W]
             have hp : t - F t=line (v-ξ ((slashEq (u i)).mkQ v)):=by unfold t atom F bareT; rw [AlgHom.comp_apply, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι, map_sub]
             let vq:= v-ξ ((Z).mkQ v); have hT:vq∈slashEq (u i):=(Submodule.Quotient.mk_eq_zero _).mp (show (Z).mkQ vq=0 from (by unfold vq; rw [map_sub, show (slashEq (u i)).mkQ (ξ ((slashEq (u i)).mkQ v))=(Z).mkQ v from LinearMap.congr_fun hξ _,sub_self]))
             rw[hp,show W (Grass.line vq)=_ from ExteriorAlgebra.map_apply_ι (rifle u i) vq,mul_assoc (b*_)]
             exact lease_quiet x hx i hT b _
     intro a b; let Zm:= lease QZ; change Zm (a*W p*b) = Zm (a*W (F p)*b); rw[← Grass.write p]; simp only [Finset.mul_sum,sum_mul,map_sum,map_smul,mul_smul_comm, _root_.smul_mul_assoc]; refine Finset.sum_congr rfl fun i _=>?_ ; obtain ⟨f,hf⟩:= expression i; rw[hf.2.2,← List.map_ofFn]; exact congr_arg _ (ht (List.ofFn f) a b)
end YM.DawnS
