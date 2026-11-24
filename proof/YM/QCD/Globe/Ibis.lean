import YM.QCD.Kites.Returns
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
section
variable {A B: Type*} [Fintype A] [DecidableEq A] [Fintype B][DecidableEq B]
-- unipotent log.Mod
lemma lists_m (i:A)(x:Alg A)(h:vary i x=0)(s:Finset A)(hk:i∈s): coef s x=0:=by
    have he(t:Finset A): atom i*vary i (mono t) = if i∈t then mono t else 0 :=by
        by_cases hi : i∈t
        · rw [if_pos hi,(show atom i*vary i (mono t)=mono t - vary i (atom i*mono t) from ?_),show atom i *mono t=0 from ?_,map_zero,sub_zero]
          · rw [← mono_single]; apply mono_mul_zero; simp [hi]
          rw [vary_head]; simp [Grass.probe]
        rw [if_neg hi, show vary i (mono t)=0 from ?_, mul_zero]
        obtain ⟨w,-,hp,H⟩:=expression t
        have ht (z : List A) (h:i∉ z): vary i (z.map atom).prod=0:=by
          induction z with
          | nil=> simp [vary_one]
          | cons k L ih=> simp only [List.mem_cons,not_or] at h; simp only [List.map_cons,List.prod_cons,vary_mul, vary_off _ _ h.1, ih h.2,mul_zero,zero_mul,add_zero]
        rw [H]; have hz : i∉List.ofFn w:=by simpa [(hp i)] using hi
        simpa only [List.map_ofFn] using ht (List.ofFn w) hz
    have hv : atom i*vary i x=0:=by rw [h,mul_zero]
    have hm:= congr_arg (coef s) hv
    conv_lhs at hm=>rw [← write x,map_sum, mul_sum,map_sum]
    simp only [map_zero,map_smul,mul_smul_comm, he] at hm
    rw [sum_eq_single s] at hm
    · simpa only [map_smul, if_pos hk,Grass.read,smul_eq_mul,mul_one] using hm
    · intro j _ hj; split <;> simp [read_other, Ne.symm hj]
    simp
lemma submerged (x y:Alg A)(z:ℂ)(hp:Plus x)(he:Plus y)(h: exp x=z • exp y)(ht:coef ∅ x=coef ∅ y): x=y:=by
    have hh (i:A) : vary i (x-y)=0:=by
        have hv:= congr_arg (vary i) h; rw [map_smul,varies_exp i x hp,varies_exp i y he,← smul_mul_assoc,← h] at hv
        have hx :exp (-x)*exp x=1:=by rw [← algebra_exp_add (hp.central _),neg_add_cancel,exp_zero]
        have ht':=congr_arg (exp (-x)*·) hv; simp only [← mul_assoc,hx,one_mul] at ht'; rw [map_sub,ht',sub_self]
    apply sub_eq_zero.mp; rw [← write (x-y)]; apply sum_eq_zero; intro i _ ; by_cases hx:i.Nonempty
    · obtain ⟨j,hj⟩:=hx; rw [lists_m j _ (hh j) _ hj,zero_smul]
    rw [Finset.not_nonempty_iff_eq_empty.mp hx,map_sub,ht,sub_self,zero_smul]
end
end YM.QCD.Globe
