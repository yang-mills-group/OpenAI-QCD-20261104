import YM.Elms.Bough
import YM.QCD.RP.Floor
import YM.QCD.RP.Hop
import YM.Poised.Canoe
/-! # Counting at the actual placement with flavor wind and AP cocycle.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open LinearMap
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
variable (n:Side) (o: Cover)(w:Walk)
-- metadata
local notation "O" => wrap n o
def capEdge (o:Cover)(w:Walk):Cover:= stop 0 w + o
abbrev landsE (n:Side)(o:Cover)(w:Walk) :Site n:= wrap n (capEdge o w)
local notation "T"=> landsE n o w
abbrev Dike := Wind 6
abbrev ΔM := Short 6
abbrev blux(M: Mat):ΔM:= copies 6 (touch M)
abbrev clutch (u:su.El):ΔM:= blux (colour u)
lemma blux_mu (A B:Mat): blux (A*B)=blux A*blux B:=by rw [blux,← touch_mul,copies_mul] -- touch_mul direction.
lemma blux_s (A:Mat)(u:ℂ): blux (u • A)=u • blux A:=by
    unfold blux; rw [show touch (u • A)=u • touch A from ?_,copies_smul]
    ext i j; unfold touch; simp; ring -- touch doesn't commute? need
lemma blux_star (A:Mat): blux (star A)= star (blux A):=by unfold blux; rw [← touch_star,copies_star] -- maybe directions
lemma clutch_add (u v:su.El): clutch (u*v)= clutch u*clutch v:=by unfold clutch; rw [Lat.colour_mul,blux_mu]
lemma clutch_inv (u:su.El): clutch u⁻¹= star (clutch u):=by unfold clutch; rw [colour_inv,blux_star]
lemma clutch_u (u:su.El):clutch u∈unitary _:= copies_unitary 6 _ (touch_u ⟨su.mat_star_mul _,su.mat_mul_star _⟩)
lemma clutch_one : clutch 1=1:=by rw [clutch, show colour 1= (1:Mat) from su.mat_one,blux,touch_one, copies_one]
def haloW (n:Side)(o:Cover)(w:Walk)(U:Grid n):su.El:=Lattice.travel (expandAt (wrap n o) U) 0 w
local notation "Tr" => haloW n o w
def stripe (o:Cover)(w:Walk)(U:Grid n):ΔM:= Cylinder.ap n (capEdge o w) • clutch (haloW n o w U)
local notation "Ψ" U:arg=> stripe n o w U
open Lining
variable (U:Grid n)
lemma stripe_star (u:Cover) : star (Cylinder.ap n u)= Cylinder.ap n u:=Ferry.ap_star n u
lemma stripe_u : Ψ U∈unitary _:=by
    constructor <;> simp only [stripe,star_smul,stripe_star,Matrix.mul_smul,Matrix.smul_mul,smul_smul,Pipes.ap_sq,one_smul]; exact (clutch_u _).1; exact (clutch_u _).2 -- inside unitary no
lemma cap_head(a:Axis): capEdge o (w++[posDir a])=capEdge o w+ step a:=by simp [capEdge,stop_append, stop]; abel
lemma cap_tail(a:Axis):capEdge o (w++[negDir a])=capEdge o w-step a:=by simp [capEdge,stop_append,stop]; abel
lemma land_head(a:Axis): landsE n o (w++[posDir a])=T+step a:=by simp [landsE,cap_head]
lemma land_tail(a:Axis): landsE n o (w++[negDir a])=T-step a:=by simp [landsE,cap_tail]
lemma Tr_head(a:Axis): haloW n o (w ++ [posDir a]) U= Tr U * U (T,a):=by simp only [haloW,Lattice.travel_append,Lattice.travel,mul_one,Step.pos_read,expandAt]; simp [landsE,capEdge]
lemma Tr_tail(a:Axis):haloW n o (w++[negDir a]) U= Tr U*(U (T-step a,a))⁻¹:=by
   simp only [haloW,Lattice.travel_append,Lattice.travel,mul_one,Step.neg_read,expandAt]; have ht:= land_tail n o w a; have hx: wrap n (stop 0 w-step a)+wrap n o=T-step a:=by simp [landsE,capEdge]; abel
   rw [hx]
lemma stripe_head(a:Axis): stripe n o (w++[posDir a]) U= stripe n o w U* blux (thread 0 U a T):=by
    rw [stripe,cap_head,Tr_head,Poised.Pipes.seam_tick,clutch_add]; unfold thread; rw [stripe,Matrix.smul_mul,blux_s,Matrix.mul_smul,mul_smul]
lemma stripe_tail(a:Axis): stripe n o (w++[negDir a]) U= Ψ U * star (blux (thread 0 U a (T-step a))):=by
    unfold thread; rw [stripe,cap_tail,Tr_tail,clutch_add,clutch_inv,stripe,blux_s,star_smul,seam_real,Matrix.smul_mul,Matrix.mul_smul,smul_smul]; let v:=capEdge o w-step a; rw [show Cylinder.ap n (capEdge o w)=Cylinder.ap n v*seam 0 (T-step a) a from ?_, mul_assoc,seam_sq,mul_one]
    rw [show T-step a=wrap n v from (by unfold v; rw [map_sub,wrap_step])]; exact Eq.trans (congr_arg _ (sub_add_cancel _ _).symm) (Pipes.seam_tick v a)
lemma halo_change (g:Frame n): haloW n o w (Lattice.gauge g U)= (g O)*Tr U*(g T)⁻¹:=by rw [haloW,expandAt_gauge,travel_gauge]; simp only [map_zero, zero_add,landsE,capEdge,map_add]; rfl
lemma stripe_change (g:Frame n): stripe n o w (Lattice.gauge g U)= clutch (g O)*Ψ U*star (clutch (g T)):=by rw [stripe,stripe,halo_change,clutch_add,clutch_add,clutch_inv]; simp
@[fun_prop] lemma halo_cont : Continuous (Tr):=Push.Mark.onStencil _ (continuous_travel w _)
@[fun_prop] lemma stripes_c : Continuous (stripe n o w):=by unfold stripe clutch blux; fun_prop
variable {n}
noncomputable abbrev peggle (q:Bool)(A:ΔM):ΔM:=if q then (star A).transpose else A
lemma peglow (q:Bool)(A B:ΔM): peggle q (A*B)=peggle q A*peggle q B:=by cases q; rfl; simp [peggle]; -- order
-- matrix-driven bean.Res Use coors.at E.Sc.
noncomputable def beams (q:Bool)(n:Side)(o:Cover)(w:Walk)(U:Grid n)(a:Dike):Lat.Fields n 6:=∑ j:Dike, (peggle q (stripe n o w U) a j) • lineT q (RP.place (landsE n o w) j)
noncomputable def cane (n:Side)(q:Bool)(o:Cover)(w:Walk)(a:Dike):Insertion n 6:=⟨fun U=>beams q n o w U a,by cases q <;> unfold beams <;> simp only [peggle,Bool.false_eq_true,if_false, if_true] <;> fun_prop⟩
variable (q:Bool)(a:Dike)
lemma tops(g:Frame n)(x:Site n): slots 6 g (lineT q (place x a))=∑ j: Dike, (peggle q (clutch (g x)) a j) • lineT q (place x j):=by
    unfold slots; cases q with
    | false=>rw [lineT,if_neg (by simp),Grass.adapt_psi,Lat.rotates,siteRot,placed_sum,sum_eq_single x]; · simp_rw [placed,Equiv.refl_apply,if_true]; rfl
             · intro y _ he; simp [placed, Ne.symm he]
             simp
    | true=> rw [lineT,if_pos rfl,Grass.adapt_bar]; unfold Lat.rotates siteRot; simp only [Matrix.transpose_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]; rw [placed_sum,sum_eq_single x]
             · simp_rw [placed,Equiv.refl_apply,if_true]; rfl
             · intro y _ he; simp [placed,Ne.symm he]
             simp
lemma flowAct(g:Frame n): slots 6 g (beams q n o w (Lattice.gauge g U) a)=∑ b:Dike,(peggle q (clutch (g (wrap n o))) a b) • beams q n o w U b:=by
   let Z:=stripe n o w (Lattice.gauge g U); let g1:=g T; let g0:=g O; have hz : peggle q Z *peggle q (clutch g1)= peggle q (clutch g0)*peggle q (Ψ U):=by rw [← peglow,←peglow]; apply congr_arg; unfold Z; rw [stripe_change]; change _*star (clutch g1)*clutch g1=_; rw [Matrix.mul_assoc,(clutch_u g1).1, mul_one] -- fail assoc
   simp only [beams,map_sum,map_smul,tops]; simp_rw [smul_sum,smul_smul]; rw [sum_comm]; conv_rhs=> rw [sum_comm]
   apply Finset.sum_congr rfl; intro i _; rw [←sum_smul,← sum_smul]; exact congr_arg (fun z:ℂ=> z • lineT q (place T i)) (congr_fun (congr_fun hz a) i)
end Arbor
end SparK
end YM.Massive.Elm
