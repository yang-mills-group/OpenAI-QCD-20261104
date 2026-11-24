import YM.QCD.Tide.Chord
import YM.QCD.Revolve.Roots
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C] {n c f : Side} {F : ℕ} {β:ℝ} (R:Cells.Cut c) (r:Ratio c f)
-- scalar slice ratio
lemma coords0 (t:Site c)(v:Axis): r.embed t v = (((t v).val*r.count.val:ℕ):Per f):=by
    let y:Cover:=fun i=>(t i).val; have he: wrap c y=t:=funext fun i=>Int.cast_natCast ..|>.trans (ZMod.natCast_zmod_val _)
    calc _ = r.embed (wrap c y) v:= by rw [he]
         _ = _:=by rw [r.embed_wrap]; change (((r.count.val • y) v:ℤ):Per f)=_; push_cast; simp [y,nsmul_eq_mul,mul_comm] -- align calc
noncomputable def perM (v:Axis) : Per c →+ Per f where
    toFun i:=r.embed (i • step v) v
    map_zero' :=by change r.root _ v=0; rw [zero_smul,map_zero]; rfl
    map_add' x y:=by change r.root _ v=_; rw [add_smul,map_add]; rfl
lemma per_val (t:Per c)(v:Axis): perM r v t= (((t.val*r.count.val):ℕ):Per f):=by unfold perM; dsimp only [AddMonoidHom.coe_mk,ZeroHom.coe_mk]; rw [coords0]; simp
lemma per_root (t:Site c)(v:Axis): perM r v (t v)=r.embed t v:=by rw [per_val,coords0]
lemma per_one (v:Axis): perM r v 1=(r.count.val:Per f):=by
    change r.embed _ _=_; rw [one_smul]; rw [← wrap_step c v,r.embed_wrap,map_nsmul,wrap_step,Pi.smul_apply,nsmul_eq_mul,step_apply]; simp
lemma per_nat (x:ℕ)(v:Axis): perM r v (x:Per c)= (↑(x*r.count.val):Per f):=by rw [← nsmul_one,map_nsmul,per_one]; simp [nsmul_eq_mul]
noncomputable def gateH : Cells.Cut f:=⟨R.half*r.count, by rw [r.exact_size,R.even,PNat.mul_coe,mul_assoc],.link, R.pos,perM r R.pos R.baseLine-(r.count.val/2:ℕ)⟩
local notation "v"=> R.pos
local notation "L"=> r.count.val
local notation "d"=> L/2
local notation "T"=> gateH R r
lemma hat (ho:Odd L):2*(d:ℕ)+1=L:=by obtain ⟨p,hp⟩:=ho; omega
lemma slippery (h:R.kind=.link)(ho:Odd L): r.embed R.slide=(gateH R r).slide:=by
    unfold Cells.Cut.slide; funext i; rw [← per_root,Pi.smul_apply]; by_cases hi: i=v
    · subst i; change perM _ _ ((2*_ - _) * _)=(2*_ - _) * _; simp only [step_apply, if_true,mul_one,h,Cells.Kind.shift,Nat.cast_one]; unfold gateH; dsimp only
      rw [map_sub, show ∀ (A:Per c),perM r v (2*A)= 2*perM r v A from fun A=>by rw [two_mul,two_mul,map_add],per_one]; have ht:=hat r ho
      have hm:(L:Per f)=2*(↑(d):Per f)+1:=by nth_rw 1 [← ht]; push_cast; rfl
      rw [hm]; simp only [ ↓reduceIte,mul_one]; ring -- rewrites also nested d? since hm matches cast syntactic L.
    have ht: i≠(gateH R r).pos:=hi
    rw [Pi.smul_apply]; simp only [step_apply,if_neg hi, if_neg ht,smul_eq_mul,mul_zero,map_zero]
lemma switchy (h:R.kind=.link)(ho:Odd L)(x:Site c): r.embed (R.reflect x)=(gateH R r).reflect (r.embed x):=by
    change r.root (R.flip.act _+_)=_; rw [map_add,Ratio.root_embed, Ratio.root_embed, slippery R r h ho, r.signed]; rfl -- second arg root_embed? check
lemma stopH: Slice.Link.top T+1 = perM r v (Slice.Link.top R+1)-(↑(d):Per f):=by
    simp only [Slice.Link.top,sub_add_cancel]; unfold gateH; simp only [PNat.mul_coe,map_add, per_nat]; rw [sub_add_eq_add_sub]
end YM.QCD.Tide
